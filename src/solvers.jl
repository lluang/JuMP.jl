#  Copyright 2015, Iain Dunning, Joey Huchette, Miles Lubin, and contributors
#  This Source Code Form is subject to the terms of the Mozilla Public
#  License, v. 2.0. If a copy of the MPL was not distributed with this
#  file, You can obtain one at http://mozilla.org/MPL/2.0/.

function solve(m::Model; suppress_warnings=false, ignore_solve_hook=(m.solvehook==nothing), kwargs...)

    ignore_solve_hook || return m.solvehook(m; suppress_warnings=suppress_warnings, kwargs...)

    # Analyze model to see if any integers
    anyInts = (length(m.sosconstr) > 0) ||
        any(c-> !(c == :Cont || c == :Fixed), m.colCat)

    if length(m.sdpconstr) > 0
        @assert m.nlpdata == nothing
        @assert !anyInts
        if isa(m.solver,UnsetSolver)
            m.solver = MathProgBase.defaultSDPsolver
        end
        return solveSDP(m, suppress_warnings=suppress_warnings)
    end

    if m.nlpdata != nothing
        if isa(m.solver,UnsetSolver)
            m.solver = MathProgBase.defaultNLPsolver
        end
        return solvenlp(m, suppress_warnings=suppress_warnings)
    end

    if isa(m.solver,UnsetSolver) &&
      (length(m.obj.qvars1) > 0 || length(m.quadconstr) > 0)
        m.solver = MathProgBase.defaultQPsolver
    end
    if anyInts
        if isa(m.solver,UnsetSolver)
            m.solver = MathProgBase.defaultMIPsolver
            s = solveMIP(m; suppress_warnings=suppress_warnings)
            # Clear solver in case we change problem types
            m.solver = UnsetSolver()
            m.internalModelLoaded = false
            return s
        else
            solveMIP(m; suppress_warnings=suppress_warnings)
        end
    else
        if isa(m.solver,UnsetSolver)
            m.solver = MathProgBase.defaultLPsolver
            s = solveLP(m, suppress_warnings=suppress_warnings)
            m.solver = UnsetSolver()
            return s
        else
            solveLP(m; suppress_warnings=suppress_warnings)
        end
    end
end

function addQuadratics(m::Model)

    if length(m.obj.qvars1) != 0
        assert_isfinite(m.obj)
        verify_ownership(m, m.obj.qvars1)
        verify_ownership(m, m.obj.qvars2)
        # Check for solver support for quadratic objectives happens in MPB
        MathProgBase.setquadobjterms!(m.internalModel, Cint[v.col for v in m.obj.qvars1], Cint[v.col for v in m.obj.qvars2], m.obj.qcoeffs)
    end

    # Add quadratic constraint to solver
    const sensemap = @compat Dict(:(<=) => '<', :(>=) => '>', :(==) => '=')
    for k in 1:length(m.quadconstr)
        qconstr = m.quadconstr[k]::QuadConstraint
        if !haskey(sensemap, qconstr.sense)
            error("Invalid sense for quadratic constraint")
        end
        s = sensemap[qconstr.sense]

        terms::QuadExpr = qconstr.terms
        assert_isfinite(terms)
        for ind in 1:length(terms.qvars1)
            if (terms.qvars1[ind].m != m) || (terms.qvars2[ind].m != m)
                error("Variable not owned by model present in constraints")
            end
        end
        affidx = Cint[v.col for v in qconstr.terms.aff.vars]
        var1idx = Cint[v.col for v in qconstr.terms.qvars1]
        var2idx = Cint[v.col for v in qconstr.terms.qvars2]
        if applicable(MathProgBase.addquadconstr!, m.internalModel, affidx, qconstr.terms.aff.coeffs, var1idx, var2idx, qconstr.terms.qcoeffs, s, -qconstr.terms.aff.constant)
            MathProgBase.addquadconstr!(m.internalModel, affidx, qconstr.terms.aff.coeffs, var1idx, var2idx, qconstr.terms.qcoeffs, s, -qconstr.terms.aff.constant)
        else
            error("Solver does not support quadratic constraints")
        end
    end
end

function addSOS(m::Model)
    for i in 1:length(m.sosconstr)
        sos = m.sosconstr[i]
        indices = Int[v.col for v in sos.terms]
        if sos.sostype == :SOS1
            if applicable(MathProgBase.addsos1!, m.internalModel, indices, sos.weights)
                MathProgBase.addsos1!(m.internalModel, indices, sos.weights)
            else
                error("Solver does not support SOS constraints")
            end
        elseif sos.sostype == :SOS2
            if applicable(MathProgBase.addsos2!, m.internalModel, indices, sos.weights)
                MathProgBase.addsos2!(m.internalModel, indices, sos.weights)
            else
                error("Solver does not support SOS constraints")
            end
        end
    end
end

# prepare objective, constraint matrix, and row bounds
function prepProblemBounds(m::Model)

    objaff::AffExpr = m.obj.aff
    assert_isfinite(objaff)
    verify_ownership(m, objaff.vars)

    # We already have dense column lower and upper bounds

    # Create dense objective vector
    f = zeros(m.numCols)
    for ind in 1:length(objaff.vars)
        f[objaff.vars[ind].col] += objaff.coeffs[ind]
    end

    # Create row bounds
    linconstr = m.linconstr::Vector{LinearConstraint}
    numRows = length(linconstr)
    rowlb = fill(-Inf, numRows)
    rowub = fill(+Inf, numRows)
    for c in 1:numRows
        rowlb[c] = linconstr[c].lb
        rowub[c] = linconstr[c].ub
    end

    return f, rowlb, rowub
end

# prepare column-wise constraint matrix
function prepConstrMatrix(m::Model)

    # Create sparse A matrix
    # First we build it row-wise, then use the efficient transpose
    # Theory is, this is faster than us trying to do it ourselves
    # Intialize storage
    linconstr = m.linconstr::Vector{LinearConstraint}
    numRows = length(linconstr)
    rowptr = Array(Int,numRows+1)
    nnz = 0
    for c in 1:numRows
        nnz += length(linconstr[c].terms.coeffs)
    end
    colval = Array(Int,nnz)
    rownzval = Array(Float64,nnz)

    # Fill it up
    nnz = 0
    tmprow = IndexedVector(Float64,m.numCols)
    tmpelts = tmprow.elts
    tmpnzidx = tmprow.nzidx
    for c in 1:numRows
        rowptr[c] = nnz + 1
        assert_isfinite(linconstr[c].terms)
        coeffs = linconstr[c].terms.coeffs
        vars = linconstr[c].terms.vars
        # collect duplicates
        for ind in 1:length(coeffs)
            if !is(vars[ind].m, m)
                error("Variable not owned by model present in constraints")
            end
            addelt!(tmprow,vars[ind].col,coeffs[ind])
        end
        for i in 1:tmprow.nnz
            nnz += 1
            idx = tmpnzidx[i]
            colval[nnz] = idx
            rownzval[nnz] = tmpelts[idx]
        end
        empty!(tmprow)
    end
    rowptr[numRows+1] = nnz + 1

    # Build the object
    rowmat = SparseMatrixCSC(m.numCols, numRows, rowptr, colval, rownzval)
    # Note that rowmat doesn't have sorted indices, so technically doesn't
    # follow SparseMatrixCSC format. But it's safe to take the transpose.
    A = rowmat'
end

function vartypes_without_fixed(m::Model)
    colCats = copy(m.colCat)
    for i in 1:length(colCats)
        if colCats[i] == :Fixed
            @assert m.colLower[i] == m.colUpper[i]
            colCats[i] = :Cont
        end
    end
    return colCats
end

function solveLP(m::Model; suppress_warnings=false)
    f, rowlb, rowub = prepProblemBounds(m)

    # Ready to solve
    noQuads = (length(m.quadconstr) == 0) && (length(m.obj.qvars1) == 0)
    if m.internalModelLoaded
        if applicable(MathProgBase.setvarLB!, m.internalModel, m.colLower) &&
           applicable(MathProgBase.setvarUB!, m.internalModel, m.colUpper) &&
           applicable(MathProgBase.setconstrLB!, m.internalModel, rowlb) &&
           applicable(MathProgBase.setconstrUB!, m.internalModel, rowub) &&
           applicable(MathProgBase.setobj!, m.internalModel, f) &&
           applicable(MathProgBase.setsense!, m.internalModel, m.objSense) &&
           applicable(MathProgBase.setvartype!, m.internalModel, [:Cont])
            MathProgBase.setvarLB!(m.internalModel, m.colLower)
            MathProgBase.setvarUB!(m.internalModel, m.colUpper)
            MathProgBase.setconstrLB!(m.internalModel, rowlb)
            MathProgBase.setconstrUB!(m.internalModel, rowub)
            MathProgBase.setobj!(m.internalModel, f)
            MathProgBase.setsense!(m.internalModel, m.objSense)
            MathProgBase.setvartype!(m.internalModel, fill(:Cont,m.numCols))
        else
            !suppress_warnings && Base.warn_once("Solver does not appear to support hot-starts. Problem will be solved from scratch.")
            m.internalModelLoaded = false
        end
    end
    if !m.internalModelLoaded
        A = prepConstrMatrix(m)
        m.internalModel = MathProgBase.model(m.solver)

        # Wrap conic solvers
        if applicable(MathProgBase.supportedcones, m.solver) &&
            !method_exists(MathProgBase.addquadconstr!, (typeof(m.internalModel), Vector{Int}, Vector{Float64}, Vector{Int}, Vector{Int}, Vector{Float64}, Char, Float64)) &&
            :SOC in MathProgBase.supportedcones(m.solver)

            m.internalModel = MathProgBase.model(MathProgBase.ConicSolverWrapper(m.solver))
        end

        MathProgBase.loadproblem!(m.internalModel, A, m.colLower, m.colUpper, f, rowlb, rowub, m.objSense)
        addQuadratics(m)
        m.internalModelLoaded = true
    end

    MathProgBase.optimize!(m.internalModel)
    stat = MathProgBase.status(m.internalModel)

    if stat != :Optimal
        !suppress_warnings && warn("Not solved to optimality, status: $stat")
        m.colVal = fill(NaN, m.numCols)
        m.objVal = NaN
        if stat == :Infeasible
            if noQuads && applicable(MathProgBase.getinfeasibilityray, m.internalModel)
                m.linconstrDuals = MathProgBase.getinfeasibilityray(m.internalModel)
            else
                noQuads && !suppress_warnings && warn("Infeasibility ray (Farkas proof) not available")
                m.linconstrDuals = fill(NaN, length(m.linconstr))
            end
        elseif stat == :Unbounded
            if noQuads && applicable(MathProgBase.getunboundedray, m.internalModel)
                m.colVal = MathProgBase.getunboundedray(m.internalModel)
            else
                noQuads && !suppress_warnings && warn("Unbounded ray not available")
            end
        else
            try # guess try/catch is necessary because we're not sure what return status we have
                m.colVal = MathProgBase.getsolution(m.internalModel)
            catch
                m.colVal = fill(NaN, m.numCols)
            end
            try
                # store solution values in model
                m.objVal = MathProgBase.getobjval(m.internalModel)
                m.objVal += m.obj.aff.constant
            catch
                m.objVal = NaN
            end
        end
    else
        # store solution values in model
        m.objVal = MathProgBase.getobjval(m.internalModel)
        m.objVal += m.obj.aff.constant
        m.colVal = MathProgBase.getsolution(m.internalModel)
        if applicable(MathProgBase.getreducedcosts, m.internalModel) &&
                      applicable(MathProgBase.getconstrduals,  m.internalModel)
            m.redCosts = MathProgBase.getreducedcosts(m.internalModel)
            m.linconstrDuals = MathProgBase.getconstrduals(m.internalModel)
        else
            !suppress_warnings && warn("Dual solutions not available")
            m.redCosts = fill(NaN, length(m.linconstr))
            m.linconstrDuals = fill(NaN, length(m.linconstr))
        end
    end

    return stat
end

function solveMIP(m::Model; suppress_warnings=false)
    f, rowlb, rowub = prepProblemBounds(m)
    A = prepConstrMatrix(m)

    # Ready to solve
    colCats = vartypes_without_fixed(m)

    if m.internalModelLoaded
        if applicable(MathProgBase.setvarLB!, m.internalModel, m.colLower) &&
           applicable(MathProgBase.setvarUB!, m.internalModel, m.colUpper) &&
           applicable(MathProgBase.setconstrLB!, m.internalModel, rowlb) &&
           applicable(MathProgBase.setconstrUB!, m.internalModel, rowub) &&
           applicable(MathProgBase.setobj!, m.internalModel, f) &&
           applicable(MathProgBase.setsense!, m.internalModel, m.objSense) &&
           applicable(MathProgBase.setvartype!, m.internalModel, colCats)
            MathProgBase.setvarLB!(m.internalModel, m.colLower)
            MathProgBase.setvarUB!(m.internalModel, m.colUpper)
            MathProgBase.setconstrLB!(m.internalModel, rowlb)
            MathProgBase.setconstrUB!(m.internalModel, rowub)
            MathProgBase.setobj!(m.internalModel, f)
            MathProgBase.setsense!(m.internalModel, m.objSense)
            MathProgBase.setvartype!(m.internalModel, colCats)
        else
            !suppress_warnings && Base.warn_once("Solver does not appear to support hot-starts. Problem will be solved from scratch.")
            m.internalModelLoaded = false
        end
    end
    if !m.internalModelLoaded
        m.internalModel = MathProgBase.model(m.solver)

        MathProgBase.loadproblem!(m.internalModel, A, m.colLower, m.colUpper, f, rowlb, rowub, m.objSense)
        if applicable(MathProgBase.setvartype!, m.internalModel, colCats)
            MathProgBase.setvartype!(m.internalModel, colCats)
        else
            error("Solver does not support discrete variables")
        end

        addSOS(m)

        addQuadratics(m)
        registercallbacks(m)

        m.internalModelLoaded = true
    end

    if !all(isnan,m.colVal)
        if applicable(MathProgBase.setwarmstart!, m.internalModel, m.colVal)
            MathProgBase.setwarmstart!(m.internalModel, m.colVal)
        else
            !suppress_warnings && Base.warn_once("Solver does not appear to support providing initial feasible solutions.")
        end
    end

    MathProgBase.optimize!(m.internalModel)
    stat = MathProgBase.status(m.internalModel)

    if stat != :Optimal
        !suppress_warnings && warn("Not solved to optimality, status: ", string(stat))
    end
    # It's possible that we have a feasible solution if we're not optimal
    # TODO: Test this behavior on various solvers
    try
        # store solution values in model
        m.objVal = MathProgBase.getobjval(m.internalModel)
        m.objVal += m.obj.aff.constant
    catch
        m.objVal = NaN
    end
    try
        m.colVal = MathProgBase.getsolution(m.internalModel)
    catch
        m.colVal = fill(NaN, m.numCols)
    end

    return stat
end

function solveSDP(m::Model; suppress_warnings=false)
    @assert (length(m.quadconstr) == 0) && (length(m.obj.qvars1) == 0) # Not sure how SDP and Quadratic mixes at this point

    objaff::AffExpr = m.obj.aff
    assert_isfinite(objaff)
    verify_ownership(m, objaff.vars)

    # Create dense objective vector
    f = zeros(m.numCols)
    for ind in 1:length(objaff.vars)
        f[objaff.vars[ind].col] += objaff.coeffs[ind]
    end

    # find starting column indices for sdp matrices
    sdp_start, sdp_end = Int[], Int[]
    var_cones = Any[]
    for c in m.sdpconstr
        if isa(c.terms,OneIndexedArray)
            frst = c.terms[1,1].col
            last = c.terms[end,end].col
            push!(sdp_start, frst)
            push!(sdp_end, last)
            push!(var_cones, (:SDP,frst:last))
        end
    end

    # Create sparse A matrix
    # First we build it row-wise, then use the efficient transpose
    # Theory is, this is faster than us trying to do it ourselves
    # Intialize storage
    linconstr = m.linconstr::Vector{LinearConstraint}
    numLinRows = length(linconstr)
    numBounds = 0
    nonNeg = Int[]
    nonPos = Int[]
    free   = Int[]
    in_sdp = false
    for i in 1:m.numCols
        lb, ub = m.colLower[i], m.colUpper[i]
        if i in sdp_start
            in_sdp = true
            @assert lb == -Inf && ub == Inf
            continue
        end
        if in_sdp
            @assert lb == -Inf && ub == Inf
            if i in sdp_end
                in_sdp = false
            end
            continue
        end

        if !(lb == 0 || lb == -Inf)
            numBounds += 1
        end
        if !(ub == 0 || ub == Inf)
            numBounds += 1
        end
        if lb == 0
            push!(nonNeg, i)
        elseif ub == 0
            push!(nonPos, i)
        else
            push!(free, i)
        end
    end
    if !isempty(nonNeg)
        push!(var_cones, (:NonNeg,nonNeg))
    end
    if !isempty(nonPos)
        push!(var_cones, (:NonPos,nonPos))
    end
    if !isempty(free)
        push!(var_cones, (:Free,free))
    end

    nnz = numBounds
    for c in 1:numLinRows
        nnz += length(linconstr[c].terms.coeffs)
    end

    numSDPRows = 0
    for c in m.sdpconstr
        if !isa(c.terms, OneIndexedArray)
            n = size(c.terms,1)
            @assert n == size(c.terms,2)
            numSDPRows += convert(Int, n*(n+1)/2)
            for i in 1:n, j in i:n
                nnz += length(c.terms[i,j].coeffs)
            end
        end
    end
    numRows = numLinRows + numBounds + numSDPRows

    b = Array(Float64, numRows)

    I = Int[]
    J = Int[]
    V = Float64[]
    @compat sizehint!(I, nnz)
    @compat sizehint!(J, nnz)
    @compat sizehint!(V, nnz)

    # Fill it up
    nnz = 0
    tmprow = IndexedVector(Float64,m.numCols)
    tmpelts = tmprow.elts
    tmpnzidx = tmprow.nzidx
    nonneg_rows = Int[]
    nonpos_rows = Int[]
    eq_rows     = Int[]
    for c in 1:numLinRows
        if linconstr[c].lb == -Inf
            b[c] = linconstr[c].ub
            push!(nonneg_rows, c)
        elseif linconstr[c].ub == Inf
            b[c] = linconstr[c].lb
            push!(nonpos_rows, c)
        elseif linconstr[c].lb == linconstr[c].ub
            b[c] = linconstr[c].lb
            push!(eq_rows, c)
        else
            error("We currently do not support ranged constraints with conic solvers")
        end

        assert_isfinite(linconstr[c].terms)
        coeffs = linconstr[c].terms.coeffs
        vars = linconstr[c].terms.vars
        # collect duplicates
        for ind in 1:length(coeffs)
            if !is(vars[ind].m, m)
                error("Variable not owned by model present in constraints")
            end
            addelt!(tmprow,vars[ind].col, coeffs[ind])
        end
        nnz = tmprow.nnz
        append!(I, fill(c, nnz))
        indices = tmpnzidx[1:nnz]
        append!(J, indices)
        append!(V, tmpelts[indices])
        empty!(tmprow)
    end

    c = numLinRows
    for idx in 1:m.numCols
        lb = m.colLower[idx]
        if !(lb == 0 || lb == -Inf)
            nnz += 1
            c   += 1
            push!(I, c)
            push!(J, idx)
            push!(V, 1.0)
            b[c] = lb
            push!(nonpos_rows, c)
        end
        ub = m.colUpper[idx]
        if !(ub == 0 || ub == Inf)
            c   += 1
            push!(I, c)
            push!(J, idx)
            push!(V, 1.0)
            b[c] = ub
            push!(nonneg_rows, c)
        end
    end

    con_cones = Any[]
    if !isempty(nonneg_rows)
        push!(con_cones, (:NonNeg,nonneg_rows))
    end
    if !isempty(nonpos_rows)
        push!(con_cones, (:NonPos,nonpos_rows))
    end
    if !isempty(eq_rows)
        push!(con_cones, (:Zero,eq_rows))
    end

    @assert c == numLinRows + numBounds
    for con in m.sdpconstr
        if !isa(con.terms, OneIndexedArray)
            sdp_start = c + 1
            n = size(con.terms,1)
            for i in 1:n, j in i:n
                c += 1
                terms::AffExpr = con.terms[i,j] # should add test that this type assertion is valid elsewhere...
                assert_isfinite(terms)
                coeffs = terms.coeffs
                vars = terms.vars
                # collect duplicates
                for ind in 1:length(coeffs)
                    if !is(vars[ind].m, m)
                        error("Variable not owned by model present in constraints")
                    end
                    if i == j
                        addelt!(tmprow,vars[ind].col, coeffs[ind])
                    else
                        addelt!(tmprow,vars[ind].col,2coeffs[ind])
                    end
                end
                nnz = tmprow.nnz
                indices = tmpnzidx[1:nnz]
                append!(I, fill(c, nnz))
                append!(J, indices)
                append!(V, -tmpelts[indices])
                empty!(tmprow)
                if i == j
                    b[c] =  terms.constant
                else
                    b[c] = 2terms.constant
                end
            end
            push!(con_cones, (:SDP, sdp_start:c))
        end
    end
    @assert c == numRows

    # @show rowptr, colval, rownzval
    # Build the object
    # rowmat = SparseMatrixCSC(m.numCols, numRows, rowptr, colval, rownzval)
    # Note that rowmat doesn't have sorted indices, so technically doesn't
    # follow SparseMatrixCSC format. But it's safe to take the transpose.
    # A = rowmat'
    # @show I, J, V, m.numCols, numRows
    A = sparse(I, J, V, numRows, m.numCols)
    # @show full(A), b

    m.internalModel = MathProgBase.model(m.solver)
    # TODO: uncomment these lines when they work with Mosek
    # supported = MathProgBase.supportedcones(m.internalModel)
    # @assert (:NonNeg in supported) && (:NonPos in supported) && (:Free in supported) && (:SDP in supported)

    MathProgBase.loadconicproblem!(m.internalModel, f, A, b, con_cones, var_cones)
    MathProgBase.setsense!(m.internalModel, m.objSense)
    m.internalModelLoaded = true

    MathProgBase.optimize!(m.internalModel)
    stat = MathProgBase.status(m.internalModel)

    if stat != :Optimal
        !suppress_warnings && warn("Not solved to optimality, status: $stat")
        m.colVal = fill(NaN, m.numCols)
        m.objVal = NaN
        try # guess try/catch is necessary because we're not sure what return status we have
            m.colVal = MathProgBase.getsolution(m.internalModel)
        catch
            m.colVal = fill(NaN, m.numCols)
        end
        try
            # store solution values in model
            m.objVal = MathProgBase.getobjval(m.internalModel)
            m.objVal += m.obj.aff.constant
        catch
            m.objVal = NaN
        end
    else
        # store solution values in model
        m.objVal = MathProgBase.getobjval(m.internalModel)
        m.objVal += m.obj.aff.constant
        m.colVal = MathProgBase.getsolution(m.internalModel)
    end

    return stat
end

function buildInternalModel(m::Model)
    m.nlpdata == nothing || error("buildInternalModel not supported for nonlinear problems")

    anyInts = (length(m.sosconstr) > 0) ||
        any(c-> !(c == :Cont || c == :Fixed), m.colCat)

    if isa(m.solver,UnsetSolver) &&
      (length(m.obj.qvars1) > 0 || length(m.quadconstr) > 0)
        m.solver = MathProgBase.defaultQPsolver
    end
    if anyInts
        if isa(m.solver,UnsetSolver)
            m.solver = MathProgBase.defaultMIPsolver
        end
    else
        if isa(m.solver,UnsetSolver)
            m.solver = MathProgBase.defaultLPsolver
        end
    end
    m.internalModel = MathProgBase.model(m.solver)

    f, rowlb, rowub = prepProblemBounds(m)
    A = prepConstrMatrix(m)
    MathProgBase.loadproblem!(m.internalModel, A, m.colLower, m.colUpper, f, rowlb, rowub, m.objSense)
    addQuadratics(m)

    if anyInts # do MIP stuff
        colCats = vartypes_without_fixed(m)
        MathProgBase.setvartype!(m.internalModel, colCats)
        addSOS(m)
        registercallbacks(m)
        if !all(isnan(m.colVal))
            if applicable(MathProgBase.setwarmstart!, m.internalModel, m.colVal)
                MathProgBase.setwarmstart!(m.internalModel, m.colVal)
            else
                Base.warn_once("Solver does not appear to support providing initial feasible solutions.")
            end
        end
    end
    if applicable(MathProgBase.updatemodel!, m.internalModel)
        MathProgBase.updatemodel!(m.internalModel)
    end
    m.internalModelLoaded = true
    nothing
end

# returns (unsorted) column indices and coefficient terms for merged vector
# assume that v is zero'd
function merge_duplicates{CoefType,IntType<:Integer}(::Type{IntType},aff::GenericAffExpr{CoefType,Variable}, v::IndexedVector{CoefType}, m::Model)
    resize!(v, m.numCols)
    for ind in 1:length(aff.coeffs)
        var = aff.vars[ind]
        is(var.m, m) || error("Variable does not belong to this model")
        addelt!(v, aff.vars[ind].col, aff.coeffs[ind])
    end
    indices = Array(IntType,v.nnz)
    coeffs = Array(CoefType,v.nnz)
    for i in 1:v.nnz
        idx = v.nzidx[i]
        indices[i] = idx
        coeffs[i] = v.elts[idx]
    end
    empty!(v)

    return indices, coeffs

end
