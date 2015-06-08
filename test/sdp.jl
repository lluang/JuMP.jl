ispsd(x::Matrix) = minimum(eigvals(x)) ≥ -1e-5

facts("[sdp] Test simple SDP") do
for solver in sdp_solvers
context("With solver $(typeof(solver))") do
    m = Model()
    @defVar(m, 0 <= X[1:3,1:3] <= 1/2*eye(3,3), SDP)
    @defVar(m, -ones(5,5) <= Y[1:5,1:5] <= 2*ones(5,5), SDP)
    @defVar(m, Z[1:4,1:4] <= ones(4,4), SDP)

    @addConstraint(m, trace(X) == 1)
    @addConstraint(m, trace(Y) == 3)
    @addConstraint(m, trace(Z) == -1)
    @setObjective(m, Max, X[1,2] + Y[1,2] + Z[1,2])
    solve(m)

    XX, YY, ZZ, = getValue(X), getValue(Y), getValue(Z)
    Xtrue = [0.25 0.25 0
             0.25 0.25 0
             0    0    0.5]
    Ytrue = fill(0.6, 5, 5)
    Ztrue = [-1.5  3.5 1 1
              3.5 -1.5 1 1
              1    1   1 1
              1    1   1 1]

    @fact norm(XX-Xtrue) => roughly(0, 1e-2)
    @fact norm(YY-Ytrue) => roughly(0, 1e-2)
    @fact norm(ZZ-Ztrue) => roughly(0, 1e-2)
    @fact ispsd(XX) => true
    @fact ispsd(1/2*eye(3,3)-XX) => true
    @fact ispsd(YY+ones(5,5)) => true
    @fact ispsd(2*ones(5,5)-YY) => true
    @fact ispsd(ones(4,4)-ZZ) => true
    @fact trace(XX) => roughly( 1, 1e-5)
    @fact trace(YY) => roughly( 3, 1e-5)
    @fact trace(ZZ) => roughly(-1, 1e-5)
    @fact getObjectiveValue(m) => roughly(4.35, 1e-3)

    @setObjective(m, Min, X[1,2] + Y[1,2] + Z[1,2])
    solve(m)

    XX, YY, ZZ, = getValue(X), getValue(Y), getValue(Z)
    Xtrue = [ 0.25 -0.25 0
             -0.25  0.25 0
              0     0    0.5]
    Ytrue = fill(0.6, 5, 5)
    Ztrue = [-1.5 -1.5 1 1
             -1.5 -1.5 1 1
              1    1   1 1
              1    1   1 1]

    @fact norm(XX-Xtrue) => roughly(0, 1e-2)
    @fact norm(YY-Ytrue) => roughly(0, 1e-2)
    @fact norm(ZZ-Ztrue) => roughly(0, 1e-2)
    @fact ispsd(XX) => true
    @fact ispsd(1/2*eye(3,3)-XX) => true
    @fact ispsd(YY+ones(5,5)) => true
    @fact ispsd(2*ones(5,5)-YY) => true
    @fact ispsd(ones(4,4)-ZZ) => true
    @fact trace(XX) => roughly( 1, 1e-5)
    @fact trace(YY) => roughly( 3, 1e-5)
    @fact trace(ZZ) => roughly(-1, 1e-5)

    # Test SDP constraints
    m = Model()
    @defVar(m, X[1:3,1:3], SDP)

    @addSDPConstraint(m, X >= ones(3,3))
    @setObjective(m, Min, trace(ones(3,3)*X))
    stat = solve(m)
    @fact stat => :Optimal
    XX = getValue(X)
    @fact ispsd(XX) => true
    @fact ispsd(XX - ones(3,3)) => true
    @fact norm(XX-[23 2 2;2 23 2;2 2 23]./9) => roughly(0,1e-3)

    # Another test SDP
    m = Model()
    @defVar(m, X[1:3,1:3], SDP)
    @defVar(m, Y[1:2,1:2], SDP)

    C = eye(3,3)
    A1 = zeros(3,3)
    A1[1,1] = 1.0
    A2 = zeros(3,3)
    A2[2,2] = 1.0
    A3 = zeros(3,3)
    A3[3,3] = 1.0
    D = eye(2,2)
    B1 = ones(2,2)
    B2 = zeros(2,2)
    B2[1,1] = 1
    B3 = zeros(2,2)
    B3[1,2] = B3[2,1] = 2

    @setObjective(m, Min, trace(C*X)+1+trace(D*Y))
    @addConstraint(m, trace(A1*X-eye(3,3)/3) == 0)
    @addConstraint(m, 2*trace(A2*X) == 1)
    @addConstraint(m, trace(A3*X) >= 2)
    @addConstraint(m, trace(B1*Y) == 1)
    @addConstraint(m, trace(B2*Y) == 0)
    @addConstraint(m, trace(B3*Y) <= 0)
    @addConstraint(m, trace(A1*X)+trace(B1*Y) >= 1)
    @addConstraint(m, Y[2,2] == 1)

    stat = solve(m)
    @fact stat => :Optimal
    XX, YY = getValue(X), getValue(Y)
    @fact trace(A1*XX-eye(3,3)/3) => roughly(0, 1e-8)
    @fact 2*trace(A2*XX) => roughly(1, 1e-8)
    @fact trace(A3*XX) >= 2 => true
    @fact trace(B1*YY) => roughly(1, 1e-8)
    @fact trace(B2*YY) => roughly(0, 1e-8)
    @fact trace(B3*YY) <= 0 => true
    @fact trace(A1*XX)+trace(B1*YY) >= 1 => true
    @fact YY[2,2] => roughly(1, 1e-8)
    @fact norm(XX - diagm([1,.5,2])) => roughly(0, 1e-4)
    @fact norm(YY - [0 0;0 1]) => roughly(0, 1e-4)
end; end; end

facts("[sdp] Nonsensical SDPs") do
    m = Model()
    @fact_throws @defVar(m, unequal[1:5,1:6], SDP)
    # Some of these errors happen at compile time, so we can't use @fact_throws
    @fact macroexpand(:(@defVar(m, notone[1:5,2:6], SDP))).head => :error
    @fact macroexpand(:(@defVar(m, oneD[1:5], SDP))).head => :error
    @fact macroexpand(:(@defVar(m, threeD[1:5,1:5,1:5], SDP))).head => :error
    @fact macroexpand(:(@defVar(m, psd[2] <= rand(2,2), SDP))).head => :error
    @fact_throws @defVar(m, -ones(3,4) <= foo[1:4,1:4] <= ones(4,4), SDP)
    @fact_throws @defVar(m, -ones(4,4) <= foo[1:4,1:4] <= ones(4,5), SDP)
    @fact_throws @defVar(m, -rand(5,5) <= nonsymmetric[1:5,1:5] <= rand(5,5), SDP)
    @fact_throws @defVar(m, -1.0 <= nonzero[1:6,1:6] <= 1.0, SDP)

    # test that nonsymmetric constraints throw
    @defVar(m, X[1:5,1:5], SDP)
    Y = eye(5)*X
    Y[1,2] += 1
    @fact_throws @addSDPConstraint(m, Y <= ones(5,5))
end

facts("[sdp] SDP with quadratics") do
for solver in sdp_solvers
context("With solver $(typeof(solver))") do
    m = Model(solver=solver)
    @defVar(m, X[1:2,1:2], SDP)
    @defVar(m, y[0:2])
    @addConstraint(m, y[0] >= 0)
    @addConstraint(m, y[1]^2 + y[2]^2 <= y[0]^2)
    @addSDPConstraint(m, X <= eye(2))
    @addConstraint(m, X[1,1] + X[1,2] == y[1] + y[2])
    @setObjective(m, Max, trace(X) - y[0])
    stat = solve(m)

    @fact stat => :Optimal
    XX, yy = getValue(X), getValue(y)
    @fact ispsd(XX) => true
    @fact yy[0] >= 0 => true
    @fact yy[1]^2 + yy[2]^2 <= yy[0]^2 => true
    @fact ispsd(eye(2)-XX) => true
    @fact (XX[1,1] + XX[1,2]) - (yy[1] + yy[2]) => roughly(0,1e-4)
    @fact norm(XX - eye(2)) => roughly(0, 1e-4)
    @fact norm(yy - [1/sqrt(2), 0.5, 0.5]) => roughly(0, 1e-4)
    @fact getObjectiveValue(m) => roughly(1.293, 1e-2)
end; end; end
