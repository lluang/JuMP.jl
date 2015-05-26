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
end; end; end

facts("[sdp] Nonsensical SDP variable construction") do
    m = Model()
    @fact_throws @defVar(m, unequal[1:5,1:6], SDP)
    @fact_throws @defVar(m, notone[1:5,2:6], SDP)
    @fact_throws @defVar(m, oneD[1:5], SDP)
    @fact_throws @defVar(m, threeD[1:5,1:5,1:5], SDP)
    @fact_throws @defVar(m, psd[2] <= rand(2,2), SDP)
    @fact_throws @defVar(m, -ones(3,4) <= foo[1:4,1:4] <= ones(4,4), SDP)
    @fact_throws @defVar(m, -ones(4,4) <= foo[1:4,1:4] <= ones(4,5), SDP)
    @fact_throws @defVar(m, -rand(5,5) <= nonsymmetric[1:5,1:5] <= rand(5,5), SDP)
    @fact_throws @defVar(m, -1.0 <= nonzero[1:6,1:6] <= 1.0, SDP)
end
