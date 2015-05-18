using JuMP

m = Model()
@defVar(m, X[1:3,1:3], SDP)

@addSDPConstraint(m, X >= ones(3,3))
@setObjective(m, Min, trace(ones(3,3)*X))

stat = solve(m)
