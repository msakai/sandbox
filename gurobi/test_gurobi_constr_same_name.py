import gurobipy

model = gurobipy.Model()
x = model.addVar(name="x")

model.addConstr(x >= 1, name="lb")
model.addConstr(x <= 2, name="ub")
model.addConstr(x >= 10, name="lb")
model.addConstr(x <= 11, name="ub")

model.write("model.lp")
# \ LP format - for model browsing. Use MPS format to capture full model detail.
# Minimize
#
# Subject To
#  lb: x >= 1
#  ub: x <= 2
#  lb: x >= 10
#  ub: x <= 11
# Bounds
# End

model.optimize()

if model.Status == gurobipy.GRB.INFEASIBLE:
    model.computeIIS()
    model.write('iismodel.ilp')

# \ Model _copy
# \ LP format - for model browsing. Use MPS format to capture full model detail.
# Minimize
#
# Subject To
#  ub: x <= 2
#  lb: x >= 10
# Bounds
#  x free
# End
