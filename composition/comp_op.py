from problem import IneqProblem

def comp_add(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : f1(X) + f2(X) \ge g1(X) + g2(X)
    P.statement_lhs : "f1(X) + f2(X)"
    P.statement_rhs : "g1(X) + g2(X)"
    """
    # set the variables of the new problem to be the union of P1 and P2
    v1 = P1.variables
    v2 = P2.variables
    new_variables = v1.deepcopy()
    for v in v2:
        if v not in new_variables:
            new_variables.append(v)
    P = IneqProblem()
    P.set_variables(new_variables)

    # set the condition, make sure that there is at most 1 condition
    assert (P1.condition == None or P2.condition == None), "cannot compose two problems both with condition"

    if P1.condition != None:
        P.set_condition(P1.condition)
    elif P2.condition != None:
        P.set_condition(P2.condition)
    
    # set the statement
    lhs = P1.statement_lhs + " + " + P2.statemnet_lhs
    rhs = P1.statement_rhs + " + " + P2.statemnet_rhs

    P.set_statement_lhs(lhs)
    P.set_statement_rhs(rhs)

    return P