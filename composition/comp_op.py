import copy
import random

from problem import IneqProblem

def random_comp(problem_list1, problem_list2, num, name="comp_p"):
    new_problem_list = []
    random_comp_list = ["add","weighted_sum","mul","div","reciprocal","maxima","minima"]
    for i in range(num):
        while True:
            try:
                comp_op = random.choice(random_comp_list)
                P1 = random.choice(problem_list1)
                P2 = random.choice(problem_list2)
                new_p = comp(P1, P2, mode=comp_op)
                new_p.set_name(f"{name}{i}")
                new_problem_list.append(new_p)
                break
            except:
                print("Error happen during composition, retry")
    return new_problem_list

def comp(P1, P2, mode="add"):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P.statement_lhs and P.statement_rhs are determined by the mode
    """
    # set the variables of the new problem to be the union of P1 and P2
    v1 = P1.variables
    v2 = P2.variables
    new_variables = copy.deepcopy(v1)
    for v in v2:
        if v not in new_variables:
            new_variables.append(v)
    P = IneqProblem()
    P.set_variables(new_variables)

    # first check if two problems have totally different variablees
    flag = False
    for v in P2.variables:
        if v in P1.variables:
            flag = True
            break
    
    if flag:
        # set the condition, make sure that there is at most 1 condition
        assert (P1.condition == None or P2.condition == None), "cannot compose two problems both with condition"

        if P1.condition != None:
            P.set_condition(P1.condition)
        elif P2.condition != None:
            P.set_condition(P2.condition)
    else:
        # in this case, we can combine two conditions together
        condition_list = []
        if P1.condition != None:
            condition_list = condition_list + P1.condition
        if P2.condition != None:
            condition_list = condition_list + P2.condition
        P.set_condition(condition_list)
    
    rhs_pos = False
    # set the statement
    if mode=="add":
        # direct addition
        lhs, rhs, rhs_pos = _comp_add(P1, P2)
    elif mode=="weighted_sum":
        lhs, rhs, rhs_pos = _comp_weightedsum(P1, P2)
    elif mode=="mul":
        lhs, rhs, rhs_pos = _comp_mul(P1, P2)
    elif mode=="div":
        lhs, rhs, rhs_pos = _comp_div(P1, P2)
    elif mode=="reciprocal":
        lhs, rhs, rhs_pos = _comp_reciprocal(P1, P2)
    elif mode=="maxima":
        lhs, rhs, rhs_pos = _comp_maxima(P1, P2)
    elif mode=="minima":
        lhs, rhs, rhs_pos = _comp_minima(P1, P2)
    else:
        raise ValueError("Not Implemented Comp Op")

    P.set_statement_lhs(lhs)
    P.set_statement_rhs(rhs)
    P.set_rhs_pos(rhs_pos)

    new_orig_probs = copy.deepcopy(P1.original_problem)
    for orig_prob_name in P2.original_problem:
        if orig_prob_name not in new_orig_probs:
            new_orig_probs.append(orig_prob_name)
    P.set_original_problem(new_orig_probs)

    return P

def _comp_add(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : f1(X) + f2(X) \ge g1(X) + g2(X)
    P.statement_lhs : "f1(X) + f2(X)"
    P.statement_rhs : "g1(X) + g2(X)"
    """
    lhs = P1.statement_lhs + " + " + P2.statement_lhs
    if random.randint(0,1) > 0:
        rhs = P1.statement_rhs + " + " + P2.statement_rhs
    else:
        rhs = P2.statement_rhs + " + " + P1.statement_rhs
    rhs_pos = False
    if P1.rhs_pos and P2.rhs_pos:
        rhs_pos = True
    return lhs, rhs, rhs_pos

def _comp_weightedsum(P1, P2, mu=3, lamb=2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : mu * f1(X) + lamb * f2(X) \ge mu * g1(X) + lamb * g2(X)
    P.statement_lhs : "mu * f1(X) + lamb * f2(X)"
    P.statement_rhs : "mu * g1(X) + lamb * g2(X)"
    """
    lhs = f"({mu}:ℝ) * ({P1.statement_lhs}) + ({lamb}:ℝ) * ({P2.statement_lhs})"
    if random.randint(0,1) > 0:
        rhs = f"({mu}:ℝ) * ({P1.statement_rhs}) + ({lamb}:ℝ) * ({P2.statement_rhs})"
    else:
        rhs = f"({lamb}:ℝ) * ({P2.statement_rhs}) + ({mu}:ℝ) * ({P1.statement_rhs})"
    rhs_pos = False
    if P1.rhs_pos and P2.rhs_pos:
        rhs_pos = True
    return lhs, rhs, rhs_pos

def _comp_mul(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : f1(X) * f2(X) \ge g1(X) * g2(X)
    P.statement_lhs : "f1(X) * f2(X)"
    P.statement_rhs : "g1(X) * g2(X)"
    """
    # need both P1 and P2 to have positive RHS
    assert P1.rhs_pos and P2.rhs_pos, "Require both problems to have positive RHS to use _comp_mul"

    lhs = f"({P1.statement_lhs}) * ({P2.statement_lhs})"
    if random.randint(0,1) > 0:
        rhs = f"({P1.statement_rhs}) * ({P2.statement_rhs})"
    else:
        rhs = f"({P2.statement_rhs}) * ({P1.statement_rhs})"
    
    return lhs, rhs, True

def _comp_div(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : f1(X) / g2(X) \ge g1(X) / f2(X)
    P.statement_lhs : "f1(X) / g2(X)"
    P.statement_rhs : "g1(X) / f2(X)"
    """
    # need both P1 and P2 to have positive RHS
    assert P1.rhs_pos and P2.rhs_pos, "Require both problems to have positive RHS to use _comp_div"

    lhs = f"({P1.statement_lhs}) / ({P2.statement_rhs})"
    rhs = f"({P1.statement_rhs}) / ({P2.statement_lhs})"

    return lhs, rhs, True

def _comp_reciprocal(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : 1 / g1(X) + 1 / g2(X) \ge 1 / f1(X) + 1 / f2(X)
    P.statement_lhs : "1 / g1(X) + 1 / g2(X)"
    P.statement_rhs : "1 / f1(X) + 1 / f2(X)"
    """
    # need both P1 and P2 to have positive RHS
    assert P1.rhs_pos and P2.rhs_pos, "Require both problems to have positive RHS to use _comp_reciprocal"

    lhs = f"(1:ℝ)/({P1.statement_rhs}) + (1:ℝ)/({P2.statement_rhs})"
    if random.randint(0,1) > 0:
        rhs = f"(1:ℝ)/({P1.statement_lhs}) + (1:ℝ)/({P2.statement_lhs})"
    else:
        rhs = f"(1:ℝ)/({P2.statement_lhs}) + (1:ℝ)/({P1.statement_lhs})"

    return lhs, rhs, True

def _comp_maxima(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : max f1(X)  f2(X) \ge max g1(X) g2(X)
    P.statement_lhs : "max f1(X) f2(X)"
    P.statement_rhs : "max g1(X) g2(X)"
    """
    lhs = f"max ({P1.statement_lhs}) ({P2.statement_lhs})"
    if random.randint(0,1) > 0:
        rhs = f"max ({P1.statement_rhs}) ({P2.statement_rhs})"
    else:
        rhs = f"max ({P2.statement_rhs}) ({P1.statement_rhs})"
    rhs_pos = False
    if P1.rhs_pos and P2.rhs_pos:
        rhs_pos = True
    return lhs, rhs, rhs_pos

def _comp_minima(P1, P2):
    """
    input: two problems P1 P2 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    P2 statement : f2(X) \ge g2(X)
    new problem P
    P statement : min f1(X)  f2(X) \ge min g1(X) g2(X)
    P.statement_lhs : "min f1(X) f2(X)"
    P.statement_rhs : "min g1(X) g2(X)"
    """
    lhs = f"min ({P1.statement_lhs}) ({P2.statement_lhs})"
    if random.randint(0,1) > 0:
        rhs = f"min ({P1.statement_rhs}) ({P2.statement_rhs})"
    else:
        rhs = f"min ({P2.statement_rhs}) ({P1.statement_rhs})"
    rhs_pos = False
    if P1.rhs_pos and P2.rhs_pos:
        rhs_pos = True
    return lhs, rhs, rhs_pos

if __name__ == '__main__':
    P1 = IneqProblem()
    P1.set_name("test")
    P1.set_variables(["a", "b", "c"])
    P1.set_condition("{a} + {b} + {c} = 1")
    P1.set_statement_lhs("(1:ℝ)/{a} + (1:ℝ)/{b} + (1:ℝ)/{c}")
    P1.set_statement_rhs("(9:ℝ)")
    P1.set_rhs_pos(True)

    P2 = IneqProblem()
    P2.set_name("test")
    P2.set_variables(["d", "e", "f"])
    P2.set_condition("{d} + {e} + {f} = 1")
    P2.set_statement_lhs("({d} + {e} + {f}) * ((1:ℝ)/{d} + (1:ℝ)/{e} + (1:ℝ)/{f})")
    P2.set_statement_rhs("(9:ℝ)")
    P2.set_rhs_pos(True)

    P = comp(P1, P2, mode="mul")
    print(P.condition)
    print(P.rhs_pos)
    print(P.to_lean())