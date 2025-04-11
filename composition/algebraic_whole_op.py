import copy
import random

from problem import IneqProblem

def random_algebraic_whole(problem_list1, problem_list2, num, name="alge_whole_p"):
    new_problem_list = []
    random_comp_pos_list = ["exp","sq","cube","sqrt","log"]
    random_comp_list = ["exp","cube"]
    for i in range(num):
        while True:
            try:
                P1 = random.choice(problem_list1)
                if P1.rhs_pos:
                    alge_whole_op = random.choice(random_comp_pos_list)
                else:
                    alge_whole_op = random.choice(random_comp_list)


                new_p = algebraic_whole_op(P1, mode=alge_whole_op)
                new_p.set_name(f"{name}{i}")
                new_problem_list.append(new_p)
                break
            except:
                print("Error happen during composition, retry")
    return new_problem_list

def algebraic_whole_op(P1, mode="exp"):
    """
    input: two problems P1 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    new problem P
    P.statement_lhs and P.statement_rhs are determined by the mode
    """
    # set the variables of the new problem to be the union of P1
    v1 = P1.variables
    new_variables = copy.deepcopy(v1)

    P = IneqProblem()
    P.set_variables(new_variables)


    # in this case, we can combine two conditions together
    condition_list = []
    if P1.condition != None:
        condition_list = condition_list + P1.condition
        P.set_condition(condition_list)
    
    rhs_pos = False
    # set the statement
    if mode=="exp":
        # direct addition
        lhs, rhs, rhs_pos = _alge_whole_exp(P1)
    elif mode=="sq":
        # direct addition
        lhs, rhs, rhs_pos = _alge_whole_sq(P1)
    elif mode=="cube":
        # direct addition
        lhs, rhs, rhs_pos = _alge_whole_cube(P1)
    elif mode=="sqrt":
        # direct addition
        lhs, rhs, rhs_pos = _alge_whole_sqrt(P1)
    elif mode=="log":
        # direct addition
        lhs, rhs, rhs_pos = _alge_whole_log(P1)
    else:
        raise ValueError("Not Implemented Algebraic Whole Op")

    P.set_statement_lhs(lhs)
    P.set_statement_rhs(rhs)
    P.set_rhs_pos(rhs_pos)

    new_orig_probs = copy.deepcopy(P1.original_problem)
    P.set_original_problem(new_orig_probs)

    return P

def _alge_whole_exp(P1):
    """
    input: two problems P1 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    new problem P
    P statement : Real.exp f1(X) \ge Real.exp g1(X)
    P.statement_lhs : "Real.exp f1(X)"
    P.statement_rhs : "Real.exp g1(X)"
    """
    lhs = f"Real.exp ({P1.statement_lhs})"
    rhs = f"Real.exp ({P1.statement_rhs})"
    
    rhs_pos = True
    return lhs, rhs, rhs_pos

def _alge_whole_sq(P1):
    """
    input: two problems P1 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    new problem P
    P statement : (f1(X))^2 \ge (g1(X))^2
    P.statement_lhs : "(f1(X))^2"
    P.statement_rhs : "(g1(X))^2"
    """
    
    assert P1.rhs_pos , "make sure rhs is pos"
    lhs = f"({P1.statement_lhs})^2"
    rhs = f"({P1.statement_rhs})^2"
    
    rhs_pos = True
    return lhs, rhs, rhs_pos

def _alge_whole_cube(P1):
    """
    input: two problems P1 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    new problem P
    P statement : (f1(X))^3 \ge (g1(X))^3
    P.statement_lhs : "(f1(X))^3"
    P.statement_rhs : "(g1(X))^3"
    """
    
    lhs = f"({P1.statement_lhs})^3"
    rhs = f"({P1.statement_rhs})^3"
    
    rhs_pos = P1.rhs_pos
    return lhs, rhs, rhs_pos

def _alge_whole_sqrt(P1):
    """
    input: two problems P1 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    new problem P
    P statement : √(f1(X)) \ge √(g1(X))
    P.statement_lhs : "√(f1(X))"
    P.statement_rhs : "√(g1(X))"
    """
    
    assert P1.rhs_pos , "make sure rhs is pos"
    lhs = f"√({P1.statement_lhs})"
    rhs = f"√({P1.statement_rhs})"
    
    rhs_pos = True
    return lhs, rhs, rhs_pos

def _alge_whole_log(P1):
    """
    input: two problems P1 : IneqProblem
    P1 statement : f1(X) \ge g1(X)
    new problem P
    P statement : Real.log (f1(X)) \ge Real.log (g1(X))
    P.statement_lhs : "Real.log (f1(X))"
    P.statement_rhs : "Real.log (g1(X))"
    """
    
    assert P1.rhs_pos , "make sure rhs is pos"
    lhs = f"Real.log ({P1.statement_lhs})"
    rhs = f"Real.log ({P1.statement_rhs})"
    # to make things easy, just assume that after transformation, rhs is not guaranteed to be positive
    rhs_pos = False
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

    P = algebraic_whole_op(P1, mode="log")
    print(P.condition)
    print(P.rhs_pos)
    print(P.to_lean())
    with open("test.log", "w") as f:
        f.writelines([P.to_lean()])