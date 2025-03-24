import copy
import random

from problem import IneqProblem

def algebraic_op(P1, mode="sqrt_all"):
    variables = P1.variables
    
    if mode == "sqrt_all":
        transform_dict = _sqrt_all(P1)
    elif mode == "sqrt_random":
        transform_dict = _sqrt_random(P1)
    elif mode == "sq_all":
        transform_dict = _sq_all(P1)
    elif mode == "sq_random":
        transform_dict = _sq_random(P1)
    elif mode == "cube_all":
        transform_dict = _cube_all(P1)
    elif mode == "cube_random":
        transform_dict = _cube_random(P1)
    elif mode == "reciprocal_all":
        transform_dict = _reciprocal_all(P1)
    elif mode == "reciprocal_random":
        transform_dict = _reciprocal_random(P1)
    else:
        raise ValueError("Not implemented algebraic transformation!")
    
    P = IneqProblem()
    new_variables = copy.deepcopy(variables)
    P.set_variables(new_variables)

    if P1.condition != None:
        new_condition = [cond.format(**transform_dict) for cond in P1.condition]
        P.set_condition(new_condition)
    
    P.set_statement_lhs(P1.statement_lhs.format(**transform_dict))
    P.set_statement_rhs(P1.statement_rhs.format(**transform_dict))

    P.set_rhs_pos(P1.rhs_pos)

    return P

def shift_var(P1):
    pass

def _sqrt_all(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "(√{"+v+"})"
        transform_dict[v] = str_temp
    
    return transform_dict

def _sqrt_random(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "{"+v+"}"
        transform_dict[v] = str_temp

    vr = random.choice(variables)
    str_temp = "(√{"+vr+"})"
    transform_dict[vr] = str_temp
    
    return transform_dict

def _sq_all(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "({"+v+"}^2)"
        transform_dict[v] = str_temp
    
    return transform_dict

def _sq_random(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "{"+v+"}"
        transform_dict[v] = str_temp

    vr = random.choice(variables)
    str_temp = "({"+vr+"}^2)"
    transform_dict[vr] = str_temp
    
    return transform_dict

def _cube_all(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "({"+v+"}^3)"
        transform_dict[v] = str_temp
    
    return transform_dict

def _cube_random(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "{"+v+"}"
        transform_dict[v] = str_temp

    vr = random.choice(variables)
    str_temp = "({"+vr+"}^3)"
    transform_dict[vr] = str_temp

def _reciprocal_all(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "(1/{"+v+"})"
        transform_dict[v] = str_temp
    
    return transform_dict

def _reciprocal_random(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "{"+v+"}"
        transform_dict[v] = str_temp

    vr = random.choice(variables)
    str_temp = "(1/{"+vr+"})"
    transform_dict[vr] = str_temp

if __name__ == '__main__':
    P1 = IneqProblem()
    P1.set_name("test")
    P1.set_variables(["a", "b", "c"])
    P1.set_condition("{a} + {b} + {c} = 1")
    P1.set_statement_lhs("(1:ℝ)/{a} + (1:ℝ)/{b} + (1:ℝ)/{c}")
    P1.set_statement_rhs("(9:ℝ)")
    P1.set_rhs_pos(True)
    
    P = algebraic_op(P1,mode='sqrt_random')
    print(P.to_lean())