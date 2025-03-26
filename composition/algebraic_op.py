import copy
import random
import string

from problem import IneqProblem

def random_algebraic_op(problem_list, num, name="algtrans_p"):
    # generate num new problems using random algebraic op
    new_problem_list = []
    ranodm_op_list = ["sqrt_all","sqrt_random","sq_all","sq_random","cube_all","cube_random","reciprocal_all","reciprocal_random","exp_all","exp_random","log_all","log_random"]
    for i in range(num):
        while True:
            try:
                op_mode = random.choice(ranodm_op_list)
                orig_p = random.choice(problem_list)
                new_p = algebraic_op(orig_p, mode=op_mode)
                
                further_op = random.choice(["no","reset_from_a","shift_var","mod_var_idx"])
                if further_op != "no":
                    if further_op == "shift_var" or further_op == "reset_from_a":
                        new_p = algebraic_op(new_p, mode=further_op)
                    else:
                        nv = len(new_p.variables)
                        #print(new_p.variables)
                        new_p = algebraic_op(new_p, mode="shift_var")
                        new_p = algebraic_op(new_p, mode="shift_var")
                        new_p = algebraic_op(new_p, mode="shift_var")
                        new_p = algebraic_op(new_p, mode="mod_var_idx", additional_arg=(nv+2))
                new_p.set_name(f"{name}{i}")
                new_problem_list.append(new_p)
                break
            except:
                print("error, retry")
    return new_problem_list

def algebraic_op(P1, mode="reset_from_a", additional_arg=None):
    variables = P1.variables
    new_variable_list = None
    if mode == "reset_from_a":
        transform_dict, new_variable_list = _reset_from_a(P1)
    elif mode == "shift_var":
        transform_dict, new_variable_list = _shift_var(P1)
    elif mode == "mod_var_idx":
        transform_dict, new_variable_list = _mod_var_idx(P1, additional_arg)
    elif mode == "sqrt_all":
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
    elif mode == "exp_all":
        transform_dict = _exp_all(P1)
    elif mode == "exp_random":
        transform_dict = _exp_random(P1)
    elif mode == "log_all":
        transform_dict = _log_all(P1)
    elif mode == "log_random":
        transform_dict = _log_random(P1)
    else:
        raise ValueError("Not implemented algebraic transformation!")
    
    P = IneqProblem()
    if new_variable_list != None:
        new_variables = new_variable_list
    else:
        new_variables = copy.deepcopy(variables)
    P.set_variables(new_variables)

    if P1.condition != None:
        new_condition = [cond.format(**transform_dict) for cond in P1.condition]
        P.set_condition(new_condition)
    

    P.set_statement_lhs(P1.statement_lhs.format(**transform_dict))
    P.set_statement_rhs(P1.statement_rhs.format(**transform_dict))

    P.set_rhs_pos(P1.rhs_pos)

    new_orig_probs = copy.deepcopy(P1.original_problem)
    P.set_original_problem(new_orig_probs)

    return P

def _reset_from_a(P1):
    # reset all variables starting from a
    # eg, previously has x y z
    # reset to a b c
    variables = P1.variables
    total_num = len(variables)
    assert total_num <= 26 , "Problem has too many (>26) variables!"
    transform_dict = dict()
    for i, v in enumerate(variables):
        str_temp = "{"+string.ascii_lowercase[i]+"}"
        transform_dict[v] = str_temp
    
    new_variable_list = []
    for i in range(total_num):
        new_variable_list.append(string.ascii_lowercase[i])
    
    return transform_dict, new_variable_list

def _shift_var(P1):
    # shift by n
    # e.g., previous a b c, n=2
    # change to c d e
    variables = P1.variables
    total_num = len(variables)
    assert total_num <= 26 , "Problem has too many (>26) variables!"

    char_to_index = dict(zip(string.ascii_lowercase, range(26)))

    transform_dict = dict()
    new_variable_list = []
    for v in variables:
        i = char_to_index[v]
        # make sure the variables lies in a-z
        i = (i+1) % 26
        str_temp = "{"+string.ascii_lowercase[i]+"}"
        transform_dict[v] = str_temp
        new_variable_list.append(string.ascii_lowercase[i])
    
    return transform_dict, new_variable_list

def _mod_var_idx(P1, n):

    # shift by n
    # e.g., previous a b c, n=2
    # change to c d e
    variables = P1.variables
    total_num = len(variables)
    assert total_num <= 26 , "Problem has too many (>26) variables!"

    char_to_index = dict(zip(string.ascii_lowercase, range(26)))

    transform_dict = dict()
    new_variable_list = []
    for v in variables:
        i = char_to_index[v]
        # make sure the variables lies in a-z
        i = i % n

        str_temp = "{"+string.ascii_lowercase[i]+"}"
        transform_dict[v] = str_temp
        assert string.ascii_lowercase[i] not in new_variable_list , "Mod operation failed : two variables mapped to same after mod."
        new_variable_list.append(string.ascii_lowercase[i])
    
    return transform_dict, new_variable_list

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

    return transform_dict

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
    return transform_dict

def _exp_all(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "((Real.exp {"+v+"}) - 1)"
        transform_dict[v] = str_temp
    
    return transform_dict

def _exp_random(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "{"+v+"}"
        transform_dict[v] = str_temp

    vr = random.choice(variables)
    str_temp = "((Real.exp {"+v+"}) - 1)"
    transform_dict[vr] = str_temp

    return transform_dict

def _log_all(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "(Real.log ({"+v+"}+1))"
        transform_dict[v] = str_temp
    
    return transform_dict

def _log_random(P1):
    variables = P1.variables
    transform_dict = dict()
    for v in variables:
        str_temp = "{"+v+"}"
        transform_dict[v] = str_temp

    vr = random.choice(variables)
    str_temp = "(Real.log ({"+vr+"}+1))"
    transform_dict[vr] = str_temp

    return transform_dict

if __name__ == '__main__':
    P1 = IneqProblem()
    P1.set_name("test")
    P1.set_variables(["x", "y", "z"])
    P1.set_condition("{x} + {y} + {z} = 1")
    P1.set_statement_lhs("(1:ℝ)/{x} + (1:ℝ)/{y} + (1:ℝ)/{z}")
    P1.set_statement_rhs("(9:ℝ)")
    P1.set_rhs_pos(True)
    
    P = algebraic_op(P1,mode='mod_var_idx', additional_arg=5)
    print(P.variables)
    print(P.condition)
    print(P.statement_lhs)
    print(P.statement_rhs)
    print(P.to_lean())