import json
import random

from problem import IneqProblem
import algebraic_op
import comp_op

def read_problems_from_jsonl(filename):
    list_of_dicts = []
    with open(filename, "r") as file:
        for line in file:
            list_of_dicts.append(json.loads(line))
    
    problems_pool = []
    for d in list_of_dicts:
        P = IneqProblem()
        P.set_name(d["name"])
        P.set_original_problem(d["name"])
        if len(d["variables"]) > 1:
            P.set_variables(d["variables"].split(" "))
        else:
            P.set_variables([d["variables"]])
        if (d["condition"] != None) and (d["condition"] != ""):
            P.set_condition(d["condition"])
        P.set_statement_lhs(d["statement_lhs"])
        P.set_statement_rhs(d["statement_rhs"])
        P.set_rhs_pos(d["rhs_pos"])
        
        problems_pool.append(P)
    
    return problems_pool

def problem_list_to_jsonl(problems, filename):
    with open(filename, "w") as f:
        for p in problems:
            d = p.to_dict()
            f.write(json.dumps(d) + "\n")

if __name__ == '__main__':
    pp = read_problems_from_jsonl("sq_problems.jsonl")
    pp = [algebraic_op.algebraic_op(p, "reset_from_a") for p in pp]
    
    new_p_alg = algebraic_op.random_algebraic_op(pp, 10)
    new_p_comp = comp_op.random_comp(pp, pp, 10)
    #new_p_comp2 = comp_op.random_comp(new_p_comp, new_p_alg, 10)
    for p in new_p_comp:
        print(p.to_lean())
    problem_list_to_jsonl(new_p_comp, "test_comp.jsonl")