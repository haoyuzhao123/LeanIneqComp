import os
import sys
import time
import json
import ctypes
import resource
import tempfile
import traceback
import threading
import pexpect
import subprocess
import multiprocessing as mp
from pprint import pprint
# from memory_profiler import profile


import random

import numpy as np

def split_list_randomly(lst, k):
    random.shuffle(lst)  # Shuffle the list randomly
    return list(map(list, np.array_split(lst, k)))  # Split into k approximately equal parts


from prover.lean.ast_parser import lean4_parser
from prover.workers import ProcessScheduler
from prover.utils import AttrDict

HOME_DIR = os.path.expanduser('/scratch/gpfs/st3812')

# HOME_DIR = os.path.expanduser('~')

DEFAULT_LAKE_PATH = f'{HOME_DIR}/.elan/bin/lake'

DEFAULT_LEAN_WORKSPACE = 'mathlib4/'

DEFAULT_IMPORTS = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

IMPORT_TIMEOUT = 300
PROOF_TIMEOUT = 100


statement_sample = "\n/-- Show that $\frac{9x^2\\sin^2 x + 4}{x\\sin x} \\geq 12$ for $0 < x < \\pi$.-/\ntheorem aime_1983_p9 (x : ℝ) (h₀ : 0 < x ∧ x < Real.pi) :\n  12 ≤ (9 * (x ^ 2 * Real.sin x ^ 2) + 4) / (x * Real.sin x) :="

proof_code_sample_1 = " by\n  /-\n  To find the minimum value of $\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$, we need to show that it is at least 12. We start by noting that the expression can be rewritten using the division property of inequalities. We then use the fact that \\$sin x$ and $x$ are positive in the given range to establish the necessary inequalities. Finally, we apply these results to conclude that the minimum value is indeed 12.\n  -/\n  -- We start by ensuring that the product x * sin x is positive in the given range.\n  have h₁ : 0 < x * Real.sin x := by\n    apply mul_pos\n    -- x is positive in the range (0, π).\n    exact h₀.1\n    -- sin x is positive in the range (0, π).\n    exact Real.sin_pos_of_pos_of_lt_pi h₀.1 h₀.2\n  -- Using the division property of inequalities, we rewrite the expression.\n  rw [le_div_iff h₁]\n  /- tactic state:\n    x : ℝ\n    h₀ : 0 < x ∧ x < π\n    h₁ : 0 < x * x.sin\n    ⊢ 12 * (x * x.sin) ≤ 9 * (x ^ 2 * x.sin ^ 2) + 4\n  -/\n  -- This is equivalent to showing that 9x^2 sin^2 x - 12x sin x + 4 ≥ 0, and the left hand side can be rewritten as a perfect square (3x sin x - 2)^2.\n  -- We use the fact that (3x sin x - 2)^2 is non-negative to establish this.\n  nlinarith [sq_nonneg (3 * x * Real.sin x - 2)]\n"

proof_code_sample_2 = " by sorry"

proof_code_sample_3 = "\n/-- For a series $\\{a_n\\}$, we have $\\sum_{n=0}^{99} a_{n+1}^2 = 1$. Show that $\\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \\frac{12}{25}$.-/\ntheorem imosl_2007_algebra_p6 (a : \u2115 \u2192 NNReal) (h\u2080 : (\u2211 x in Finset.range 100, a (x + 1) ^ 2) = 1) :\n    (\u2211 x in Finset.range 99, a (x + 1) ^ 2 * a (x + 2)) + a 100 ^ 2 * a 1 < 12 / 25 := by\n  /-\n  Given a series \\(\\{a_n\\}\\), we know that \\(\\sum_{n=0}^{99} a_{n+1}^2 = 1\\). We need to show that \\(\\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \\frac{12}{25}\\).\n  -/\n  -- Simplify the given sum condition using basic arithmetic properties.\n  simp_all [Finset.sum_range_succ, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc,\n    add_left_comm, add_comm]\n  -- Use linear arithmetic to prove the inequality.\n  <;> nlinarith [h\u2080]"

proof_code_sample_4 = "BUG" * 4096

proof_code_sample_5 = DEFAULT_IMPORTS


# proof_code_list_sample = [proof_code_sample] * 1
# proof_code_list_sample = [statement_sample + proof_code_sample_1, statement_sample + proof_code_sample_2] * 2

proof_code_list_sample = ([{"name": "test_problem", "code": statement_sample + proof_code_sample_1}] + [{"name": "test_problem", "code": statement_sample + proof_code_sample_2}]) * 1
# proof_code_list_sample.append({'name': 'timeout_problem', 'code': proof_code_sample_3})
proof_code_list_sample.append({'name': 'timeout_problem', 'code': proof_code_sample_5})

problem_list_sample = [proof_code_list_sample] * 1 #each item in problem_list_sample is a proof_code_list which I want a single process to do

# proof_code_list needs to have problem_id for each problem
# @profile
def verify_lean4_proofs(proof_code_list, imports = DEFAULT_IMPORTS, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE): # cpu?
    """
    Spawns the Lean 4 REPL using pexpect, sends commands, and waits for a dict output
    delimited by double newline (\n\n) before sending the next command.
    """
    
    def send_command_and_wait(child, command, env=None, timeout=PROOF_TIMEOUT):
        """
        Send a JSON command to the Lean REPL and wait for the output.
        The REPL output is expected to be a JSON dict (possibly spanning multiple lines)
        ending with a double newline.
        """
        # Build the JSON command
        if env is None:
            json_cmd = json.dumps({"cmd": command})
        else:
            json_cmd = json.dumps({"cmd": command, "env": env})

        # # if the length of cmd is too long, needs to send by chunk
        # if len(json_cmd) < 20:    
        #     # Send the command. The REPL expects a double newline to signal end-of-command.
        #     child.sendline(json_cmd)
        #     child.sendline("")  # This sends the extra newline.
        # else:
        #     begin_length = 0
        #     end_length = 10
        #     while end_length < len(json_cmd):
        #         child.send(json_cmd[begin_length:end_length])
        #         begin_length = end_length
        #         end_length += 10
        #     child.sendline(json_cmd[begin_length:])
        #     child.sendline("")

        child.sendline(json_cmd)
        child.sendline("")  # This sends the extra newline.


        # import pdb; pdb.set_trace()

        code = imports + command
        try:
            # Wait for the output delimiter (double newline)
            child.expect(["\r\n\r\n", "\n\n"], timeout=timeout)
            # pexpect.before contains everything up to the matched delimiter.
            response = child.before.strip()

            block = response
            
            # problem_id = proof_code_list[i]["name"]
            try:
                result = json.loads(block)
                parsed_result = {
                    "sorries": result.get("sorries", []),
                    "tactics": result.get("tactics", []),
                    "errors": [m for m in result.get("messages", []) if m.get("severity") == "error"],
                    "warnings": [m for m in result.get("messages", []) if m.get("severity") == "warning"],
                    "infos": [m for m in result.get("messages", []) if m.get("severity") == "info"],
                    # "verified_code": code,
                    # "problem_id": problem_id
                    "system_errors": None
                }
                parsed_result["pass"] = not parsed_result["errors"]
                parsed_result["complete"] = (
                    parsed_result["pass"]
                    and not parsed_result["sorries"]
                    and not any(
                        "declaration uses 'sorry'" in warning["data"] or "failed" in warning["data"]
                        for warning in parsed_result["warnings"]
                    )
                )

            except json.JSONDecodeError as e:

                parsed_result = {
                    "pass": False,
                    "complete": False,
                    # "verified_code": code,
                    # "problem_id": problem_id,
                    "system_errors": f"JSONDECODE ERROR: {e}"
                }
        
            response = {"code": command, "compilation_result": parsed_result}


            # if "uncaught exception" in response:
            #     response = "UNCAUGHT ERROR: "+ response
        except pexpect.TIMEOUT as e:
            response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"TIMEOUT ERROR: {e}"}}
        except pexpect.EOF as e:
            response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"EOF ERROR: {e}"}}
        except Exception as e:  # Catch any other unexpected errors
            response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"UNEXPECTED ERROR: {e}"}}
        return response



    # start_time = time.time()

    # def initiate_child():
    #     # Start the Lean 4 REPL using pexpect
    #     # Note: Adjust the command if necessary for your setup
    #     cmd = f"{lake_path} exe repl"
    #     child = pexpect.spawn(cmd, cwd=lean_workspace, encoding='utf-8', maxread=1, echo=False)
    #     # Uncomment the next line to see the REPL's output for debugging
    #     # child.logfile = sys.stdout

    #     print(f"Initializing Lean REPL: (PID: {child.pid})", flush = True)

    #     response = send_command_and_wait(child, imports, timeout=IMPORT_TIMEOUT)

    #     # return child

    #     return child, response
    

    def initiate_child():
        # Start the Lean 4 REPL using pexpect
        # Note: Adjust the command if necessary for your setup
        # child = pexpect.spawn('stty -icanon', cwd=lean_workspace, encoding='utf-8', maxread=1, echo=False)

        child = pexpect.spawn(f"/bin/bash", cwd=lean_workspace, encoding='utf-8', maxread=1, echo=False)
        
        # # Uncomment the next line to see the REPL's output for debugging
        # child.logfile = sys.stdout

        child.sendline("stty -icanon")

        child.sendline(f"cd {lean_workspace}")

        child.sendline(f"{lake_path} exe repl")
        
        print(f"Initializing Lean REPL: (PID: {child.pid})", flush = True)

        response = send_command_and_wait(child, imports, timeout=IMPORT_TIMEOUT)


        # return child

        return child, response
    

    # IMPORTS = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

    json_blocks = []

    # child = initiate_child()

    child , _ = initiate_child()
    # print("init response:", response)

    fail = 0
    start_time = time.time()
    for i, proof_code_dict in enumerate(proof_code_list):
        proof_code = proof_code_dict["code"]
        


        # emoty code should be false
        if len(proof_code)==0:



            response = {"code": proof_code, "compilation_result": {"pass": False, "complete": False, "system_errors": None}}

        else:

        # # just for debug: terminal can not input more than 4096. How to fix?
        # if len(proof_code + imports) > 3500:
        #     fail+=1
        #     print("jump one long sample", flush = True)
        #     continue

            # Send the proof code to the REPL and wait for its output.
            response = send_command_and_wait(child, proof_code, env=0, timeout=PROOF_TIMEOUT)

            # if "TIMEOUT" in response:
            # if "ERROR:" in response:
            if response["compilation_result"]["system_errors"] is not None:
                fail += 1   

                if "EOF" in response["compilation_result"]["system_errors"]:

                    # debug
                    print("EOF error:", response["compilation_result"]["system_errors"], flush = True)

                    previous_id = child.pid

                    try:
                        child.close()
                    except Exception:
                        child.terminate(force=True)

                    child , _ = initiate_child()
                    print("EOF restart", previous_id, "replaced with", child.pid, flush = True) 
                else : 
                    previous_id = child.pid
                    try:
                        child.close()
                    except Exception:
                        child.terminate(force=True)
                    child , _ = initiate_child()
                    print("restart because of", response["compilation_result"]["system_errors"], previous_id, "replaced with", child.pid, flush = True) 

        response["name"] = proof_code_list[i]["name"]

        response["verify_time"] = round(time.time() - start_time, 2)

        start_time = time.time()

        json_blocks.append(response)


        # Print progress every several steps
        if (i + 1) % 5 == 0 or (i + 1) == len(proof_code_list):
           
            print(f"PID: {child.pid} - Progress: {i + 1}/{len(proof_code_list)} proofs processed - Failure rate: {fail/(i+1):.2%}", flush=True) 

    try:
        child.close()
    except Exception:
        child.terminate(force=True)


    return json_blocks

# def parallel_verification(problem_list, imports = DEFAULT_IMPORTS, lake_path =DEFAULT_LAKE_PATH, lean_workspace =DEFAULT_LEAN_WORKSPACE):
#     """Launch multiple Lean REPL processes, each handling a different problem on a separate CPU core."""
#     all_results = []

#     processes = []
#     # num_cores = min(len(problem_list), os.cpu_count())  # Limit to available CPU cores
#     result_queue = mp.Queue()

#     for proof_code_list in problem_list:
#         p = mp.Process(target=verify_lean4_proofs, args=(result_queue, proof_code_list, imports, lake_path, lean_workspace))
#         processes.append(p)
#         p.start()
    
#     # Wait for all processes to complete
#     for p in processes:
#         p.join()

#     print("All verification processes completed.")

#     while not result_queue.empty():
#         lean_results = result_queue.get()
#         all_results += lean_results
        
#     return all_results

# @profile
def parallel_verification(problem_list, imports=DEFAULT_IMPORTS, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE):
    """Launch multiple Lean REPL processes using multiprocessing.Pool."""
    
    # len(problem_list) should not be too large compare to num available cpus

    # num_cores = min(len(problem_list), mp.cpu_count())  # Limit to available CPU cores
    
    all_results = []

    num_proc = len(problem_list)

    # Prepare arguments for starmap
    args = [(proof_code_list, imports, lake_path, lean_workspace) for proof_code_list in problem_list]

    # Use multiprocessing Pool to manage worker processes
    with mp.Pool(processes = num_proc) as pool:
        results = pool.starmap(verify_lean4_proofs, args)  # Distribute tasks across cores
    
    # Combine all results
    for result in results:
        all_results += result  # Merge lists

    # for arg in args:
    #     results = verify_lean4_proofs(*arg)
    #     all_results += results

    print("All verification processes completed.", flush = True)
    return all_results

# print(verify_lean4_proofs(statement_sample,proof_code_list_sample))


# print(verify_lean4_proofs(proof_code_list_sample))

if __name__ == '__main__':
    # print(os.cpu_count())

    # output_dir="/scratch/gpfs/st3812/aiformath/Deepseek/eval_results/minif2f/Goedel-Prover-SFT_long_form_thought_data_5k_Epoch2_LR1e-5"

    # input_file = output_dir + "/to_inference_codes.json"


    # compile_output_path=output_dir+ "/code_compilation_repl2.json"


    print(parallel_verification(problem_list_sample))


    # with open(input_file, 'r') as json_file:
    #     codes = json.load(json_file)

    #     codes = codes[:800]
    #     # remove imports

    #     imports = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n"

    #     for code in codes:
    #         code["code"] = code["code"][len(imports):]

    #     to_compile_problems_list= split_list_randomly(codes, 16)

    #     to_compile_problems_list = [to_compile_problems_list[0]] * 16

    #     outputs_list = parallel_verification(to_compile_problems_list)


    # with open(compile_output_path, 'w') as json_file:
    #     json.dump(outputs_list, json_file, indent=4)

    # print("time:",time.time()-starttime)