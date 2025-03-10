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

DEFAULT_LAKE_PATH = f'{HOME_DIR}/.elan/bin/lake'

DEFAULT_LEAN_WORKSPACE = 'mathlib4/'

# DEFAULT_LEAN_WORKSPACE = '/scratch/gpfs/CHIJ/Shange/Deepseek/mathlib4'

IMPORT_TIMEOUT = 300
# PROOF_TIMEOUT = 100
PROOF_TIMEOUT = 300
MAXHEARTBEATS = 500_000
# COUNTHEARTBEATS = False

# DEFAULT_IMPORTS = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

DEFAULT_IMPORTS = f"import Mathlib\nimport Aesop\nopen BigOperators Real Nat Topology Rat\n\n"







statement_sample = "\n/-- Show that $\frac{9x^2\\sin^2 x + 4}{x\\sin x} \\geq 12$ for $0 < x < \\pi$.-/\ntheorem aime_1983_p9 (x : ℝ) (h₀ : 0 < x ∧ x < Real.pi) :\n  12 ≤ (9 * (x ^ 2 * Real.sin x ^ 2) + 4) / (x * Real.sin x) :="

proof_code_sample_1 = " by\n /-\n  To find the minimum value of $\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$, we need to show that it is at least 12. We start by noting that the expression can be rewritten using the division property of inequalities. We then use the fact that \\$sin x$ and $x$ are positive in the given range to establish the necessary inequalities. Finally, we apply these results to conclude that the minimum value is indeed 12.\n  -/\n  -- We start by ensuring that the product x * sin x is positive in the given range.\n  have h₁ : 0 < x * Real.sin x := by\n    apply mul_pos\n    -- x is positive in the range (0, π).\n    exact h₀.1\n    -- sin x is positive in the range (0, π).\n    exact Real.sin_pos_of_pos_of_lt_pi h₀.1 h₀.2\n  -- Using the division property of inequalities, we rewrite the expression.\n  rw [le_div_iff h₁]\n  /- tactic state:\n    x : ℝ\n    h₀ : 0 < x ∧ x < π\n    h₁ : 0 < x * x.sin\n    ⊢ 12 * (x * x.sin) ≤ 9 * (x ^ 2 * x.sin ^ 2) + 4\n  -/\n  -- This is equivalent to showing that 9x^2 sin^2 x - 12x sin x + 4 ≥ 0, and the left hand side can be rewritten as a perfect square (3x sin x - 2)^2.\n  -- We use the fact that (3x sin x - 2)^2 is non-negative to establish this.\n  nlinarith [sq_nonneg (3 * x * Real.sin x - 2)]\n"

proof_code_sample_2 = " by sorry"

proof_code_sample_3 = "\n/-- For a series $\\{a_n\\}$, we have $\\sum_{n=0}^{99} a_{n+1}^2 = 1$. Show that $\\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \\frac{12}{25}$.-/\ntheorem imosl_2007_algebra_p6 (a : \u2115 \u2192 NNReal) (h\u2080 : (\u2211 x in Finset.range 100, a (x + 1) ^ 2) = 1) :\n    (\u2211 x in Finset.range 99, a (x + 1) ^ 2 * a (x + 2)) + a 100 ^ 2 * a 1 < 12 / 25 := by\n  /-\n  Given a series \\(\\{a_n\\}\\), we know that \\(\\sum_{n=0}^{99} a_{n+1}^2 = 1\\). We need to show that \\(\\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \\frac{12}{25}\\).\n  -/\n  -- Simplify the given sum condition using basic arithmetic properties.\n  simp_all [Finset.sum_range_succ, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc,\n    add_left_comm, add_comm]\n  -- Use linear arithmetic to prove the inequality.\n  <;> nlinarith [h\u2080]"

proof_code_sample_4 = "BUG" * 4096

proof_code_sample_5 = DEFAULT_IMPORTS


# proof_code_list_sample = [proof_code_sample] * 1
# proof_code_list_sample = [statement_sample + proof_code_sample_1, statement_sample + proof_code_sample_2] * 2

# proof_code_list_sample = ([{"name": "test_problem", "code": statement_sample + proof_code_sample_1}] + [{"name": "test_problem", "code": statement_sample + proof_code_sample_2}]) * 1

proof_code_list_sample = [{"name": "test_problem", "code": statement_sample + proof_code_sample_1}] * 1


# proof_code_list_sample.append({'name': 'timeout_problem', 'code': proof_code_sample_3})
# proof_code_list_sample.append({'name': 'timeout_problem', 'code': proof_code_sample_5})

problem_list_sample = [proof_code_list_sample] * 1 #each item in problem_list_sample is a proof_code_list which I want a single process to do



def initiate_child(timeout=IMPORT_TIMEOUT, max_heartbeats=MAXHEARTBEATS):
    # Start the Lean 4 REPL using pexpect
    # Note: Adjust the command if necessary for your setup
    # child = pexpect.spawn('stty -icanon', cwd=lean_workspace, encoding='utf-8', maxread=1, echo=False)

    child = pexpect.spawn(f"/bin/bash", cwd=DEFAULT_LEAN_WORKSPACE, encoding='utf-8', maxread=1, echo=False)
    
    # # Uncomment the next line to see the REPL's output for debugging
    # child.logfile = sys.stdout

    child.sendline("stty -icanon")

    child.sendline(f"cd {DEFAULT_LEAN_WORKSPACE}")

    child.sendline(f"{DEFAULT_LAKE_PATH} exe repl")

    imports = DEFAULT_IMPORTS + f"set_option maxHeartbeats {max_heartbeats}\n\n"

    response = send_command_and_wait(child, imports, timeout=timeout)

    # print(f"Initializing Lean REPL: (PID: {child.pid})", flush = True)
    # return child

    return child, response

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

    child.sendline(json_cmd)
    child.sendline("")  # This sends the extra newline.


    # import pdb; pdb.set_trace()

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


    except pexpect.TIMEOUT as e:
        response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"TIMEOUT ERROR: {e}"}}
    except pexpect.EOF as e:
        response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"EOF ERROR: {e}"}}
    except Exception as e:  # Catch any other unexpected errors
        response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"UNEXPECTED ERROR: {e}"}}
    return response

def worker(worker_id, task_queue, result_list, total_restarts, lock, import_timeout=IMPORT_TIMEOUT, proof_timeout=PROOF_TIMEOUT, max_heartbeats=MAXHEARTBEATS):
    """Worker function that continuously picks tasks and executes them."""
    child, _ = initiate_child(timeout=import_timeout, max_heartbeats=max_heartbeats)  # Start Lean 4 REPL
    print(f"Worker {worker_id} started Lean REPL.", flush = True)

    start_time = time.time()

    while True:
        try:
            proof_code_dict = task_queue.get(timeout=10)

            proof_code = proof_code_dict["code"]
            proof_name = proof_code_dict["name"]
            # proof_id, proof_command = task_queue.get(timeout=10)  # Get task
        except mp.queues.Empty:
            break  # Exit if no tasks are left


        if len(proof_code)==0:


            response = {"code": proof_code, "compilation_result": {"pass": False, "complete": False, "system_errors": None}}

            response["name"] = proof_name

            response["verify_time"] = round(time.time() - start_time, 2)

            start_time = time.time()

            with lock:
                result_list.append(response)

        else:
            # When COUNTHEARTBEATS is True, insert #count_heartbeats inside the proof's tactic block
            # if COUNTHEARTBEATS:
            #     # Split the proof code to insert #count_heartbeats after the := by
            #     parts = proof_code.split(':= by', 1)
            #     if len(parts) == 2:
            #         proof_code = parts[0] + ':= by\n  #count_heartbeats' + parts[1]
            #     else:
            #         # Fallback if splitting fails (shouldn't happen with valid proofs)
            #         proof_code = '\n#count_heartbeats in\n' + proof_code
            #     response = send_command_and_wait(child, proof_code, env=0)
            response = send_command_and_wait(child, proof_code, env=0, timeout=proof_timeout)


            response["name"] = proof_name

            response["verify_time"] = round(time.time() - start_time, 2)

            start_time = time.time()

            with lock:
                result_list.append(response)

            if response["compilation_result"]["system_errors"] is not None:


                with total_restarts.get_lock():  # Ensure atomic update
                    total_restarts.value += 1  # Increment total restart count 

                if "EOF" in response["compilation_result"]["system_errors"]:

                    # # debug
                    # print("EOF error:", response["compilation_result"]["system_errors"], flush = True)

                    previous_id = child.pid

                    try:
                        child.close()
                    except Exception:
                        child.terminate(force=True)

                    # with total_restarts.get_lock():  # Ensure atomic update
                    #     total_restarts.value += 1  # Increment total restart count  

                    if task_queue.empty():
                        print(f"Worker {worker_id}: No more proofs left. Not restarting REPL.", flush=True)
                        break  # Exit instead of restarting
                    else:
                        child , _ = initiate_child(timeout=import_timeout, max_heartbeats=max_heartbeats)

                    # print("EOF restart", previous_id, "replaced with", child.pid, flush = True) 
                else : 
                    previous_id = child.pid
                    try:
                        child.close()
                    except Exception:
                        child.terminate(force=True)

                    if task_queue.empty():
                        print(f"Worker {worker_id}: No more proofs left. Not restarting REPL.", flush=True)

                        break  # Exit instead of restarting
                    else:
                        child , _ = initiate_child(timeout=import_timeout, max_heartbeats=max_heartbeats)

                    # print("restart because of", response["compilation_result"]["system_errors"], previous_id, "replaced with", child.pid, flush = True) 
                    # print("Timemout restart", previous_id, "replaced with", child.pid, flush = True) 


    try:
        child.close()
    except Exception:
        child.terminate(force=True)
    print(f"Worker {worker_id} terminated Lean REPL.", flush = True)
    




def scheduler(proofs, num_workers=64, import_timeout=IMPORT_TIMEOUT, proof_timeout=PROOF_TIMEOUT, max_heartbeats=MAXHEARTBEATS):
    print(f"Starting scheduler with import_timeout {import_timeout} proof_timeout {proof_timeout} max_heartbeats {max_heartbeats}", flush = True)

    start_time = time.time()

    # proofs is a list of all the proofs that need to verify

    """Scheduler function that launches REPL processes and assigns tasks to CPUs."""
    task_queue = mp.Queue()
    result_queue = mp.Queue()
    total_restarts = mp.Value('i', 0)  # Shared counter for total REPL restarts


    manager = mp.Manager()
    result_list = manager.list()  #  Shared list
    lock = manager.Lock()  #  Lock for thread safety

    # Populate the task queue
    for proof in proofs:
        task_queue.put(proof)

    # Start worker processes
    workers = []
    for i in range(num_workers):
        process = mp.Process(target=worker, args=(i, task_queue, result_list, total_restarts, lock, import_timeout, proof_timeout, max_heartbeats))
        process.start()
        workers.append(process)




    # Monitor progress while workers are running
    total_proofs = len(proofs)
    while any(worker.is_alive() for worker in workers):  # While workers are active
        time.sleep(10)  #  Check progress every 10 seconds
        print(f"Progress: {len(result_list)}/{total_proofs} proofs processed. REPL errors: {total_restarts.value}", flush=True)


    # Wait for all processes to finish
    for process in workers:
        # process.join(timeout=60)
        process.join()

    task_queue.close()
    task_queue.join_thread()

    # Calculate total duration
    end_time = time.time()
    total_duration = end_time - start_time

    print(f"All proofs processed! Total REPL Errors: {total_restarts.value} Total execution time: {total_duration/60:.2f} mins", flush = True)

    # print(results, flush = True)

    return list(result_list)






if __name__ == '__main__':


    print(scheduler(proof_code_list_sample, num_workers=1))