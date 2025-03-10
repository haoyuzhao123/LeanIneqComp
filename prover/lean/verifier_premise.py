import os
import time
import json
import ctypes
import resource
import tempfile
import traceback
import threading
import subprocess
import multiprocessing as mp
from pprint import pprint

import numpy as np

from prover.lean.ast_parser import lean4_parser
from prover.workers import ProcessScheduler
from prover.utils import AttrDict


# HOME_DIR = os.path.expanduser('~')
DEFAULT_LAKE_PATH = f'/scratch/gpfs/st3812/.elan/bin/lake'
DEFAULT_LEAN_WORKSPACE = 'mathlib4/'


def verify_lean4_file(code, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, timeout=300, allTactics=False, ast=False, premises=False, tactics=False):
    command = dict(cmd=code, allTactics=allTactics, ast=ast, tactics=tactics, premises=premises)
    if last_env is not None:
        command.update(env=last_env)
    message_str = json.dumps(command, ensure_ascii=False)
    if verbose:
        print(message_str)
    start_time = time.time()
    system_messages = ''
    try:
        with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as temp_file:
            temp_file.write(message_str + "\r\n\r\n")
            temp_file.seek(0)
            outputs = subprocess.run([lake_path, "exe", 'repl'], stdin=temp_file, capture_output=True, text=True, cwd=lean_workspace, timeout=timeout)
        result = json.loads(outputs.stdout)
        ast_results = lean4_parser(code, result['ast']) if 'ast' in result and result['ast'] else {}
        result = {
            "sorries" : result.get('sorries', []), 
            "tactics" : result.get('tactics', []),
            "errors" : [m for m in result.get('messages', []) if m['severity'] == 'error'],
            "warnings" : [m for m in result.get('messages', []) if m['severity'] == 'warning'],
            "infos" : [m for m in result.get('messages', []) if m['severity'] == 'info'],
            "system_messages" : system_messages,
            "system_errors" : None,
            "ast" : ast_results,
            "verified_code" : code,
        }
        result['pass'] = not result['errors']
        result['complete'] = result['pass'] and not result['sorries'] and not any("declaration uses 'sorry'" in warning['data'] or 'failed' in warning['data'] for warning in result['warnings'])
    except:
        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc(),
            "system_messages": system_messages
        }
    result['verify_time'] = time.time() - start_time
    return result

#######################################################
#     Merge code from STP repo
#######################################################

def extract_invokes(ast_results):
    premises = ast_results.get('premises', [])
    invokes = set()
    for premise in premises:
        invokes.add(premise['fullName'])
    return list(invokes)

def get_result_from_repl(repl_result, code, start_time):
    result = {
        "sorries" : repl_result.get('sorries', []), 
        "tactics" : repl_result.get('tactics', []),
        "errors" : [m for m in repl_result.get('messages', []) if m['severity'] == 'error'],
        "warnings" : [m for m in repl_result.get('messages', []) if m['severity'] == 'warning'],
        "infos" : [m for m in repl_result.get('messages', []) if m['severity'] == 'info'],
        "verified_code" : code,
    }
    result['pass'] = not result['errors']
    result['complete'] = result['pass'] and not result['sorries'] and not any("declaration uses 'sorry'" in warning['data'] or 'failed' in warning['data'] for warning in result['warnings'])
    if result['complete']:
        ast_results = lean4_parser(code, repl_result['ast']) if 'ast' in repl_result and repl_result['ast'] else {}
        result['invokes'] = extract_invokes(ast_results)
        #if __DEBUG__:
        #    result['ast'] = ast_results
    result['verify_time'] = time.time() - start_time
    return result

def verify_lean4_file_premises(code, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, 
                      timeout=300, allTactics=False, ast=False, premises=False, tactics=False):
    command = dict(cmd=code, allTactics=allTactics, ast=ast, tactics=tactics, premises=premises)
    if last_env is not None:
        command.update(env=last_env)

    message_str = json.dumps(command, ensure_ascii=False)
    if verbose:
        print(message_str)
    start_time = time.time()
    
    results = []
    try:
        with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as temp_file:
            temp_file.write(message_str + "\r\n\r\n")
            temp_file.seek(0)
            outputs = subprocess.run([lake_path, "exe", 'repl'], stdin=temp_file, capture_output=True, text=True, cwd=lean_workspace, timeout=timeout)

        repl_result = json.loads(outputs.stdout)
        result = get_result_from_repl(repl_result, code, start_time)
        return result
    except Exception as e:
        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc()
        }
        return result

#######################################################
#     End of merging code from STP repo
#######################################################

class Lean4ServerProcess(mp.Process):
    def __init__(self, idx, task_queue, request_statuses, lock, extra_args=AttrDict()):
        super().__init__()
        self.idx = idx
        self.task_queue = task_queue
        self.request_statuses = request_statuses
        self.lock = lock
        self.extra_args = extra_args

        self.timeout = extra_args.get('timeout', 300)
        self.memory_limit = extra_args.get('memory_limit', -1)
        self.last_output_time = mp.Value(ctypes.c_double, time.time())
        self.complete_count = mp.Value(ctypes.c_int, 0)
    
    def run(self):
        if self.memory_limit > 0:
            resource.setrlimit(
                resource.RLIMIT_AS,
                (self.memory_limit * (1000 ** 3), self.memory_limit * (1000 ** 3))
            )
        while True:
            inputs = self.task_queue.get()
            if inputs is None: # Terminate when receiving None
                break
            for _, request_id, task in inputs:
                if isinstance(task, str):
                    task = dict(code=task)
                if 'timeout' not in task:
                    task['timeout'] = self.timeout
                result = verify_lean4_file(**task)
                if len(result['system_messages']) > 0:
                    retry_start_time = time.time()
                    while ('lean::exception: failed to create thread' in result['system_messages'] or
                           'std::bad_alloc: std::bad_alloc' in result['system_messages'] or
                           'Cannot allocate memory' in result['system_messages']) \
                          and time.time() - retry_start_time < self.timeout:
                        time.sleep(0.1)
                        result = verify_lean4_file(**task)

                ##########################
                # Start collect premises
                ##########################
                result["pass_compile"] = True
                if result.get('complete', False):
                    result["pass_complete"] = True
                    task['premises'] = True
                    task['ast'] = True
                    result = verify_lean4_file_premises(**task)
                    result["pass_premise"] = True


                with self.lock:
                    self.request_statuses[request_id] = result
                    self.last_output_time.value = time.time()
                    self.complete_count.value += 1


class Lean4ServerScheduler(ProcessScheduler):
    def __init__(self, max_concurrent_requests=64, timeout=300, memory_limit=-1, name='verifier'):
        super().__init__(batch_size=1, name=name)
        print("test code")
        self.processes = [
            Lean4ServerProcess(
                idx=idx,
                task_queue=self.task_queue,
                request_statuses=self.request_statuses,
                lock=self.lock,
                extra_args=AttrDict(
                    timeout=timeout,
                    memory_limit=memory_limit,
                )
            )
            for idx in range(max_concurrent_requests)
        ]
        for p in self.processes:
            p.start()
        print(f'Complete launching {len(self.processes)} LeanServerProcesses')

        self.timeout = timeout
        self._running_monitor = mp.Value(ctypes.c_bool, True)
        self._last_complete_count = mp.Value(ctypes.c_int, 0)
        self._monitor_process = mp.Process(target=self._monitor)
        self._monitor_process.start()
    
    def _monitor(self):
        while self._running_monitor.value:
            time.sleep(1.0)
            subprocess.run(['killall', 'repl', f'--older-than={int(self.timeout) + 10}s'], capture_output=True)
    
    def close(self):
        super().close()
        for p in self.processes:
            p.join()
        self._running_monitor.value = False
        self._monitor_process.join()
        print(f'All {len(self.processes)} LeanServerProcesses stopped')


if __name__ == '__main__':
    #code = open('mathlib4/.lake/packages/REPL/test/aime_1983_p9.code.in').read()
    code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Suppose $a, b, c$ are the sides of a triangle. Prove that \n\n$a^2(b+c-a)+b^2(c+a-b)+c^2(a+b-c)\\le{3abc}.$-/\ntheorem imo_1964_p2 (a b c : \u211d) (h\u2080 : 0 < a \u2227 0 < b \u2227 0 < c) (h\u2081 : c < a + b) (h\u2082 : b < a + c)\n    (h\u2083 : a < b + c) :\n    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) \u2264 3 * a * b * c := by\n  /-\n  To prove the inequality \\(a^2(b+c-a) + b^2(c+a-b) + c^2(a+b-c) \\leq 3abc\\) for the sides \\(a, b, c\\) of a triangle, we can use the non-negativity of squares and some algebraic manipulations. Specifically, we will use the fact that the square of any real number is non-negative, and then apply these properties to the differences \\(a - b\\), \\(b - c\\), and \\(c - a\\). By leveraging these non-negative terms, we can derive the desired inequality.\n  -/\n  -- Use the non-negativity of squares to derive the inequality.\n  -- Specifically, we use the fact that the square of any real number is non-negative.\n  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),\n    sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b), pow_two_nonneg (a + c)]"
    code = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- The volume of a cone is given by the formula $V = \\frac{1}{3}Bh$, where $B$ is the area of the base and $h$ is the height. The area of the base of a cone is 30 square units, and its height is 6.5 units. What is the number of cubic units in its volume? Show that it is 65.-/\ntheorem mathd_algebra_478 (b h v : \u211d) (h\u2080 : 0 < b \u2227 0 < h \u2227 0 < v) (h\u2081 : v = 1 / 3 * (b * h))\n    (h\u2082 : b = 30) (h\u2083 : h = 13 / 2) : v = 65 := by\n  /-\n  To find the volume \\( V \\) of a cone using the formula \\( V = \\frac{1}{3}Bh \\), where \\( B \\) is the area of the base and \\( h \\) is the height, we proceed as follows:\n  1. Substitute the given values \\( B = 30 \\) square units and \\( h = 6.5 \\) units into the volume formula.\n  2. Simplify the expression step by step.\n  3. Verify that the resulting volume matches the expected value of 65 cubic units.\n  -/\n  -- Substitute the given values for b and h into the volume formula.\n  subst h\u2082\n  subst h\u2083\n  -- Simplify the expression using the given values and properties.\n  simp_all only [mul_one, mul_div_cancel_left, one_mul, mul_comm, pow_one, pow_two]\n  -- Normalize the numerical expression to verify the result.\n  norm_num"


    code = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- For any integer \( n \geq 1 \), prove that 
\[
\sum_{k=1}^n k^2 \leq \left( \sum_{k=1}^n k \right)^2.
\]
-/
theorem sum_of_squares_leq_square_of_sum (n : ℕ) (h : 1 ≤ n) :
    ∑ k in Finset.range n, (k + 1) ^ 2 ≤ (∑ k in Finset.range n, (k + 1)) ^ 2 := by
  /-
  We aim to prove that the sum of squares of the first \( n \) positive integers is less than or equal to the square of the sum of the first \( n \) positive integers. The proof uses the non-negativity of squares and the properties of powers (specifically `pow_succ`).

  The key idea is to expand the square of the sum and compare it term-by-term with the sum of squares. The non-negativity of squares ensures that the cross terms are non-negative, which helps in establishing the inequality.
  -/
  -- First, express the sum of squares and the square of the sum.
  have sum_squares : ∑ k in Finset.range n, (k + 1) ^ 2 = ∑ k in Finset.range n, (k^2 + 2*k + 1) := by
    simp [pow_succ, add_pow]
  have square_sum : (∑ k in Finset.range n, (k + 1)) ^ 2 = (∑ k in Finset.range n, (k + 1)) * (∑ k in Finset.range n, (k + 1)) := by
    simp [pow_succ]
  
  -- Expand the square of the sum.
  have expanded_square : (∑ k in Finset.range n, (k + 1)) ^ 2 = ∑ k in Finset.range n, (k + 1)^2 + 2 * ∑ i in Finset.range n, ∑ j in Finset.range i, (i + 1) * (j + 1) := by
    simp [pow_succ, Finset.sum_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp [mul_add, add_mul, mul_comm, mul_assoc]
  
  -- The cross terms are non-negative due to the non-negativity of squares.
  have cross_terms_nonneg : 0 ≤ ∑ i in Finset.range n, ∑ j in Finset.range i, (i + 1) * (j + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (Nat.cast_nonneg (i + 1)) (Nat.cast_nonneg (j + 1))
  
  -- Combine the results to prove the inequality.
  rw [sum_squares, expanded_square]
  apply add_le_add_left
  exact mul_nonneg (by norm_num) cross_terms_nonneg
"""

    lean4_scheduler = Lean4ServerScheduler(max_concurrent_requests=1, timeout=300, memory_limit=10, name='verifier')
    request_id_list = lean4_scheduler.submit_all_request([dict(code=code, ast=True, tactics=True)])
    outputs_list = lean4_scheduler.get_all_request_outputs(request_id_list)
    lean4_scheduler.close()
    pprint(outputs_list)
