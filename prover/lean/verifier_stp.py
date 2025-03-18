import os
import sys
import time
import json
import pickle
import psutil
import ctypes
import resource
import tempfile
import traceback
import signal
import threading
import subprocess
import multiprocessing as mp
from multiprocessing import Process, Event
from pprint import pprint
import numpy as np
from typing import List
import ray
from ray.util import placement_group, remove_placement_group, ActorPool
from tqdm.auto import tqdm
from utils.prover.lean.ast_parser import lean4_parser
from utils.gcloud_utils import read_file, write_data, move_file, execute_on_all_workers
from func_timeout import FunctionTimedOut, func_set_timeout

__DEBUG__ = os.getenv("DEBUG", 'False').lower() in ('true', '1', 't')
HOME_DIR = os.path.expanduser('~')
DEFAULT_LAKE_PATH = f'{HOME_DIR}/.elan/bin/lake'
DEFAULT_LEAN_WORKSPACE = f'{HOME_DIR}/lean/mathlib4/'
MEMORY_USAGE_THRESHOLD = 15
DEFAULT_TIMEOUT = 200
LEAN_HEADER = 'import miniF2F\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n'
TEST_BATCH_SIZE = 40

MEMORY_THRESHOLD = 75.0  # Memory usage percentage to trigger waiting

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
        if __DEBUG__:
            result['ast'] = ast_results
    result['verify_time'] = time.time() - start_time
    return result

def read_from_repl(proc):
    ret = ''
    while True:
        line = proc.stdout.readline()
        if len(line.strip()) == 0:
            break
        ret += line
    return ret

@func_set_timeout(DEFAULT_TIMEOUT, allowOverride=True)
def query_repl(proc, message_str):
    proc.stdin.write(message_str)
    proc.stdin.flush()
    return read_from_repl(proc)

@func_set_timeout(DEFAULT_TIMEOUT + 10, allowOverride=True)
def _start_repl_process(lake_path, lean_workspace, header = None):
    proc = subprocess.Popen([lake_path, "exe", 'repl'], 
                                    stdin=subprocess.PIPE,
                                    stdout=subprocess.PIPE, 
                                    stderr=subprocess.PIPE,  # Capture stderr
                                    text=True, 
                                    cwd=lean_workspace,)
    cmd = json.dumps({"cmd": header or LEAN_HEADER, "allTactics": False, "ast": False, "tactics": False, "premises": False}, ensure_ascii=False) + '\r\n\r\n'
    query_repl(proc, cmd)
    return proc

def start_repl_process(lake_path, lean_workspace, header = None):
    # Retry if the process is not started
    for i in range(5):
        try:
            return _start_repl_process(lake_path, lean_workspace, header)
        except Exception as e:
            if __DEBUG__:
                print(f"Error in starting Lean4 process: {e}")
            time.sleep(i + 1)
            continue
    raise Exception("Failed to start Lean4 process")

@func_set_timeout(DEFAULT_TIMEOUT, allowOverride=True)
def terminate_repl(proc):
    if proc is None:
        return
    
    try:
        # Create a psutil Process instance for the main process
        parent = psutil.Process(proc.pid)
        
        # Retrieve all child processes recursively
        children = parent.children(recursive=True)
        
        # Terminate all child processes
        for child in children:
            child.terminate()
        
        # Terminate the main process
        parent.terminate()
        
        # Wait for all processes to terminate gracefully
        gone, alive = psutil.wait_procs([parent] + children, timeout=5)
        
        # Force kill any processes that are still alive after the timeout
        for p in alive:
            p.kill()
            
    except psutil.NoSuchProcess:
        # The process may have already terminated
        pass
    except Exception as e:
        # Optionally log the exception if needed
        # print(f"Error in terminating processes: {e}")
        pass

def verify_lean4_file(codes, headers, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, 
                      allTactics=False, ast=False, premises=False, tactics=False):
    command = dict(allTactics=allTactics, ast=ast, tactics=tactics, premises=premises)
    
    results = []
    try:
        proc = None
        last_header = None
        for code, header in zip(codes, headers):
            if proc is None or header != last_header:
                terminate_repl(proc)
                proc = start_repl_process(lake_path, lean_workspace, header)
                last_header = header
            
            message_str = json.dumps(command | {'cmd': code, 'env': 0}, ensure_ascii=False) + '\r\n\r\n'
            try:
                start_time = time.time()
                output = query_repl(proc, message_str)
                repl_result = json.loads(output)
                result = get_result_from_repl(repl_result, code, start_time)
                results.append(result)
            except (Exception, FunctionTimedOut) as e:
                if __DEBUG__:
                    print(e)
                results.append({"system_messages": str(e), 'complete': False})
                terminate_repl(proc)
                proc = None

        terminate_repl(proc)
    except (Exception, FunctionTimedOut) as e:
        if __DEBUG__:
            print(e)
        results += [{"system_messages": str(e)}] * (len(codes) - len(results))

    assert len(results) == len(codes), f"Results length mismatch: {len(results)} != {len(codes)}"
    return results

def verify_lean4_file_premises(code, header, lake_path=DEFAULT_LAKE_PATH, lean_workspace=DEFAULT_LEAN_WORKSPACE, last_env=None, verbose=False, 
                      timeout=DEFAULT_TIMEOUT, allTactics=False, ast=False, premises=False, tactics=False):
    command = dict(allTactics=allTactics, ast=ast, tactics=tactics, premises=premises)
    if last_env is not None:
        command.update(env=last_env)

    message_str = json.dumps(command | {'cmd': (header or LEAN_HEADER) + code}, ensure_ascii=False) + '\r\n\r\n'
    if verbose:
        print(message_str)
    start_time = time.time()
    
    results = []
    try:
        with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as temp_file:
            temp_file.write(message_str + "\r\n\r\n")
            temp_file.seek(0)
            outputs = subprocess.run([lake_path, "exe", 'repl'], 
                                     stdin=temp_file, 
                                     capture_output=True, 
                                     text=True, 
                                     cwd=lean_workspace, 
                                     timeout=timeout,)

        repl_result = json.loads(outputs.stdout)
        result = get_result_from_repl(repl_result, code, start_time)
        results.append(result)
        return results
    except Exception as e:
        if __DEBUG__:
            print(e)
        return [{"system_messages": str(e), 'complete': False}]

@ray.remote(num_cpus=1)
class Lean4Worker():
    def __init__(self, node, idx, collect_premises = True, timeout=DEFAULT_TIMEOUT):
        super().__init__()
        self.node = node
        self.idx = idx

        self.timeout = timeout
        self.last_output_time = time.time()
        self.complete_count = 0
        self.collect_premises = collect_premises

        if idx == 0:
            _monitor_process = mp.Process(target=self._monitor)
            _monitor_process.start()
            self.monitor_pid = _monitor_process.pid

        time.sleep(idx * 0.1)
        print(f'Lean4Worker id={self.idx} node={self.node} started.')
    
    def run(self, inputs, batched = True):
        # If (memory > threshold), wait until we have enough memory
        while psutil.virtual_memory().percent > MEMORY_THRESHOLD:
            print(f'Lean4Worker id={self.idx} node={self.node} waiting for memory...')
            time.sleep(5)

        if batched:
            tasks = dict(codes=[test_info['statement'] + '\n' + test_info['proof'] for test_info in inputs],
                        headers=[test_info.get('header', None) for test_info in inputs],
                        premises=False,
                        ast=False,
                        last_env=0)
            results = verify_lean4_file(**tasks)

            # get premises
            if self.collect_premises:
                for i, (test_info, result) in enumerate(zip(inputs, results)):
                    if result.get('complete', False):
                        task = dict(code=test_info['statement'] + '\n' + test_info['proof'],
                                    header=test_info.get('header', None),
                                    premises=True,
                                    ast=True,
                                    timeout=DEFAULT_TIMEOUT)
                        result = verify_lean4_file_premises(**task)
                        results[i] = result[0]
        else:
            assert len(inputs) == 1, "Single input only for premises mode"
            test_info = inputs[0]
            tasks = dict(code=test_info['statement'] + '\n' + test_info['proof'],
                        header=test_info.get('header', None),
                        premises=True,
                        ast=True,
                        timeout=DEFAULT_TIMEOUT)
            results = verify_lean4_file_premises(**tasks)

        outputs = []
        for test_info, result in zip(inputs, results):
            outputs.append(test_info | result)
            self.last_output_time = time.time()
            self.complete_count += 1

        return outputs
    
    def _monitor(self):
        while True:
            time.sleep(1.0)

            if psutil.virtual_memory().percent > 90.0:
                print(f'Node {self.node} memory usage too high...')
                subprocess.run(['killall', 'python'], capture_output=True)
                subprocess.run(['killall', 'repl'], capture_output=True)
                subprocess.run(['killall', 'lake'], capture_output=True)
            
            # Fetch all processes
            for process in psutil.process_iter(['pid', 'name', 'memory_info']):
                try:
                    if 'repl' in process.info['name']:
                        # Convert memory usage to GB
                        memory_usage_gb = process.info['memory_info'].rss / (1024 ** 3)
                        if memory_usage_gb > MEMORY_USAGE_THRESHOLD:  # Memory usage threshold
                            process.terminate()
                except (Exception, psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess) as e:
                    # print if there is an exception
                    print(f'Error in monitoring process: {e}')
                    continue
            subprocess.run(['killall', 'repl', f'--older-than={int(self.timeout) + 10}s'], capture_output=True)

def create_ray_lean4_actors(
        reserved_cpus: int = 0, 
        cpus_per_task: float = 4,
        **kwargs,
) -> List:
    import socket
    from ray._raylet import PlacementGroupID
    from ray._private.utils import hex_to_binary
    from ray.util.placement_group import PlacementGroup
    for pg_id_str in ray.util.placement_group_table():
        pg_id_bin = PlacementGroupID(hex_to_binary(pg_id_str))
        pg = PlacementGroup(pg_id_bin)
        remove_placement_group(pg)

    head_ip = socket.gethostbyname(socket.gethostname())
    print('Creating ray actors...')
    ray_workers = []
    
    for i, node in enumerate(ray.nodes()):
        ip = node['NodeManagerAddress']
        nr_cpus = int(node['Resources']['CPU']) - reserved_cpus
        nr_local_workers = int(nr_cpus / cpus_per_task)

        if ip == head_ip:
            continue

        print(f'Creating {nr_local_workers} workers on node {ip}, host name {node["NodeManagerHostname"]}')
        pg = placement_group([{"CPU": nr_local_workers * cpus_per_task,
                               "node:" + ip: 0.1}], strategy="STRICT_PACK")
        ray.get(pg.ready())

        for j in range(nr_local_workers):
            worker = Lean4Worker.options(
                placement_group=pg,
            ).remote(i, j, **kwargs)
            ray_workers.append(worker)

    print(f'Ray actors created. Number of workers: {len(ray_workers)}')

    print('Initializing Lean4 environment...')
    execute_on_all_workers('source ~/.profile; cd ~/lean/mathlib4; find .lake/build/ -type f -exec cat {} + > /dev/null; lake exec repl < ~/lean/mathlib4/.lake/packages/REPL/test/aime_1983_p9.in > ~/lean/mathlib4/.lake/packages/REPL/test/aime_1983_p9.out;',
                           expect_succ=True)
    print('Lean4 environment initialized.')
    return ray_workers

def save_result(valid_proofs: List, file_path: str):
    file_path_tmp = file_path + '_backup'
    write_data(pickle.dumps(valid_proofs), file_path_tmp, 'pickle')
    move_file(file_path_tmp + '.gz', file_path + '.gz')

def monitor_results(pool, nr_batches, total_size, test_results, save_file, identifier_key='local id', early_stop_threshold=0):
    if nr_batches == 0:
        return
    save_interval = 600  # Time interval in seconds (600 seconds = 10 minutes)
    last_save_time = time.time()
    pbar = tqdm(total=total_size, file=sys.stdout)
    nr_tests_done = mp.Value('i', 0)  # Shared value for subprocesses
    nr_tasks_done = mp.Value('i', 0)  # Shared value for subprocesses
    nr_tests_correct = mp.Value('i', 0)  # Shared value for subprocesses

    # Function to update pbar periodically
    stop_event = Event()
    def update_pbar(nr_tasks_done, nr_tests_done, stop_event):
        pbar_n = nr_tests_done.value
        while not stop_event.is_set():
            cpu_usage = psutil.cpu_percent(interval=1)
            memory_usage = psutil.virtual_memory().percent
            remaining = nr_batches - nr_tasks_done.value
            pbar.set_postfix(cpu=f'{cpu_usage}%', mem=f'{memory_usage}%', remaining=f'{int(remaining)}', pass_rate=f'{nr_tests_correct.value/max(nr_tests_done.value,1) * 100:.2f}%')
            pbar.set_description('Ray pisa testing')
            pbar.refresh()
            with nr_tests_done.get_lock():
                pbar.update(nr_tests_done.value - pbar_n)
                pbar_n = nr_tests_done.value
            time.sleep(3)  # Update every second

    # Start the subprocess
    update_process = Process(target=update_pbar, args=(nr_tasks_done, nr_tests_done, stop_event))
    update_process.start()

    try:
        for _ in range(nr_batches - early_stop_threshold):
            ret = pool.get_next_unordered(timeout=DEFAULT_TIMEOUT + 20)
            for test_info in ret:
                test_results[test_info[identifier_key]] = test_info
            with nr_tasks_done.get_lock():  # Lock to safely update shared value
                nr_tasks_done.value += 1
            with nr_tests_done.get_lock():  # Lock to safely update shared value
                nr_tests_done.value += sum('pass' in test_info for test_info in ret)
            with nr_tests_correct.get_lock():  # Lock to safely update shared value
                nr_tests_correct.value += sum(test_info.get('complete', False) for test_info in ret)

            # Check the time elapsed and save if it exceeds the interval
            current_time = time.time()
            if (current_time - last_save_time >= save_interval) and (save_file is not None):
                save_result(test_results, save_file)
                last_save_time = current_time  # Reset the last save time

    except (Exception, TimeoutError) as e:
        print(f"Exception occurred: {e}")
        stop_event.set()
        update_process.terminate()  # Terminate the subprocess if there's an exception

    # Stop the subprocess and close the progress bar
    stop_event.set()
    update_process.terminate()
    pbar.close()
    save_result(test_results, save_file)

def ray_lean4_testing(
        generated_proofs: List[dict],
        identifier_key: str = 'local id',
        save_file: str = None, 
        cpu_per_worker: int = 4,
) -> List[dict]:
    for i, test_info in enumerate(generated_proofs):
        test_info[identifier_key] = i
    test_results = {}

    if save_file is not None:
        test_results = read_file(save_file) or {}

    lemmas_to_test = [test_info for test_info in generated_proofs if test_info[identifier_key] not in test_results]
    total_size = len(lemmas_to_test)

    rng = np.random.default_rng(0)
    rng.shuffle(generated_proofs)
    lemmas_to_test = [lemmas_to_test[idx: idx + TEST_BATCH_SIZE] for idx in range(0, len(lemmas_to_test), TEST_BATCH_SIZE)]
    
    ray_lean4_actors = create_ray_lean4_actors(reserved_cpus=4, timeout=DEFAULT_TIMEOUT * TEST_BATCH_SIZE)
    pool = ActorPool(ray_lean4_actors)
    
    pool.map_unordered(lambda actor, batch: 
                            actor.run.remote(batch),
                       lemmas_to_test)
    monitor_results(pool, len(lemmas_to_test), total_size, test_results, save_file, identifier_key=identifier_key, early_stop_threshold=int(len(ray_lean4_actors) * 0.2))

    print('Stage 2: rerunning failed jobs...')
    lemmas_to_test = [test_info for test_info in generated_proofs if (test_info[identifier_key] not in test_results) 
                                                                    or ('complete' not in test_results[test_info[identifier_key]])]
    total_size = len(lemmas_to_test)
    lemmas_to_test = [[test_info] for test_info in lemmas_to_test]
    np.random.shuffle(lemmas_to_test)
    for actor in ray_lean4_actors:
        ray.kill(actor)
    
    ray_lean4_actors = create_ray_lean4_actors(reserved_cpus=4, cpus_per_task=cpu_per_worker, timeout=DEFAULT_TIMEOUT)
    pool = ActorPool(ray_lean4_actors)
    pool.map_unordered(lambda actor, batch: 
                            actor.run.remote(batch),
                        lemmas_to_test)
    monitor_results(pool, len(lemmas_to_test), total_size, test_results, save_file, identifier_key=identifier_key)

    print(f'Successfully finished {len(test_results)}/{len(generated_proofs)} tests.')
    for actor in ray_lean4_actors:
        actor.close.remote()
    for actor in ray_lean4_actors:
        ray.kill(actor)

    nr_failed_tests = 0
    for test_info in generated_proofs:
        if test_info[identifier_key] not in test_results:
            test_info['complete'] = False
            test_info['system_errors'] = 'test failed'
            test_results[test_info[identifier_key]] = test_info
            nr_failed_tests += 1
    if save_file is not None:
        save_result(test_results, save_file)
    assert nr_failed_tests < 0.01 * len(generated_proofs), f"Failed to test {nr_failed_tests} lemmas"
    return test_results

if __name__ == '__main__':
    test_inputs = json.loads('[{"lemma_id": 214, "statement": "theorem lean_workbook_214 (x y : \\u211d) : (x - y) ^ 2 \\u2265 0  :=  by", "label": ["lean_workbook", "inequality", "algebra", "number_theory"], "iter": 0, "proof": "\\n  rw [sq]\\n  apply mul_self_nonneg"}, {"lemma_id": 314, "statement": "theorem lean_workbook_314 (n : \\u2115) : \\u2211 i in Finset.range (n+1), choose n i = 2 ^ n  :=  by", "label": ["lean_workbook", "number_theory", "algebra", "combinatorics"], "iter": 0, "proof": "\\n  have := Nat.sum_range_choose n\\n  simpa only [Finset.sum_range_id] using this\\n  <;> rfl"}, {"lemma_id": 542, "statement": "theorem lean_workbook_543 : \\u2200 p : \\u2115, p.Prime \\u2192 \\u2200 n : \\u2115, p - 1 \\u2223 p ^ n - 1  :=  by", "label": ["lean_workbook", "number_theory", "divisibility", "proof"], "iter": 0, "proof": "\\n  intro p hp n\\n  simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 n"}]')
    worker = Lean4Worker(0, 0)
    results = worker.run(test_inputs, batched=True)
    pprint(results)
    import pdb; pdb.set_trace()