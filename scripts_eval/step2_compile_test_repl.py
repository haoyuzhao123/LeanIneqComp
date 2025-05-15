import json
import sys

import os

# sys.path.append("/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5")

# Add parent directory to sys.path
parent_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
if parent_dir not in sys.path:
    sys.path.append(parent_dir)

from prover.lean.verifier import Lean4ServerScheduler

from prover.lean.test_repl import parallel_verification

from prover.lean.test_repl_scheduler import scheduler

import argparse

import random

import numpy as np

def split_list_randomly(lst, k):
    random.shuffle(lst)  # Shuffle the list randomly
    return list(map(list, np.array_split(lst, k)))  # Split into k approximately equal parts


parser = argparse.ArgumentParser()
# 'results/test/to_inference_codes.json'
parser.add_argument('--input_path', default="", type=str)
# 'results/test/code_compilation.json'
parser.add_argument('--output_path', default="", type=str)
# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
parser.add_argument('--cpu', default=64, type=int)
parser.add_argument('--import_timeout', default=300, type=int)
parser.add_argument('--proof_timeout', default=300, type=int)
parser.add_argument('--max_heartbeats', default=500_000, type=int)
args = parser.parse_args()

input_file_path = args.input_path

with open(input_file_path, 'r') as json_file:
    codes = json.load(json_file)

# lean4_scheduler = Lean4ServerScheduler(max_concurrent_requests=args.cpu, timeout=300, memory_limit=10, name='verifier')

# request_id_list = lean4_scheduler.submit_all_request([code["code"] for code in codes])
# outputs_list = lean4_scheduler.get_all_request_outputs(request_id_list)
# lean4_scheduler.close()


# remove imports

imports = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n"

for code in codes:
    code["code"] = code["code"][len(imports):]

# to_compile_problems_list= split_list_randomly(codes, args.cpu)

# outputs_list = parallel_verification(to_compile_problems_list)

# to_compile_problems_list_one = [to_compile_problems_list[0]]

# outputs_list = parallel_verification(to_compile_problems_list_one)

random.shuffle(codes)

outputs_list = scheduler(codes, num_workers = args.cpu, import_timeout=args.import_timeout, proof_timeout=args.proof_timeout, max_heartbeats=args.max_heartbeats)

os.makedirs(os.path.dirname(args.output_path), exist_ok=True)
with open(args.output_path, 'w') as json_file:
    json.dump(outputs_list, json_file, indent=4)