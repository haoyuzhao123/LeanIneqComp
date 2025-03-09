import json
import sys

sys.path.append("/scratch/gpfs/haoyu/Deepseek")

from prover.lean.verifier import Lean4ServerScheduler

import argparse

parser = argparse.ArgumentParser()
# 'results/test/to_inference_codes.json'
parser.add_argument('--input_path', default="", type=str)
# 'results/test/code_compilation.json'
parser.add_argument('--output_path', default="", type=str)
# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
parser.add_argument('--cpu', default=64, type=int)
args = parser.parse_args()

input_file_path = args.input_path

with open(input_file_path, 'r') as json_file:
    codes = json.load(json_file)

lean4_scheduler = Lean4ServerScheduler(max_concurrent_requests=args.cpu, timeout=300, memory_limit=10, name='verifier')

request_id_list = lean4_scheduler.submit_all_request([code["code"] for code in codes])
outputs_list = lean4_scheduler.get_all_request_outputs(request_id_list)
lean4_scheduler.close()

assert len(outputs_list) == len(codes)
ana_result = []
for i in range(len(codes)):
    codes[i]["compilation_result"] = outputs_list[i]
    ana_result.append(
        {"name": codes[i]["name"],
         "compilation_result": outputs_list[i]["complete"]}
    )
with open(args.output_path, 'w') as json_file:
    json.dump(codes, json_file, indent=4)
