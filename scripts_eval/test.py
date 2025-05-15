import os
import json
import argparse

parser = argparse.ArgumentParser()
# /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
parser.add_argument('--input_path',  type=str)
parser.add_argument('--icl_folder',  type=str, default="/scratch/gpfs/haoyu/Deepseek/datasets/amgm_valid")
# /scratch/gpfs/yl7690/models/DeepSeek-Prover-V1.5-RL
parser.add_argument('--model_path', type=str)
# results/test
parser.add_argument('--output_dir',  type=str)
parser.add_argument('--split', default="none", type=str)
parser.add_argument('--n', default=32, type=int)
parser.add_argument('--gpu', default=1, type=int)
parser.add_argument('--seed', default=1, type=int)


# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
args = parser.parse_args()


# data_path = "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f_sanity10.jsonl"
data_path = args.input_path
# Initialize an empty list to hold the dictionaries
data_list = []

icl_folder = args.icl_folder

def read_lean(filename):
    with open(filename, "r") as f:
        lines = f.readlines()
    code = ''.join(lines)
    full_code_block = f"\n\n```lean4\n{code}\n```"
    return full_code_block

full_code_list = []
for i in range(1,26):
    fn_single = f"amgm_p{i}.lean"
    fn = os.path.join(icl_folder, fn_single)
    full_code_list.append(read_lean(fn))

with open("output.jsonl", "w") as f:
    for item in full_code_list:
        # Create a dictionary with the field "code"
        record = {"code": item}
        # Write the JSON object and add a newline
        f.write(json.dumps(record) + "\n")