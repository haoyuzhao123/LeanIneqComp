import pandas as pd
import numpy as np
import argparse

parser = argparse.ArgumentParser()
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/code_compilation.json 
#parser.add_argument('--input_path',  type=str, default="results/misc_test2_r1-distill-qwen/code_compilation_repl.json")
parser.add_argument('--input_path',  type=str, default="results/amgm_valid_dsprover2/code_compilation_repl.json")
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/compilation_summarize.json
#parser.add_argument('--output_path',  type=str)
parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)
args = parser.parse_args()

input_path="results/{part}_test2_stp/compilation_summarize_repl.csv"

input_path="results/{part}_test2_dsprover2_{i}/compilation_summarize_repl.csv"

total=0
count_pass=0

batch = True
start=1
end=8
if batch:
    for part in ["amgm", "cauchy", "misc"]:
        correct_list = []
        for i in range(start, end+1):
            input_file = input_path.format(part=part,i=i)
            df = pd.read_csv(input_file, delimiter='\t')
            for _, r in df.iterrows():
                p = int(r['correct'])
                n = r['name']
                if p > 0:
                    if n not in correct_list:
                        correct_list.append(n)
                    total += p
        count_pass += len(correct_list)
else:
    for part in ["amgm", "cauchy", "misc"]:
        input_file = input_path.format(part=part)
        df = pd.read_csv(input_file, delimiter='\t')
        for _, r in df.iterrows():
            p = int(r['correct'])
            if p > 0:
                count_pass += 1
                total += p

print(f"pass ratio on correct problems: {total / (count_pass * 3200)}")
print(f"pass ratio on all problems: {total / (75 * 3200)}")
