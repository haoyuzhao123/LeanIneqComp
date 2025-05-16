import pandas as pd
import numpy as np
import json
import argparse

keywords=["geom_mean_le_arith_mean"]



#input_path="results/{part}_valid_kimina-7b_{i}/code_compilation_repl.json"
input_path="results/{part}_valid_dsprover_rl/code_compilation_repl.json"
#/scratch/gpfs/yl7690/projects/

start=1
end=8
batch=False
total_try = 0
total_try_and_correct = 0
if batch:
    for i in range(start, end+1):
        for part in ['amgm','cauchy','misc']:
            input_file = input_path.format(part=part,i=i)
            df = pd.read_json(input_file)

            for _, r in df.iterrows():
                code = r['code']
                for k in keywords:
                    if k in code:
                        total_try += 1
                        if r["compilation_result"]["complete"]:
                            total_try_and_correct += 1
                        break
else:
    for part in ['amgm','cauchy','misc']:
        input_file = input_path.format(part=part)
        df = pd.read_json(input_file)
        for _, r in df.iterrows():
            code = r['code']
            for k in keywords:
                if k in code:
                    total_try += 1
                    if r["compilation_result"]["complete"]:
                        total_try_and_correct += 1
                    break


print(f"total try: {total_try}, total_try_and_correct: {total_try_and_correct}")