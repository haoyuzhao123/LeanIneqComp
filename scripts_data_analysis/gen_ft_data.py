import pandas as pd
import numpy as np
import argparse

parser = argparse.ArgumentParser()
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/code_compilation.json 
parser.add_argument('--input_path',  type=str, default="results/test_randomcomp_icl_chat_qwen-coder_seed{i}/code_compilation_repl.json")
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/compilation_summarize.json
#parser.add_argument('--output_path',  type=str)
parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)
args = parser.parse_args()

start=1
end=64
DEFAULT_IMPORTS = f"import Mathlib\nimport Aesop\nopen BigOperators Real Nat Topology Rat\n\n"

df_list = []
for i in range(start, end+1):
    input_file = args.input_path.format(i=i)
    df = pd.read_json(input_file)

    df["correct"] = df.compilation_result.apply(lambda x: x[args.field])
    print(df.shape)
    filtered_df = df[df["correct"]]
    print(filtered_df.shape)
    for i, r in filtered_df.iterrows():
        filtered_df.loc[i,'code'] = DEFAULT_IMPORTS+r['code']
    df_list.append(filtered_df)

new_df = pd.concat(df_list)
new_df.reset_index()

for i, r in new_df.iterrows():
    new_df.loc[i,'code'] = DEFAULT_IMPORTS+r['code']

new_df.to_json("datasets/combined_new.jsonl", orient="records", lines=True)