import pandas as pd
import numpy as np
import argparse
import random

parser = argparse.ArgumentParser()
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/older_saved/training/minif2f_valid128/code_compilation.json
parser.add_argument('--input_path',  type=str)
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/compilation_summarize.json
parser.add_argument('--output_path',  type=str)
args = parser.parse_args()


input_file= args.input_path
df = pd.read_json(input_file)

df["correct"] = df.compilation_result.apply(lambda x: x["complete"])

df_grp = df.groupby("name")["correct"].sum() 

df_sum = df.groupby("name")["code"].count() 

result = {
  "total": len(df_grp),
  "correct": sum(df_grp > 0),
  "accuracy": F"{sum(df_grp > 0) / len(df_grp)  * 100:.2f}"
}
correct_samples = dict(df_grp)
sum_samples = dict(df_sum)

def find_correct_samples(name):
    return correct_samples[name]

def find_sum_samples(name):
    return sum_samples[name]

df["correct_num"] = df["name"].apply(lambda x: find_correct_samples(x))
df["total_num"] = df["name"].apply(lambda x: find_sum_samples(x))
df["ratio"] = df["correct_num"] / df["total_num"]

output_results = []
correct_df = df[df.correct > 0]
for name in list(np.unique(correct_df.name)):
    sub_df = correct_df[correct_df.name == name] 
    code_list = list(sub_df["code"])
    code = random.choice(code_list)
    full_proof = F"Complete the following Lean 4 code:\n\n```lean4\n{code}\n``` "
    output_results.append({"full_proof": full_proof, "source": "proofnet"})

dfo = pd.DataFrame(output_results)

dfo.to_json(args.output_path, orient='records', lines=True)
#
