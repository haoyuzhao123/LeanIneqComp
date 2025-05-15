import pandas as pd
import os
import json
from functools import reduce
import argparse

parser = argparse.ArgumentParser()
# /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
parser.add_argument('--sfx',  type=str)
# /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/auto/translator_bench
# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
args = parser.parse_args()

meta_dirs = [
    ("minif2f", "results/auto/minif2f"),
    ("proofnet", "results/proofnet"),
    ("transbench", "results/auto/translator_bench"),
]

df_list = []
for short_name, dir_ in meta_dirs:
    dict_list = []
    for ifile in os.listdir(dir_): 
        model_path = (os.path.join(dir_, ifile))
        if args.sfx is not None:
            if args.sfx not in model_path:
                continue
        model_file = os.path.join(model_path, "compilation_summarize.json")
        try:
            with open(model_file, "r") as f:
                data = json.load(f)
        except:
            continue
        data["model"] = ifile
        data[short_name] = float(data["accuracy"]) / 100
        dict_list.append(data)
    df = pd.DataFrame(dict_list)
    if short_name in df.columns:
        df_list.append(df[["model", short_name]])

merged_df = reduce(lambda left, right: pd.merge(left, right, on='model', how='outer'), df_list)

pd.set_option('display.max_rows', None)
pd.set_option('display.max_columns', None)
pd.set_option('display.width', None)
pd.set_option('display.max_colwidth', None)

print(merged_df.sort_values(by="model"))
