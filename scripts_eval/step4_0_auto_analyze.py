import pandas as pd
import os
import json

import re
import argparse

parser = argparse.ArgumentParser()
# /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
parser.add_argument('--sfx',  type=str)
parser.add_argument('--results_dir', default="/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/auto/minif2f", type=str)
# /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/auto/translator_bench
# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
args = parser.parse_args()


dir_ = args.results_dir
dict_list = []
for ifile in os.listdir(dir_):
    model_path = (os.path.join(dir_, ifile))
    model_file = os.path.join(model_path, "compilation_summarize.json")
    try:
        with open(model_file, "r") as f:
            data = json.load(f)
    except:
        continue
    data["model"] = ifile
    # # -----only use this time ----
    # match = re.search(r'epoch(\d+).*LR([0-9e\-.]+)', model_file)
    # if match:
    #     epoch = match.group(1)
    #     lr = match.group(2)
    #     data["epoch"] = epoch
    #     data["lr"] = lr
    # # -----only use this time ----
    dict_list.append(data)

# Use regex to find epoch and lr

df = pd.DataFrame(dict_list)
pd.set_option('display.max_rows', None)
pd.set_option('display.max_columns', None)
pd.set_option('display.width', None)
pd.set_option('display.max_colwidth', None)
if args.sfx is None:
    print(df.sort_values(by="model").reset_index(drop=True))
else:
    df = df[df.model.apply(lambda x: args.sfx in x)]
    print(df.sort_values(by="model").reset_index(drop=True).head(30))
# df = pd.read_json(model_file)
# print(df)
