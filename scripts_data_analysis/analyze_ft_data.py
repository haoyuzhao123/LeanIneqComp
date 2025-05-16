import pandas as pd
import numpy as np
import json
import argparse

data_path="datasets/test_amgm_comp_5000.jsonl"

data_list = []
# Open the file and read each line
with open(data_path, 'r') as file:
    for line in file:
        # Parse the JSON object and append it to the list
        # if data_split is not None and prob['split'] not in data_split:
        #     continue
        data = json.loads(line)
        # if (data["split"] == args.split) or (args.split == "none"):
        #     data_list.append(data)
        data_list.append(data)

comp_to_icl={}

for d in data_list:
    comp_to_icl[d['name']] = d["original_problems"].split(',')

input_path="results/test_randomcomp_icl_chat_qwen-coder_seed{i}/compilation_summarize_repl.csv"

statistic={}
for i in range(1,65):
    fn = input_path.format(i=i)
    df = pd.read_csv(fn, delimiter='\t')
    for _, r in df.iterrows():
        n = r['name']
        c = int(r["correct"])
        if c > 0:
            for p in comp_to_icl[n]:
                if p not in statistic.keys():
                    statistic[p] = 0
                statistic[p] += c
print(statistic)

total = 0
for _, v in statistic.items():
    total += v
print(total)