import json
import pandas as pd

filename = "results/minif2f_test_goedel_comp_15k/compilation_summarize_repl.csv"
test_list = []

with open("datasets/minif2f.jsonl", "r") as f:
    d_list = [json.loads(line) for line in f]
    for d in d_list:
        if d['split'] == 'test':
            test_list.append(d['name'])

print(len(test_list))

df = pd.read_csv(filename, delimiter='\t')
print(df)
count = 0
for i, r in df.iterrows():
    if r['name'] in test_list:
        if r['correct'] != 0:
            count += 1

print(count / len(test_list))