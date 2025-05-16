import re
import json

import pandas as pd

from tqdm import tqdm

from collections import Counter



problem_set_complete_path = "/scratch/gpfs/haoyu/Deepseek/scripts_genmix_formal/others/problem_set_complete.json"

problem_set_complete = pd.read_json(problem_set_complete_path)

problems_code = problem_set_complete['code']

char_to_count = "@"
counter = Counter()
for i, problem_code in enumerate(tqdm(problems_code)):
    c = problem_code.count(char_to_count)
    counter.update([c])

    if c > 0:
        print(problem_code)
        print("\n\n\n")

print(counter)


