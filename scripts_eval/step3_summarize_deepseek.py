import pickle
import json
from tqdm import tqdm
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--input_path', default="", type=str)
# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
args = parser.parse_args()


# This script collect the inference results by deepseek on Leanworkbook and output whether a problem is solved.
# This script can be adopted in other datasets' analysis

# Define the file path
def analyze_success_data(file_path):
    # Read the Pickle file
    with open(file_path, 'rb') as file:
        data = pickle.load(file)

    success_trials = []
    for i_data in data:
        if i_data["result"]["complete"]:
            success_trials.append(i_data)
    return success_trials

def analyze_fail_data(file_path):
    # file_path = 'failure-Sampling-run0-20241018_063955.pkl'
    # Read the Pickle file
    with open(file_path, 'rb') as file:
        data = pickle.load(file)

    failed_trials = []
    for i_data in data:
        if not i_data["result"]["complete"]:
            failed_trials.append(i_data)
    return failed_trials

# start_position = 0
dir = args.input_path
import os
subdirs = os.listdir(dir)
full_data = []
success_count = 0
for subdir in tqdm(subdirs):
    full_subdir = dir + "/"+ subdir
    if not os.path.isdir(full_subdir):
        continue
    scs_files = [x for x in os.listdir(full_subdir) if '.pkl' in x and "success" in x]
    fail_files = [x for x in os.listdir(full_subdir) if '.pkl' in x and "fail" in x]
    assert len(scs_files) <= 1    
    assert len(fail_files) <= 1
    problem_id = None
    formal_statement = None  
    success_runs = None
    success_proof_example = None 
    failed_runs = None 
    success_num = 0
    failed_num = 0
    if len(scs_files) == 1:
        pkl_file = scs_files[0]
        full_file_path = full_subdir + "/" + pkl_file
        success_runs = analyze_success_data(full_file_path)
        problem_id = success_runs[0]["problem_name"]
        formal_statement = success_runs[0]["formal_statement"]  
        success_num = len(success_runs)
        import random
        random_success = random.choice(success_runs)
        success_proof_example = random_success['proof_code']
    if len(fail_files) == 1:
        assert len(fail_files) == 1
        pkl_file = fail_files[0]
        full_file_path = full_subdir + "/" + pkl_file
        failed_runs = analyze_fail_data(full_file_path)
        problem_id = failed_runs[0]["problem_name"]
        formal_statement = failed_runs[0]["formal_statement"]  
        failed_num = len(failed_runs)
        # print(F"Failed at {i}th problem")
    full_data.append({
        "problem_id":problem_id,
        "formal_statement":formal_statement,
        # "success_runs":success_runs, 
        # "failed_runs":failed_runs, 
        "success_num":success_num,
        "failed_num":failed_num,
        "success_proof_example": success_proof_example
    })
import pandas as pd
df = pd.DataFrame(full_data)
collected_results_output = args.input_path + "/collected.json"
with open(collected_results_output, "w") as f:
    json.dump(full_data, f, indent=4)

summary_results_output = args.input_path + "/summary.txt"
success_num = sum(df.success_num>0)
total_num = sum((df.success_num + df.failed_num)>0)

output_str = (F"The current accuracy is {success_num} / {total_num}: {success_num / total_num}")
with open(summary_results_output, "w") as f:
    f.write(output_str)
print(output_str)
# import json
# file_path = F"/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/leanworkbook_inference/inference_collect.json"
# with open(file_path, 'w') as json_file:
#     json.dump(full_data, json_file, indent=4)
