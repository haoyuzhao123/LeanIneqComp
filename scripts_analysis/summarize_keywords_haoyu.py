import pandas as pd
import numpy as np
import argparse

parser = argparse.ArgumentParser()
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/code_compilation.json 
parser.add_argument('--input_path',  type=str, default="results/misc_test2_kimina-7b_3/code_compilation_repl.json")
#/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/new_pipe_minif2f/compilation_summarize.json
#parser.add_argument('--output_path',  type=str)
parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)
args = parser.parse_args()



def create_random_matrix(a, m):
    """
    Create an n x m binary matrix where each row j contains exactly a[j] ones.
    
    Parameters:
        a (list or array): List/array of non-negative integers. Each value a[j] is the number of ones in row j.
        m (int): Number of columns. Must be >= max(a).
        
    Returns:
        np.ndarray: An n x m binary matrix.
    """
    n = len(a)
    if any(x > m for x in a):
        raise ValueError("m must be greater than or equal to all elements in a")
    
    # Initialize the matrix with zeros.
    matrix = np.zeros((n, m), dtype=int)
    
    # Populate each row with a[j] ones at random positions.
    for j, ones_count in enumerate(a):
        # Choose ones_count unique positions for ones.
        ones_indices = np.random.choice(m, ones_count, replace=False)
        matrix[j, ones_indices] = 1
        
    return matrix

def group_and_sum(matrix, k):
    """
    Groups the columns of a matrix into groups of k and sums each group along axis 1.
    
    Parameters:
        matrix (np.ndarray): An n x m matrix.
        k (int): The number of columns per group. Must evenly divide m.
    
    Returns:
        np.ndarray: A matrix of shape (n, m/k) where each entry is the sum of a group.
    """
    n, m = matrix.shape
    if m % k != 0:
        raise ValueError("k must evenly divide the number of columns m")
    
    # Reshape the matrix to (n, m//k, k) where each slice along axis 1 is a group of k columns.
    reshaped_matrix = matrix.reshape(n, m // k, k)
    
    # Sum along the last axis (i.e., sum over each group of k columns).
    group_sums = reshaped_matrix.sum(axis=2)
    
    return group_sums



input_file= args.input_path
df = pd.read_json(input_file)

df["compilation_result"] = df.compilation_result

df["correct"] = df["compilation_result"].apply(lambda x: x[args.field])

keyword = "concaveOn"

df["apply_keywords"] = df["code"].apply(lambda x : keyword in x)

correct_and_apply = [(r["correct"] and r["apply_keywords"]) for _, r in df.iterrows()]
df["correct_and_apply"] = correct_and_apply

df_grp = df.groupby("name")["correct"].sum() 
df_grp_apply = df.groupby("name")["correct_and_apply"].sum() 

print(df_grp)
print(df_grp_apply)

total = len(df_grp)
mat = create_random_matrix(df_grp, 128)

passes = [32,64,128]

for trial in passes:
    group_sums = group_and_sum(mat, trial)
    group_passes = (group_sums > 0)
    total_passes_in_group = np.sum(group_passes, axis=0)
    print(total_passes_in_group.shape)
    total_passes_ratio_in_group = total_passes_in_group / total * 100.0
    mean = np.mean(total_passes_ratio_in_group)
    std = np.std(total_passes_ratio_in_group)
    print("mean_std of pass %d: %.1f\\textsubscript{%.1f}" % (trial, mean, std))

# for pass and apply
total = len(df_grp_apply)
mat = create_random_matrix(df_grp_apply, 128)

passes = [32,64,128]

for trial in passes:
    group_sums = group_and_sum(mat, trial)
    group_passes = (group_sums > 0)
    total_passes_in_group = np.sum(group_passes, axis=0)
    print(total_passes_in_group.shape)
    total_passes_ratio_in_group = total_passes_in_group / total * 100.0
    mean = np.mean(total_passes_ratio_in_group)
    std = np.std(total_passes_ratio_in_group)
    print("mean_std of pass %d: %.1f\\textsubscript{%.1f}" % (trial, mean, std))


#result = {
#  "total": len(df_grp),
#  "correct": sum(df_grp > 0),
#  "accuracy": F"{sum(df_grp > 0) / len(df_grp)  * 100:.2f}",
#  "field": args.field
#}
#import json
#with open(args.output_path, "w") as f:
#    json.dump(result, f)

#
#df_grp.reset_index()[["name", "correct"]].to_csv(args.output_path.replace(".json", ".csv"), index=False, header=True, sep='\t', quoting=1, na_rep='Missing')

