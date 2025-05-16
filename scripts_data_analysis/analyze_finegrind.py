import re
import json

import pandas as pd

from tqdm import tqdm

import matplotlib.pyplot as plt
import numpy as np

import seaborn as sns

result_path1 = "/scratch/gpfs/st3812/aiformath/Deepseek/eval_results/minif2f_3200/FIXRWN8_Goedel-Prover-SFT_full_plus_syn_0_05_Epoch1_LR5e-6_KL0.003_N16_group_norm_G8_CKPT/global_step200_hf"

output_path1 = "testrl-step200.png"

#result_path1 = "/scratch/gpfs/st3812/aiformath/Deepseek/eval_results/minif2f_3200/Goedel-Prover-SFT_long_form_thought_data_5k_Epoch2_LR1e-5"

#output_path1 = "long-cot.png"

summary_path1 = f"{result_path1}/all_compilation_summarize.csv"

df_summary1 = pd.read_csv(summary_path1,sep='\t')

result_path2 = "/scratch/gpfs/st3812/aiformath/Deepseek/eval_results/minif2f_3200/DeepSeek-Prover-V1.5-Base__fullsonnet2reweightv2_fulllwb2reweightv2_proofnet100_minif2f10_mathlib2_Epoch1_LR1e-4"

output_path2 = "goedel.png"

summary_path2 = f"{result_path2}/all_compilation_summarize.csv"

df_summary2 = pd.read_csv(summary_path2,sep='\t')

# 1/2, 1/4, 1/8, ... 1/1024, else > 0
categories=[">1/2",">1/4",">1/8",">1/16",">1/32",">1/64",">1/128",">1/256",">1/512",">1/1024",">0"]
bins1 = [0,0,0,0,0,0,0,0,0,0,0]
bins2 = [0,0,0,0,0,0,0,0,0,0,0]

matrix = np.zeros((12,12))

total_pass = 3200

for i, r in df_summary1.iterrows():
    c = r['3200']
    ratio = c / total_pass
    if ratio > 1/2:
        a1 = 0
    elif ratio > 1/4:
        a1 = 1
    elif ratio > 1/8:
        a1 = 2
    elif ratio > 1/16:
        a1 = 3
    elif ratio > 1/32:
        a1 = 4
    elif ratio > 1/64:
        a1 = 5
    elif ratio > 1/128:
        a1 = 6
    elif ratio > 1/256:
        a1 = 7
    elif ratio > 1/512:
        a1 = 8
    elif ratio > 1/1024:
        a1 = 9
    elif ratio > 0:
        a1 = 10
    else:
        a1 = 11

    if a1 != len(bins1):
        bins1[a1] += 1
    
    r2 = df_summary2.iloc[i]
    c = r2['3200']
    ratio = c / total_pass
    if ratio > 1/2:
        a2 = 0
    elif ratio > 1/4:
        a2 = 1
    elif ratio > 1/8:
        a2 = 2
    elif ratio > 1/16:
        a2 = 3
    elif ratio > 1/32:
        a2 = 4
    elif ratio > 1/64:
        a2 = 5
    elif ratio > 1/128:
        a2 = 6
    elif ratio > 1/256:
        a2 = 7
    elif ratio > 1/512:
        a2 = 8
    elif ratio > 1/1024:
        a2 = 9
    elif ratio > 0:
        a2 = 10
    else:
        a2 = 11

    if a2 != len(bins2):
        bins2[a2] += 1
    
    matrix[a1][a2] += 1

# make the upperleft corner and lowerright corner to zero
matrix[0][0] = 0
matrix[-1][-1] = 0

fig, ax = plt.subplots()

# Create the bar plot
bars = ax.bar(categories, bins1)

# Annotate each bar with its height (value)
for bar in bars:
    height = bar.get_height()
    # Place text at the center-top of each bar
    ax.text(
        bar.get_x() + bar.get_width() / 2,  # x position: center of bar
        height,                           # y position: top of bar
        f'{height}',                      # text to display
        ha='center',                      # horizontal alignment
        va='bottom'                       # vertical alignment
    )

# Show the plot
plt.savefig(output_path1)

    
fig, ax = plt.subplots()

# Create the bar plot
bars = ax.bar(categories, bins2)

# Annotate each bar with its height (value)
for bar in bars:
    height = bar.get_height()
    # Place text at the center-top of each bar
    ax.text(
        bar.get_x() + bar.get_width() / 2,  # x position: center of bar
        height,                           # y position: top of bar
        f'{height}',                      # text to display
        ha='center',                      # horizontal alignment
        va='bottom'                       # vertical alignment
    )

# Show the plot
plt.savefig(output_path2)


plt.figure(figsize=(8, 8))
ax = sns.heatmap(matrix, annot=True, fmt=".1f", cmap="viridis", 
                 xticklabels=categories, yticklabels=categories)

# Add labels and title
plt.xlabel(output_path2)
plt.ylabel(output_path1)
plt.title("Heatmap")
plt.savefig("heatmap.png")