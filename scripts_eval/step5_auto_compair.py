import pandas as pd
import numpy as np
path1 = "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/auto/minif2f/DeepSeek-Prover-V1.5-Base_leanworkbook_deepseek_v1v2v3_translator___Epoch2_LR5e-5/compilation_summarize.csv"

path2 = "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/auto/minif2f/DeepSeek-Prover-V1.5-Base_leanworkbook_1_numina_sonnet_130K_1_Epoch2_LR1e-4/compilation_summarize.csv"

df1 = pd.read_csv(path1, sep='\t')
df2 = pd.read_csv(path2, sep='\t')
domains = np.unique(df1.name.apply(lambda x: x.split("_")[0]))
# ['aime', 'algebra', 'amc12', 'amc12a', 'amc12b', 'imo', 'imosl','induction', 'mathd', 'numbertheory']


df1["domain"] = (df1.name.apply(lambda x: x.split("_")[0]))
df1["correct_01"] = df1.correct > 0

df2["domain"] = (df2.name.apply(lambda x: x.split("_")[0]))
df2["correct_01"] = df2.correct > 0

for domain in domains:
    df1_sub = df1[df1.domain == domain]
    df2_sub = df2[df2.domain == domain]
    merged_sub = pd.merge(df1_sub, df2_sub, on='name', how='inner')
    assert len(merged_sub) == len(df1_sub)
    assert len(merged_sub) == len(df2_sub)
    print("-" * 10, domain, len(merged_sub), "-" * 10)
    print("-" * 0, "Both Correct", len(merged_sub[(merged_sub.correct_x>0)&(merged_sub.correct_y>0)]), "-" * 0)
    print("-" * 0, "Both Wrong", len(merged_sub[(merged_sub.correct_x==0)&(merged_sub.correct_y==0)]), "-" * 0)
    print("-" * 0, "1st Correct", len(merged_sub[(merged_sub.correct_x>0)&(merged_sub.correct_y==0)]), "-" * 0)
    print("-" * 0, "2nd Correct", len(merged_sub[(merged_sub.correct_x==0)&(merged_sub.correct_y>0)]), "-" * 0)
