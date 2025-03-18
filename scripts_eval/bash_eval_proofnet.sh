models=(
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_Epoch2_LR1e-4"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_Epoch2_LR5e-5"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_Epoch3_LR1e-4"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_Epoch3_LR5e-5"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_reweight_Epoch2_LR1e-4"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_reweight_Epoch2_LR5e-5"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_reweight_Epoch3_LR1e-4"
    "DeepSeek-Prover-V1.5-Base_lean_workbook_sonnetv1v2v3_deepseek_full16_success_compile_reweight_Epoch3_LR5e-5"
)
# "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/Qwen2.5-Coder-32B_Leanworkbook_sonnet_v1v2_deepseek_subproblem_____Epoch3_LR2e-4"
# "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/Qwen2.5-Coder-7B_Leanworkbook_sonnet_v1v2_deepseek_subproblem_____Epoch3_LR1e-4"
# "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/DeepSeek-Prover-V1.5-Base_Leanworkbook_sonnet_v1v2_deepseek_subproblem_____Epoch3_LR5e-5"
# "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/DeepSeek-Prover-V1.5-Base_sonnet_v1v2_deepseek_v1v2v3_translator_subproblem______Epoch2_LR1e-4"
# "/scratch/gpfs/yl7690/models/Qwen2.5-Coder-32B_sonnet_v12v2v3_iter3_translator_PASS16_success_compile_Epoch5_LR2e-4"
# "/scratch/gpfs/yl7690/models/DeepSeek-Prover-V1.5-Base_leanworkbook_sonnet130K_sonnetnew100K_bk_Epoch3_LR1e-4"
# "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/DeepSeek-Prover-V1.5-Base_sonnet_v1v2_deepseek_v1v2v3_translator_subproblem______Epoch2_LR1e-4"

# Iterate through each model
for model in "${models[@]}"; do
    # Extract the model name (last part of the path)
    model_name=$(basename "$model")   
    sbatch scripts_eval/eval_proofnet.sh -m models/$model -o results/proofnet/${model_name}
done
