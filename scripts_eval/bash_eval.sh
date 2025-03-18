INPUT_PATH=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
SPLIT=test
epochs=(3)
learning_rates=(2e-4)
for epoch in "${epochs[@]}"; do
    for lr in "${learning_rates[@]}"; do
	model=Qwen2.5-Coder-32B_lean_workbook_sonnetv1v2v3_qwcot_full16_success_compile_reweight_Epoch${epoch}_LR${lr}
	# model=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/Qwen2.5-Coder-32B_lean_workbook_sonnetv1v2v3_qwcot_full16_success_compile_reweight_Epoch2_LR2e-4
	MODEL_PATH=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/$model
	OUTPUT_DIR=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/auto/minif2f/$model
        echo sbatch scripts_eval/eval_minif2f.sh -i $INPUT_PATH -m $MODEL_PATH -o $OUTPUT_DIR -s $SPLIT
        sbatch scripts_eval/eval_minif2f.sh -i $INPUT_PATH -m $MODEL_PATH -o $OUTPUT_DIR -s $SPLIT
    done
done

