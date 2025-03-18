for i in {18..18}; do
    start=$((1000 * i))
    end=$((1000 * (i + 1)))
    split="$start-$end"
    N=128
    INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/extracted_pp_batch/extracted_perturb_problem_naive_hard_r1-distill-qwen_"$split".jsonl
    OUTPUT_DIR=results/batch_results/extracted_perturb_problem_naive_hard_pass"$N"_r1-distill-qwen_"$split"
    sbatch scripts_eval/inference_2gpu.sh -i $INPUT_PATH -o $OUTPUT_DIR -n $N
done
