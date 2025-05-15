for part in "amgm" "cauchy" "misc"
do
    for split in "valid" "test1" "test2"
    do
        INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/${part}_${split}.jsonl
        MODEL_PATH=models/goedel-prover-sft_new_comp_10k_Epoch2_LR5e-5
        OUTPUT_DIR=results/${part}_${split}_${MODEL_PATH}
        sbatch scripts_eval/inference_2gpu.sh -i $INPUT_PATH -m $MODEL_PATH -o $OUTPUT_DIR
    done
done