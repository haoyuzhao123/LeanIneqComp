#!/bin/bash
#SBATCH --job-name=JOBNAME # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=24        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=10G         # memory per cpu-core (4G is default)
#SBATCH --gres=gpu:2       # number of gpus per node
#SBATCH --time=23:00:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-type=ALL
#SBATCH --mail-user=EMAIL
#SBATCH --partition=PARTITION
#SBATCH --output=slurm/%x-%j.out

source /path/to/your/conda/etc/profile.d/conda.sh
conda activate skillmixlean

export LD_LIBRARY_PATH=/path/to/your/conda/lib:$LD_LIBRARY_PATH

INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/extracted_pp/extracted_perturb_problem_naive_hard_r1-distill-qwen_full.jsonl
# following is Kimina
MODEL_PATH=/scratch/gpfs/ARORA/haoyu/deepseek-prover-v2-7b


SPLIT=none
N=128
OUTPUT_DIR=results/scripts_genmix_formal/extracted_perturb_problem_naive_hard_"$N"_r1-distill-qwen_full


SEED=1


while getopts ":i:m:o:s:n:d:" opt; do
  case $opt in
    i) INPUT_PATH="$OPTARG"
    ;;
    m) MODEL_PATH="$OPTARG"
    ;;
    o) OUTPUT_DIR="$OPTARG"
    ;;
    s) SPLIT="$OPTARG"
    ;;
    n) N="$OPTARG"
    ;;
    d) SEED="$OPTARG"
    ;;
  esac
done

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/minif2f_ineq.jsonl
#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/misc_valid.jsonl
#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/test_comp2.jsonl
#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/test.jsonl
#OUTPUT_DIR=results/testAMGM_minif2ftestineq
#OUTPUT_DIR=results/misc_valid_dsprover_rl
#OUTPUT_DIR=results/goedel_ft_${MODEL_ID}_cauchy_valid

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/comp2_amgm_100.jsonl
#OUTPUT_DIR=results/comp2_amgm_100_goedel_amgm_replicate_15k

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/comp_amgm_100.jsonl
#OUTPUT_DIR=results/comp_amgm_100_goedel_amgm_replicate_5k

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/comp_100.jsonl
#OUTPUT_DIR=results/comp_100_kimina-7b_$SEED

INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/comp_alg_w_100.jsonl
OUTPUT_DIR=results/comp_alg_w_100_dsprover2_$SEED

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/minif2f.jsonl
#OUTPUT_DIR=results/minif2f_test_goedel_amgm_replicate_15k
#split="test"


echo python scripts_eval/step1_inference_dsprover2.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED
python scripts_eval/step1_inference_dsprover2.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR