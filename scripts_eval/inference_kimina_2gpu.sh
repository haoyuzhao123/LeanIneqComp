#!/bin/bash
#SBATCH --job-name=inference # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=24        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=10G         # memory per cpu-core (4G is default)
#SBATCH --gres=gpu:2       # number of gpus per node
#SBATCH --time=23:00:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-type=ALL
#SBATCH --mail-user=haoyu@princeton.edu
#SBATCH --partition=pli-c
#SBATCH --output=slurm/%x-%j.out
#SBATCH --constraint="rh8|rh9"

#### #SBATCH --qos=pli-cp

source /scratch/gpfs/haoyu/miniconda3/etc/profile.d/conda.sh
conda activate skillmixlean

export LD_LIBRARY_PATH=/scratch/gpfs/haoyu/miniconda3/lib:$LD_LIBRARY_PATH

export HF_HOME=/scratch/gpfs/haoyu/cache/

#cd /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5

#INPUT_PATH=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f_sanity10.jsonl
INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/extracted_pp/extracted_perturb_problem_naive_hard_r1-distill-qwen_full.jsonl
# following is Kimina
MODEL_PATH=/scratch/gpfs/ARORA/haoyu/kimina-7b





#MODEL_PATH=/scratch/gpfs/yl7690/projects/LeanRL/models/FIXRWN8_Goedel-Prover-SFT_half_0_05_Epoch1_LR5e-6_KL0.00003_N16_group_norm_G8
#MODEL_PATH=/scratch/gpfs/st3812/projects/LLM-training/models/DeepSeek-R1-Distill-Qwen-32B_lwb_v1tov5_cot2_Epoch2_LR2e-4/
#MODEL_PATH=/scratch/gpfs/yl7690/models/DeepSeek-Prover-V1.5-Base__ours_tengyus_Epoch2_LR1e-4
#MODEL_PATH=/scratch/gpfs/st3812/projects/LLM-training/models/DeepSeek-R1-Distill-Qwen-7B_lwb_v1tov5_cot2_Epoch2_LR5e-5
#OUTPUT_DIR=results/scripts_genmix_formal/extracted_perturb_problem_naive_medium_r1-distill-qwen


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

INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/real.jsonl
OUTPUT_DIR=results/real_kimina-7b_$SEED

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/minif2f.jsonl
#OUTPUT_DIR=results/minif2f_test_goedel_amgm_replicate_15k
#split="test"


echo python scripts_eval/step1_inference_kimina.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED
python scripts_eval/step1_inference_kimina.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

#sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR
sbatch scripts_eval/compile_summarize_test_repl.sh -i $INPUT_FILE -o $OUTPUT_DIR