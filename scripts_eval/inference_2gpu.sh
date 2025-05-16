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
# following is DeepSeek prover v1.5 RL
MODEL_PATH=/scratch/gpfs/haoyu/models/deepseek-prover-v15-rl
# following is the Goedel Prover
MODEL_PATH=/scratch/gpfs/haoyu/models/goedel-prover-sft

# following is the dpo model
#MODEL_PATH=/scratch/gpfs/yl7690/models/dpo_DPO_iter0_lwb025lstLength_sonnet025lstLength_b0.03_f0.5_lr1e-6_e2

# following in the STP model from Kefan and Tengyu
MODEL_PATH=/scratch/gpfs/haoyu/models/stp

# R1-distill-qwen-32b
#MODEL_PATH="/scratch/gpfs/ARORA/haoyu/deepseek-r1-distill-qwen-32b/"

# goedel finetuned on amgm data
#MODEL_ID=Epoch2_LR5e-5
#MODEL_PATH=models/goedel-prover-sft_comp_5k_${MODEL_ID}
#MODEL_PATH=models/stp_combined_${MODEL_ID}

# model with have
#MODEL_PATH=/scratch/gpfs/st3812/projects/LLM-training/models/DeepSeek-R1-Distill-Qwen-32B_lwb_v1tov5_cot2_Epoch2_LR2e-4




#MODEL_PATH=/scratch/gpfs/yl7690/projects/LeanRL/models/FIXRWN8_Goedel-Prover-SFT_half_0_05_Epoch1_LR5e-6_KL0.00003_N16_group_norm_G8
#MODEL_PATH=/scratch/gpfs/st3812/projects/LLM-training/models/DeepSeek-R1-Distill-Qwen-32B_lwb_v1tov5_cot2_Epoch2_LR2e-4/
#MODEL_PATH=/scratch/gpfs/yl7690/models/DeepSeek-Prover-V1.5-Base__ours_tengyus_Epoch2_LR1e-4
#MODEL_PATH=/scratch/gpfs/st3812/projects/LLM-training/models/DeepSeek-R1-Distill-Qwen-7B_lwb_v1tov5_cot2_Epoch2_LR5e-5
#OUTPUT_DIR=results/scripts_genmix_formal/extracted_perturb_problem_naive_medium_r1-distill-qwen


SPLIT=none
N=128
OUTPUT_DIR=results/scripts_genmix_formal/extracted_perturb_problem_naive_hard_"$N"_r1-distill-qwen_full


while getopts ":i:m:o:s:n:" opt; do
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

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/comp_alg_w_100.jsonl
#OUTPUT_DIR=results/comp_alg_w_100_nothink-r1-distill-qwen

INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/real.jsonl
OUTPUT_DIR=results/real_stp

#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/minif2f.jsonl
#OUTPUT_DIR=results/minif2f_test_goedel_amgm_replicate_15k
#split="test"


echo python scripts_eval/step1_inference.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2
python scripts_eval/step1_inference.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

bash scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR
# uncomment the following if you are using SLURM
# change the configuration to fit your SLURM system in the following file if needed
# sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR