#!/bin/bash
#SBATCH --job-name=inference # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=24        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=10G         # memory per cpu-core (4G is default)
#SBATCH --gres=gpu:2        # number of gpus per node
#SBATCH --time=23:00:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-type=FAIL
#SBATCH --mail-user=haoyu@princeton.edu
#SBATCH --partition=pli-c
#SBATCH --output=slurm/%x-%j.out

#### #SBATCH --qos=pli-cp

source /scratch/gpfs/haoyu/miniconda3/etc/profile.d/conda.sh
conda activate skillmixlean

export LD_LIBRARY_PATH=/scratch/gpfs/haoyu/miniconda3/lib:$LD_LIBRARY_PATH

export HF_HOME=/scratch/gpfs/haoyu/cache/

#cd /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5

#INPUT_PATH=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f_sanity10.jsonl
INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/extracted_pp/extracted_perturb_problem_naive_hard_r1-distill-qwen_full.jsonl
MODEL_PATH=/scratch/gpfs/haoyu/models/goedel-prover-sft
MODEL_PATH=/scratch/gpfs/haoyu/models/stp
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

INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/minif2f_ineq.jsonl
#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/test.jsonl
OUTPUT_DIR=results/testAMGM_minif2ftestineq_stp
OUTPUT_DIR=results/testAMGM


echo python scripts_eval/step1_inference.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2
python scripts_eval/step1_inference.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

#sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR
sbatch scripts_eval/compile_summarize_test_repl.sh -i $INPUT_FILE -o $OUTPUT_DIR