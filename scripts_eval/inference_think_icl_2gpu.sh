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


N=128
SEED=1
SPLIT=none

# R1-distill-qwen-32b
#MODEL_PATH="/scratch/gpfs/haoyu/models/deepseek-r1-distill-qwen-32b/"

# Qwen2.5-Coder-Instruct
MODEL_PATH="/scratch/gpfs/ARORA/haoyu/Qwen2.5-Coder-32B-Instruct"


# choose split from amgm/cauchy/misc
PART=misc
TYPE=1
INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/${PART}_test${TYPE}.jsonl
ICL_FOLDER=/scratch/gpfs/haoyu/Deepseek/datasets/${PART}_valid
#INPUT_PATH=/scratch/gpfs/haoyu/Deepseek/datasets/test.jsonl
#OUTPUT_DIR=results/testAMGM_minif2ftestineq

# for r1-distill-qwen
#OUTPUT_DIR=results/${PART}_test${TYPE}_icl_think_r1-distill-qwen
# for qwen coder
OUTPUT_DIR=results/${PART}_test${TYPE}_icl_chat_qwen-coder


echo python scripts_eval/step1_inference_think_icl.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED --icl_folder $ICL_FOLDER
python scripts_eval/step1_inference_think_icl.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED --icl_folder $ICL_FOLDER

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

#sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR
sbatch scripts_eval/compile_summarize_test_repl.sh -i $INPUT_FILE -o $OUTPUT_DIR