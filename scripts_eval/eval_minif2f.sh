#!/bin/bash
#SBATCH --job-name=inference # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=24        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=10G         # memory per cpu-core (4G is default)
#SBATCH --gres=gpu:2        # number of gpus per node
#SBATCH --time=23:00:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-user=yl7690@princeton.edu
#SBATCH --partition=pli-c

source ~/.bashrc
conda activate Deepseek2

cd /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5

INPUT_PATH=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
MODEL_PATH=/scratch/gpfs/yl7690/models/DeepSeek-Prover-V1.5-RL
OUTPUT_DIR=results/test_deepseek_rl_eval_minif2f
SPLIT=test
N=32
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
echo python scripts_eval/step1_inference.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2
python scripts_eval/step1_inference.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

sbatch scripts_eval/compile_summarize_short.sh -i $INPUT_FILE -o $OUTPUT_DIR
