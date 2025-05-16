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

#source /path/to/your/conda/etc/profile.d/conda.sh
#conda activate CONDA_ENV

#export LD_LIBRARY_PATH=/path/to/your/conda/lib:$LD_LIBRARY_PATH

INPUT_PATH=benchmark/amgm_seed.jsonl
# following is DeepSeek-Prover-V2-7B
MODEL_PATH=deepseek-ai/DeepSeek-Prover-V2-7B


SPLIT=none
N=132
OUTPUT_DIR=results/${MODEL_PATH}/${INPUT_PATH}


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


echo python scripts_eval/step1_inference_dsprover2.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED
python scripts_eval/step1_inference_dsprover2.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

bash scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR
# uncomment the following if you are using SLURM
# change the configuration to fit your SLURM system in the following file if needed
# sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR