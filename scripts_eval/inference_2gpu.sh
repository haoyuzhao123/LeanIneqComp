#!/bin/bash
#SBATCH --job-name=inference # create a short name for your job
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

#export LD_LIBRARY_PATH=/path/to/your/condalib:$LD_LIBRARY_PATH


INPUT_PATH=benchmark/amgm_seed.jsonl
# following is DeepSeek prover v1.5 RL
MODEL_PATH=deepseek-ai/DeepSeek-Prover-V1.5-RL 
# following is the Goedel Prover
MODEL_PATH=Goedel-LM/Goedel-Prover-SFT
# following is the STP model from Kefan and Tengyu
MODEL_PATH=kfdong/STP_model_Lean
# following is the r1 distill qwen model
MODEL_PATH=deepseek-ai/DeepSeek-R1-Distill-Qwen-32B

OUTPUT_DIR=results/${MODEL_PATH}/${INPUT_PATH}

SPLIT=none
N=128

SEED=1


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

bash scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR
# uncomment the following if you are using SLURM
# change the configuration to fit your SLURM system in the following file if needed
# sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR