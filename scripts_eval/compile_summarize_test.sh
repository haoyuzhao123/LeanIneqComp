#!/bin/bash
#SBATCH --job-name=lean-compile    # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=16 # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=8G         # memory per cpu-core (4G is default)
#SBATCH --time=10:00:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-type=all          # send email on job start, end and fault
echo "Executing on the machine:" $(hostname)


source ~/.bashrc
conda activate Deepseek2

cd /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5

FIELD=complete

# INPUT_FILE=results/test/to_inference_codes.json
# OUPUT_FILE=results/test/code_compilation.json

while getopts ":i:o:f:" opt; do
  case $opt in
    i) INPUT_FILE="$OPTARG"
    ;;
    o) OUTPUT_DIR="$OPTARG"
    ;;
    f) FIELD="$OPTARG"
    ;;
  esac
done

mkdir -p $OUTPUT_DIR


COMPILE_OUTPUT_PATH=${OUTPUT_DIR}/code_compilation.json

python scripts_eval/step2_compile.py --input_path $INPUT_FILE --output_path $COMPILE_OUTPUT_PATH --cpu 64


SUMMARIZE_OUTPUT_PATH=${OUTPUT_DIR}/compilation_summarize.json

python scripts_eval/step3_summarize_compile.py --input_path $COMPILE_OUTPUT_PATH --output_path $SUMMARIZE_OUTPUT_PATH --field ${FIELD}

