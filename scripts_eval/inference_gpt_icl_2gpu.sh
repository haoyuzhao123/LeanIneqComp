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


SPLIT=none
N=16

SEED=1



MODEL_PATH="gpt-4o-mini"
#MODEL_PATH="gpt-4o"

# choose split from amgm/cauchy/misc
# choose type from seed/type1/type2
PART=misc
TYPE=seed
INPUT_PATH=benchmark/${PART}_${TYPE}.jsonl
ICL_FOLDER=benchmark/full_answer/${PART}_${TYPE}_4.9

OUTPUT_DIR=results/${PART}_test${TYPE}-icl_gpt-4o-mini



echo python scripts_eval/step1_inference_gpt_icl.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED --icl_folder $ICL_FOLDER
python scripts_eval/step1_inference_gpt_icl.py --input_path ${INPUT_PATH}  --model_path ${MODEL_PATH}  --output_dir $OUTPUT_DIR --split $SPLIT --n $N --gpu 2 --seed $SEED --icl_folder $ICL_FOLDER

INPUT_FILE=${OUTPUT_DIR}/to_inference_codes.json

sbatch scripts_eval/compile_summarize.sh -i $INPUT_FILE -o $OUTPUT_DIR