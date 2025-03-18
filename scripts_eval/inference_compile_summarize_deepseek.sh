#!/bin/bash
#SBATCH --job-name=eval_minif2f  # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=16  # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=10G         # memory per cpu-core (4G is default)
#SBATCH --gres=gpu:1        # number of gpus per node
#SBATCH --time=10:10:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-type=end          # send email when job ends
#SBATCH --mail-user=yl7690@princeton.edu
#SBATCH --partition=pli-c

source ~/.bashrc
conda activate Deepseek2


time_step=$(date +"%m%d%H%M%S")$(date +"%N" | cut -b 1-3)
data_split=test
sample_num=32
data_path=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
# data_path=/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f_sanity.jsonl
while getopts ":d:m:s:n:" opt; do
  case $opt in
    d) data_path="$OPTARG"
    ;;
    m) model_path="$OPTARG"
    ;;
    s) data_split="$OPTARG"
    ;;
    n) sample_num="$OPTARG"
    ;;
  esac
done
last_model_path=$(echo "$model_path" | awk -F'/' '{print $NF}')
log_dir=results/minif2f/${last_model_path}_${time_step}_pass${sample_num}

python -m prover.launch  --log_dir=$log_dir --model_path=$model_path --data_path=$data_path --data_split=$data_split --sample_num $sample_num
python scripts_eval/step3_summarize.py --input_path=$log_dir
