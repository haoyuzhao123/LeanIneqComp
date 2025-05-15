#!/bin/bash
#SBATCH --job-name=inference # create a short name for your job
#SBATCH --nodes=1                # node count
#SBATCH --ntasks=1               # total number of tasks across all nodes
#SBATCH --cpus-per-task=32        # cpu-cores per task (>1 if multi-threaded tasks)
#SBATCH --mem-per-cpu=10G         # memory per cpu-core (4G is default)
#SBATCH --gres=gpu:2        # number of gpus per node
#SBATCH --time=23:00:00          # total run time limit (HH:MM:SS)
#SBATCH --mail-type=FAIL
#SBATCH --mail-user=haoyu@princeton.edu
#SBATCH --partition=pli-c
#SBATCH --output=slurm/%x-%j.out

##### #SBATCH --qos=pli-cp

source /scratch/gpfs/haoyu/miniconda3/etc/profile.d/conda.sh
conda activate skillmixlean

export LD_LIBRARY_PATH=/scratch/gpfs/haoyu/miniconda3/lib:$LD_LIBRARY_PATH

export HF_HOME=/scratch/gpfs/haoyu/cache/

python -m prover.launch --config=configs/RMaxTS.py --log_dir=logs/RMaxTS_results_another