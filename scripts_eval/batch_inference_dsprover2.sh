for SEED in {1..4}; do
    N=32
    sbatch scripts_eval/inference_dsprover2_2gpu.sh -n $N -d $SEED
done