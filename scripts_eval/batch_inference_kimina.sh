for SEED in {1..8}; do
    N=128
    sbatch scripts_eval/inference_kimina_2gpu.sh -n $N -d $SEED
done