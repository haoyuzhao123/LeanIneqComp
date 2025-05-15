for SEED in {33..64}; do
    N=2
    sbatch scripts_eval/inference_icl_randomcomp_2gpu.sh -n $N -d $SEED
done
