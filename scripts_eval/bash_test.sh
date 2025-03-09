for i in {1..50}; do
    sbatch scripts_eval/compile_summarize_test.sh -i /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/translator/test/to_inference_codes_times15.json -o /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/results/translator/test/test_compilation${i}
done
