<div align="center">
    <h1> <a href="https://arxiv.org">Ineq-Comp: Benchmarking Human-Intuitive Compositional Reasoning in Automated Theorem Proving on Inequalities</a></h1>
</div>

<div align="center">

[![Hugging Face](https://img.shields.io/badge/-HuggingFace-3B4252?logo=huggingface)](https://huggingface.co/datasets/zzzzzhy/Ineq-Comp)
[![arXiv](https://img.shields.io/badge/arXiv-2505.12680-b31b1b.svg?style=flat)](https://arxiv.org/abs/2505.12680)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Email me](https://img.shields.io/badge/Contact-6fcf97?logo=gmail)](mailto:thomaszhao1998@gmail.com)

</div>

## 1. Introduction

We introduce Ineq-Comp, a benchmark built from elementary inequalities through systematic transformations, including variable duplication, algebraic rewriting, and multi-step composition. Although these problems remain easy for humans, we find that most provers&mdash;including Goedel, STP, and Kimina-7B&mdash;struggle significantly. DeepSeek-Prover-V2 shows relative robustness&mdash;possibly because it is trained to decompose the problems into sub-problems&mdash;but still suffers a 20\% performance drop (pass@32). Strikingly, performance remains poor for all models even when formal proofs of the constituent parts are provided in context, revealing that the source of weakness  is indeed in compositional reasoning. Our results expose a persisting gap between the generalization behavior of current AI provers and human mathematical intuition. 

<div>
  <img width="30%" src=assets/fig-problem.png>
  <img width="30%" src=assets/fig-acc.png>
  <img width="30%" src=assets/fig-ratio.png>
</div>

## 2. Environment Setup

### Lean 4 Environment

The Lean 4 environment and the corresponding Mathlib version used in this project follow from [DeepSeek-Prover-V1.5](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5). Please first install the correct Lean 4 and Mathlib version following the [environment setup guide](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5/blob/main/README.md#4-setup-environment).

### Copy Data and Testing Scripts

After installing the corresponding Lean 4 environment, please copy the `benchmark/` and `scripts_eval/` folder to the parent folder where you build your Mathlib. You should get the following file strueture (only show the important folders).

```text
parent_folder/
├── benchmark/
├── configs/
├── mathlib4/
├── prover/
└── scripts_eval/
```

## 3. Quick Start

### General-Purpose Models

Please run the following command to test DeepSeek-R1-Distill-Qwen-32B without the thinking block (chat template) under pass@32. This will test the model on the 25 seed problems from Ineq-AMGM.

```sh
bash scripts_eval/inference_2gpu.sh -i benchmark/amgm_seed.jsonl -m deepseek-ai/DeepSeek-R1-Distill-Qwen-32B -o results/amgm_seed_r1-distill-qwen-32b_nothink -n 32
```

The script will: (1) inference using VLLM and extract the Lean code (need 2 gpus); (2) submit the code to REPL and verified by Lean 4 compiler. (no gpu needed)

For DeepSeek-R1-Distill-Qwen-32B with the thinking block, please run

```sh
bash scripts_eval/inference_think_2gpu.sh -i benchmark/amgm_seed.jsonl -m deepseek-ai/DeepSeek-R1-Distill-Qwen-32B -o results/amgm_seed_r1-distill-qwen-32b -n 32
```

### Whole-Proof Generation Methods

To test DeepSeek-Prover-V1.5-RL, Goedel-Prover-SFT, STP, please using the script that test DeepSeek-R1-Distill-Qwen-32B without the thinking block while changing the model to your target model (taking STP as an example).

```sh
bash scripts_eval/inference_2gpu.sh -i benchmark/amgm_seed.jsonl -m kfdong/STP_model_Lean -o results/amgm_seed_stp -n 32
```

For Kimina-Prover-Preview-Distill-7B, please run the following script

```sh
bash scripts_eval/inference_kimina_2gpu.sh -i benchmark/amgm_seed.jsonl -m AI-MO/Kimina-Prover-Preview-Distill-7B -o results/amgm_seed_kimina-7b -n 32
```

For DeepSeek-Prover-V2-7B, please run the following script

```sh
bash scripts_eval/inference_dsprover2_2gpu.sh -i benchmark/amgm_seed.jsonl -m deepseek-ai/DeepSeek-Prover-V2-7B -o results/amgm_seed_dsprover2-7b -n 32
```

The main logic under all these scripts is very similar, and the difference between different scirpts (for DeepSeek-R1-Distill-Qwen-32B, Kimina-Prover-Preview-Distill-7B, and DeepSeek-Prover-V2-7B) is the prompt and the response template.

Note 1: all the scripts can be technically run with 2 H100 80GB GPUs. However, we recommend to use 4 H100 80GB GPUs when testing DeepSeek-R1-Distill-Qwen-32B, Kimina-Prover-Preview-Distill-7B, and DeepSeek-Prover-V2-7B, especially if you want to test with more than 16K generation length, since for some VLLM versions it might cause GPU OOM with only 2 gpus.

Note 2: we highly recommend splitting the job into smaller ones, especially when testing DeepSeek-R1-Distill-Qwen-32B, Kimina-Prover-Preview-Distill-7B, and DeepSeek-Prover-V2-7B or testing models under high budget (pass@3200). We include the SLURM head in each scripts for better parallelization with more GPU resources, please refer to the scripts for more details.


### DeepSeek-Prover-V1.5-RL+RMaxTX

The experiments for DeepSeek-Prover-V1.5-RL+RMaxTX can be reproduced using exactly the same command in the original DeepSeek-Prover-V1.5 repo, by changing the dataset to the benchmark dataset (`benchmark/amgm_seed.jsonl`) in configs/RMaxTS.py file:

```sh
python -m prover.launch --config=configs/RMaxTS.py --log_dir=logs/RMaxTS_results
```

Please refer to [DeepSeek-Prover-V1.5](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5/tree/main#5-quick-start) codebase for more details.

### InternLM2.5-StepProver+BF

The evaluation code is based on the [InternLM Github Repo](https://github.com/InternLM/InternLM-Math/tree/main), and particularly, the [evaluation code](https://github.com/InternLM/InternLM-Math/tree/main/minif2f) for MiniF2F, with only minimal modifications. Please follow the repo to install the correct Lean 4 and other corresponding package version, especially LeanDojo.

After installing the corresponding environment, please substitute the MiniF2F by the <a href="https://github.com/haoyuzhao123/LeanIneqComp-Dojo">
    <img
      src="https://github.githubassets.com/images/modules/logos_page/GitHub-Mark.png"
      alt="GitHub"
      width="20"
      style="vertical-align: middle; margin-right: 4px;"
    />
    LeanIneqComp-Dojo
  </a>, which is the Github Repo of Ineq-Comp tracable by Leandojo and adapted to the Lean 4 version used by InternLM2.5-StepProver.


## 4. Ineq-Comp Benchmark
All the data of our Ineq-Comp benchmark, including the proofs of the seed problems, can be found in the `benchmark` folder, and is also available on [<img src="https://huggingface.co/front/assets/huggingface_logo-noborder.svg" alt="Hugging Face" width="20" style="vertical-align: text-bottom;"/> Huggingface](https://huggingface.co/datasets/zzzzzhy/Ineq-Comp).

For Ineq-Simp, which contains Ineq-AMGM, Ineq-Cauchy, and Ineq-MISC, the questions can be found at `benchmark/amgm_*.jsonl`, `benchmark/cauchy_*.jsonl`, and `benchmark/misc_*.jsonl`.

`benchmark/comp2_100.jsonl` contains 100 inequality problems generated using Ineq-Mix by randomly composing two seed problems from Ineq-Simp.

`benchmark/real.jsonl` contains 50 real-world inequality problems.

The proof for the 75 seed problems can be found in `benchmark/full_answer/` folder. We include the proof for two Lean 4 versions: 4.9, where our main experiments are based on (which is also the version used by DeepSeek-Prover-V1.5), and 4.18, which is the Lean 4 version (stable) used by the [interactive Lean 4 web](https://live.lean-lang.org/) at the time this benchmark is curated.

## 5. Custom Problem Generation through Ineq-Mix

Our Ineq-Mix framework that can generates more problems (given a pool of base problem) can be found in the `composition/` folder.

`original_problems.jsonl` includes 65 seed problems that can be possibly composed or transformed. The composition rules, the variable-level algebraic transformation rules, and the problem-level algebraic transformation rules are defined in `composition/comp_op.py`, `composition/algebraic_op.py`, and `composition/algebraic_whole_op.py`, respectively. Please refer to `composition/mix.py` for more details.


## 6. Evaluation Results

### General-Purpose Models
| Method                                          | Budget | AM-GM Seed         | AM-GM I            | AM-GM II           | Cauchy Seed        | Cauchy I           | Cauchy II          | Misc Seed          | Misc I             | Misc II            |
| ----------------------------------------------- | ------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ |
| **DeepSeek-R1-Distill-Qwen-32B (w/o thinking)** | 32     | 48.2<sub>1.9</sub> | 3.5<sub>3.3</sub>  | 16.2<sub>3.0</sub> | 28.0<sub>3.3</sub> | 17.0<sub>3.2</sub> | 15.0<sub>3.0</sub> | 41.4<sub>3.7</sub> | 13.4<sub>4.5</sub> | 15.4<sub>4.4</sub> |
|                                                 | 64     | 49.0<sub>1.7</sub> | 6.5<sub>4.1</sub>  | 18.4<sub>2.4</sub> | 30.6<sub>3.2</sub> | 19.5<sub>2.8</sub> | 16.8<sub>2.7</sub> | 44.5<sub>3.2</sub> | 17.7<sub>4.0</sub> | 20.2<sub>4.8</sub> |
|                                                 | 128    | 49.9<sub>2.0</sub> | 10.6<sub>4.2</sub> | 20.0<sub>2.5</sub> | 32.6<sub>2.9</sub> | 21.8<sub>3.2</sub> | 19.0<sub>2.6</sub> | 47.4<sub>3.1</sub> | 21.1<sub>3.7</sub> | 25.4<sub>4.2</sub> |
|                                                 | 3200   | 52.0               | 40.0               | 36.0               | 44.0               | 32.0               | 28.0               | 52.0               | 36.0               | 36.0               |
| **DeepSeek-R1-Distill-Qwen-32B (w thinking)**   | 32     | 48.8<sub>1.6</sub> | 10.9<sub>3.8</sub> | 21.1<sub>3.1</sub> | 42.9<sub>2.5</sub> | 27.0<sub>3.4</sub> | 18.4<sub>2.4</sub> | 50.5<sub>2.3</sub> | 18.9<sub>4.6</sub> | 22.0<sub>4.0</sub> |
|                                                 | 64     | 49.5<sub>1.9</sub> | 14.5<sub>4.4</sub> | 23.0<sub>3.4</sub> | 44.5<sub>2.4</sub> | 30.3<sub>2.9</sub> | 20.6<sub>2.3</sub> | 51.9<sub>0.6</sub> | 23.7<sub>4.9</sub> | 26.2<sub>3.1</sub> |
|                                                 | 128    | 50.9<sub>2.1</sub> | 19.2<sub>4.1</sub> | 26.1<sub>4.3</sub> | 46.2<sub>2.3</sub> | 32.6<sub>2.7</sub> | 22.1<sub>2.0</sub> | 52.0<sub>0.0</sub> | 28.0<sub>3.9</sub> | 29.4<sub>2.7</sub> |
|                                                 | 3200   | 60.0               | 44.0               | 44.0               | 56.0               | 40.0               | 24.0               | 52.0               | 36.0               | 40.0               |

### Whole-Proof Generation Methods
| Method                               | Budget | AM-GM Seed         | AM-GM I            | AM-GM II           | Cauchy Seed        | Cauchy I           | Cauchy II          | Misc Seed          | Misc I             | Misc II            |
| ------------------------------------ | ------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ |
| **DeepSeek-Prover-V1.5-RL**          | 32     | 48.1<sub>3.0</sub> | 0.0<sub>0.4</sub>  | 8.2<sub>1.5</sub>  | 14.9<sub>3.2</sub> | 2.9<sub>1.8</sub>  | 4.4<sub>1.4</sub>  | 40.2<sub>2.8</sub> | 12.4<sub>1.1</sub> | 12.2<sub>2.5</sub> |
|                                      | 64     | 50.6<sub>2.9</sub> | 0.1<sub>0.6</sub>  | 9.0<sub>1.7</sub>  | 17.0<sub>2.7</sub> | 3.7<sub>1.1</sub>  | 5.0<sub>1.9</sub>  | 42.1<sub>2.3</sub> | 12.7<sub>1.7</sub> | 13.8<sub>2.9</sub> |
|                                      | 128    | 52.2<sub>2.1</sub> | 0.2<sub>0.8</sub>  | 9.8<sub>2.0</sub>  | 18.7<sub>2.7</sub> | 4.0<sub>0.0</sub>  | 6.1<sub>2.3</sub>  | 43.2<sub>1.6</sub> | 13.3<sub>2.2</sub> | 16.2<sub>2.9</sub> |
|                                      | 3200   | 60.0               | 4.0                | 24.0               | 24.0               | 4.0                | 12.0               | 44.0               | 20.0               | 28.0               |
| **Goedel-Prover-SFT**                | 32     | 48.6<sub>2.9</sub> | 0.4<sub>1.2</sub>  | 14.0<sub>3.2</sub> | 34.8<sub>2.5</sub> | 12.4<sub>3.5</sub> | 21.5<sub>3.4</sub> | 47.0<sub>1.7</sub> | 14.4<sub>3.1</sub> | 24.6<sub>1.9</sub> |
|                                      | 64     | 50.6<sub>2.6</sub> | 0.8<sub>1.6</sub>  | 16.6<sub>2.8</sub> | 36.2<sub>1.9</sub> | 15.8<sub>3.4</sub> | 24.6<sub>2.9</sub> | 47.8<sub>0.9</sub> | 16.6<sub>2.5</sub> | 25.5<sub>1.9</sub> |
|                                      | 128    | 52.2<sub>1.4</sub> | 1.3<sub>1.9</sub>  | 18.6<sub>2.2</sub> | 37.1<sub>1.8</sub> | 19.4<sub>2.9</sub> | 26.9<sub>1.8</sub> | 48.0<sub>0.0</sub> | 17.9<sub>2.6</sub> | 26.4<sub>2.5</sub> |
|                                      | 3200   | 60.0               | 4.0                | 24.0               | 40.0               | 32.0               | 28.0               | 48.0               | 24.0               | 36.0               |
| **STP (w/o miniF2F valid)**          | 32     | 59.1<sub>1.9</sub> | 14.3<sub>4.4</sub> | 23.2<sub>4.5</sub> | 35.2<sub>2.4</sub> | 14.6<sub>2.7</sub> | 16.0<sub>2.6</sub> | 55.6<sub>1.3</sub> | 12.6<sub>5.0</sub> | 27.6<sub>3.6</sub> |
|                                      | 64     | 60.1<sub>0.6</sub> | 18.5<sub>4.1</sub> | 28.2<sub>4.6</sub> | 36.8<sub>2.4</sub> | 16.7<sub>2.8</sub> | 17.3<sub>2.7</sub> | 56.0<sub>0.0</sub> | 17.8<sub>4.9</sub> | 31.0<sub>4.1</sub> |
|                                      | 128    | 60.3<sub>1.1</sub> | 24.3<sub>4.1</sub> | 33.0<sub>3.6</sub> | 37.9<sub>2.6</sub> | 18.4<sub>3.0</sub> | 18.9<sub>3.3</sub> | 56.0<sub>0.0</sub> | 24.0<sub>4.4</sub> | 33.9<sub>4.1</sub> |
|                                      | 3200   | 64.0               | 44.0               | 40.0               | 44.0               | 24.0               | 28.0               | 56.0               | 36.0               | 40.0               |
| **Kimina-Prover-Preview-Distill-7B** | 32     | 59.4<sub>4.1</sub> | 11.7<sub>5.4</sub> | 45.2<sub>3.7</sub> | 46.9<sub>4.5</sub> | 27.0<sub>2.6</sub> | 27.7<sub>3.3</sub> | 44.2<sub>1.3</sub> | 18.1<sub>3.9</sub> | 35.8<sub>2.0</sub> |
|                                      | 64     | 64.1<sub>4.6</sub> | 19.4<sub>5.9</sub> | 48.6<sub>2.4</sub> | 52.7<sub>4.3</sub> | 28.8<sub>2.5</sub> | 30.2<sub>2.8</sub> | 44.6<sub>1.4</sub> | 22.3<sub>2.9</sub> | 36.8<sub>2.0</sub> |
|                                      | 128    | 69.4<sub>4.2</sub> | 28.2<sub>5.4</sub> | 50.6<sub>2.2</sub> | 57.6<sub>3.6</sub> | 30.4<sub>3.0</sub> | 32.0<sub>1.6</sub> | 45.1<sub>1.8</sub> | 25.6<sub>2.5</sub> | 37.6<sub>2.5</sub> |
|                                      | 3200   | 80.0               | 44.0               | 64.0               | 68.0               | 52.0               | 36.0               | 52.0               | 32.0               | 44.0               |
| **DeepSeek-Prover-V2-7B**            | 32     | 75.0<sub>4.4</sub> | 58.6<sub>4.0</sub> | 52.5<sub>4.5</sub> | 64.6<sub>4.1</sub> | 33.0<sub>2.3</sub> | 35.0<sub>2.3</sub> | 59.1<sub>2.9</sub> | 49.3<sub>3.4</sub> | 38.8<sub>4.4</sub> |
|                                      | 64     | 80.7<sub>5.3</sub> | 62.1<sub>4.5</sub> | 57.4<sub>4.0</sub> | 68.3<sub>3.1</sub> | 34.7<sub>2.7</sub> | 36.6<sub>2.3</sub> | 61.7<sub>2.5</sub> | 51.6<sub>2.9</sub> | 43.7<sub>4.2</sub> |
|                                      | 128    | 85.8<sub>5.4</sub> | 65.9<sub>5.3</sub> | 61.4<sub>3.7</sub> | 71.0<sub>2.0</sub> | 36.3<sub>3.6</sub> | 37.9<sub>2.6</sub> | 64.0<sub>1.6</sub> | 53.3<sub>3.1</sub> | 49.9<sub>4.3</sub> |
|                                      | 3200   | 96.0               | 84.0               | 76.0               | 76.0               | 52.0               | 48.0               | 68.0               | 64.0               | 64.0               |

### Tree-Search Methods
| Method                               | Budget    | AM-GM Seed         | AM-GM I           | AM-GM II           | Cauchy Seed        | Cauchy I           | Cauchy II          | Misc Seed          | Misc I             | Misc II            |
| ------------------------------------ | --------- | ------------------ | ----------------- | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ |
| **DeepSeek-Prover-V1.5-RL + RMaxTS** | 1×3200    | 60.0<sub>0.0</sub> | 3.0<sub>1.7</sub> | 22.0<sub>2.0</sub> | 24.0<sub>0.0</sub> | 8.0<sub>2.8</sub>  | 13.0<sub>3.3</sub> | 44.0<sub>0.0</sub> | 14.0<sub>3.5</sub> | 29.0<sub>1.7</sub> |
|                                      | 2×3200    | 60.0<sub>0.0</sub> | 6.0<sub>2.0</sub> | 26.0<sub>2.0</sub> | 24.0<sub>0.0</sub> | 10.0<sub>2.0</sub> | 16.0<sub>0.0</sub> | 44.0<sub>0.0</sub> | 16.0<sub>4.0</sub> | 32.0<sub>0.0</sub> |
|                                      | 4×3200    | 60.0               | 8.0               | 28.0               | 24.0               | 12.0               | 20.0               | 44.0               | 20.0               | 36.0               |
| **InternLM2.5-StepProver + BF**      | 1×32×600  | 30.8<sub>3.1</sub> | 0.0<sub>0.0</sub> | 2.5<sub>3.1</sub>  | 12.0<sub>0.0</sub> | 0.0<sub>0.0</sub>  | 1.2<sub>1.9</sub>  | 34.0<sub>2.0</sub> | 2.2<sub>2.0</sub>  | 17.0<sub>3.9</sub> |
|                                      | 4×32×600  | 38.0<sub>4.5</sub> | 0.0<sub>0.0</sub> | 9.0<sub>3.3</sub>  | 12.0<sub>0.0</sub> | 0.0<sub>0.0</sub>  | 3.0<sub>1.7</sub>  | 36.0<sub>0.0</sub> | 5.0<sub>1.7</sub>  | 21.0<sub>1.7</sub> |
|                                      | 16×32×600 | 44.0               | 0.0               | 24.0               | 12.0               | 0.0                | 4.0                | 36.0               | 8.0                | 24.0               |




## 7. Citation

If you find our work helps, please consider starring ⭐ us and citing:

```{bibtex}
@article{zhao2025ineq,
  title={Ineq-Comp: Benchmarking Human-Intuitive Compositional Reasoning in Automated Theorem Proving on Inequalities},
  author={Zhao, Haoyu and Geng, Yihan and Tang, Shange and Lin, Yong and Lyu, Bohan and Lin, Hongzhou and Jin, Chi and Arora, Sanjeev},
  journal={arXiv preprint arXiv:2505.12680},
  year={2025}
}
```
