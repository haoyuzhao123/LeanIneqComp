# Lean 4 Benchmark for Inequalities

## Structure of the folder
+ full.jsonl : final benchmark file
+ full_answer/ : this folder contains all the lean 4 code for problems in full.jsonl
+ maybe some jsonl corresponding to different category
+ xxx-haoyu.jsonl : problems / files currently working by Haoyu
+ xxx_answer-haoyu/ : folder contains lean 4 code for problems currently working by Haoyu

## Structure of the benchmark
Here we summarize some type of the problems in the benchmark
+ basic: very basic ineq., including but not limited to: sqrt{x} <= 1 leads to x <= 1.
+ sum of square:
+ AM-GM:
+ Cauchy-Schwatz:
+ Derivative: i feel like it is very important
+ Lagrange mean value: this is also important for some inequalities related to integral (e.g., estimate sum 1/sqrt{n} or sum 1/n or sum a_i / sum_{j\le i}a_j)

After we have some problems for each category, we can then work on perturbing the problems, which includes but not limited to:
+ add more variable
+ substitue variable to other form (a -> a^2, a -> 1/a)
+ combine two things together (e.g., f(x) >= 2, g(y) >= 2, f(x) * g(y) >= 4)