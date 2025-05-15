import re
import os
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams

import json
import argparse

parser = argparse.ArgumentParser()
# /scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl
parser.add_argument('--input_path',  type=str)
parser.add_argument('--icl_folder',  type=str, default="/scratch/gpfs/haoyu/Deepseek/datasets/amgm_valid")
# /scratch/gpfs/yl7690/models/DeepSeek-Prover-V1.5-RL
parser.add_argument('--model_path', type=str)
# results/test
parser.add_argument('--output_dir',  type=str)
parser.add_argument('--split', default="none", type=str)
parser.add_argument('--n', default=32, type=int)
parser.add_argument('--gpu', default=1, type=int)
parser.add_argument('--seed', default=1, type=int)


# parser.add_argument('--output_path', default="example_data/o1_sorried_output.json", type=str)
args = parser.parse_args()


# data_path = "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f_sanity10.jsonl"
data_path = args.input_path
# Initialize an empty list to hold the dictionaries
data_list = []

icl_folder = args.icl_folder

def read_lean(filename):
    with open(filename, "r") as f:
        lines = f.readlines()
    code = ''.join(lines)
    full_code_block = f"\n\n```lean4\n{code}\n```"
    return full_code_block

full_code_dict = {}
if "amgm" in args.icl_folder:
    for i in range(1,26):
        fn_single = f"amgm_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_dict[f"amgm_p{i}"] = read_lean(fn)
        """
elif "misc" in args.icl_folder:
    for i in range(1,11):
        fn_single = f"jensen_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_list.append(read_lean(fn))
    for i in range(1,6):
        fn_single = f"induction_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_list.append(read_lean(fn))
    for i in range(1,6):
        fn_single = f"schur_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_list.append(read_lean(fn))
    for i in range(1,6):
        fn_single = f"sq_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_list.append(read_lean(fn))
elif "cauchy" in args.icl_folder:
    for i in range(1,26):
        fn_single = f"cauchy_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_list.append(read_lean(fn))"
        """
else:
    raise ValueError("Not implemented ICL folder")



# Open the file and read each line
with open(data_path, 'r') as file:
    for line in file:
        # Parse the JSON object and append it to the list
        # if data_split is not None and prob['split'] not in data_split:
        #     continue
        data = json.loads(line)
        # if (data["split"] == args.split) or (args.split == "none"):
        #     data_list.append(data)
        if args.split == "none":
            data_list.append(data)
        else:
            try:
                int_split = int(args.split)
            except:
                int_split = None
                pass
            if isinstance(int_split, int):
                if (int(data["split"]) == int(args.split)):
                    data_list.append(data)
            else:
                if ((data["split"]) == (args.split)):
                    data_list.append(data)

LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

SYSTEM_PROMPT = "Your role as an assistant involves thoroughly exploring questions through a systematic long \
        thinking process before providing the final precise and accurate solutions. This requires \
        engaging in a comprehensive cycle of analysis, summarizing, exploration, reassessment, reflection, \
        backtracing, and iteration to develop well-considered thinking process. \
        Please structure your response into two main sections: Thought and Solution. \
        In the Thought section, detail your reasoning process using the specified format: \
        <|begin_of_thought|> {thought with steps separated with '\n\n'} \
        <|end_of_thought|> \
        Each step should include detailed considerations such as analisying questions, summarizing \
        relevant findings, brainstorming new ideas, verifying the accuracy of the current steps, refining \
        any errors, and revisiting previous steps. \
        In the Solution section, based on various attempts, explorations, and reflections from the Thought \
        section, systematically present the final solution that you deem correct. The solution should \
        remain a logical, accurate, concise expression style and detail necessary step needed to reach the \
        conclusion, formatted as follows: \
        <|begin_of_solution|> \
        {final formatted, precise, and clear solution} \
        <|end_of_solution|> \
        Now, try to solve the following question through the above guidelines:"

model_name = args.model_path
# model_name = "/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/models/Translator_Qwen2.5-Coder-32B_numina_sonnet_130K_translator_Epoch2_LR1e-4"
tokenizer = AutoTokenizer.from_pretrained(model_name)
# model = LLM(model=model_name, max_num_batched_tokens=8192, seed=1, trust_remote_code=True, swap_space=8, tensor_parallel_size=args.gpu)
model = LLM(model=model_name, seed=args.seed, trust_remote_code=True, swap_space=8, tensor_parallel_size=args.gpu, max_model_len=32768)


sampling_params = SamplingParams(
    temperature=1.0,
    max_tokens=32768,
    top_p=0.95,
    n=args.n,
)

model_inputs = []
#assert len(full_code_list) == len(data_list), "length mismatch for icl and inputs"
for data in data_list:
    # model_inputs.append("Complete the following Lean 4 code with explanatory comments preceding each line of code:\n\n```lean4\n{header}\n/-{informal_prefix}-/ \n{formal_statement}".format(
    original_problems=data["original_problems"].split(',')
    icl_code = '\n\n'.join([full_code_dict[n] for n in original_problems])
    prompt = "Give a proof for the following problem written in lean 4:\n\n```lean4\n{header}{informal_prefix}{formal_statement}```.\n\nFollowing are the solutions for some related problems written in Lean 4. You can fully trust the provided code and it has already passed the Lean 4 compilation.\n{icl_code}\n\nPlease follow the provided code such that you don't make more mistakes. Your code should be self-contained, i.e., you should first prove the provided example inside your whole proof (not as a separate theorem outside the proof of the problem) if you want to use the result. You should wrap your answer in the lean code block\n\n```lean4\n<You answer>\n```".format(
            header=data.get('header', LEAN4_DEFAULT_HEADER),
            informal_prefix=data.get('informal_prefix', str()),
            formal_statement=data['formal_statement'],
            icl_code=icl_code,
        )
    messages = [
        #{"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": prompt}
    ]
    text = tokenizer.apply_chat_template(
        messages,
        tokenize=False,
        add_generation_prompt=True
    )
    #text = prompt
    model_inputs.append(text)

model_outputs = model.generate(
    model_inputs,
    sampling_params,
    use_tqdm=True,
)

assert len(model_outputs) == len(model_inputs)

def extrac_code(inputs):
    try:
        return re.search(r'```lean4\n(.*?)\n```', inputs, re.DOTALL).group(1)
    except:
        try:
            return re.search(r'```lean4\n(.*)', inputs, re.DOTALL).group(1)
        except:
            return "None"

to_inference_codes = []
for i in range(len(data_list)):
    data_list[i]["model_input"] = model_inputs[i]
    data_list[i]["model_outputs"] = [output.text for output in model_outputs[i].outputs]
    #change the following
    if "r1-distill" in model_name:
        data_list[i]["full_code"] = [(LEAN4_DEFAULT_HEADER+extrac_code(output.text)) for output in model_outputs[i].outputs]
    else:
        data_list[i]["full_code"] = [extrac_code(output.text) for output in model_outputs[i].outputs]
    if "problem_id" in data_list[i]:
        to_inference_codes += [{"name": data_list[i]["problem_id"], "code": code} for code in data_list[i]["full_code"]]
    else:
        to_inference_codes += [{"name": data_list[i]["name"], "code": code} for code in data_list[i]["full_code"]]

import os
os.makedirs(args.output_dir, exist_ok=True)

output_file_path = F'{args.output_dir}/full_records.json'
print(F"Outputing to {output_file_path}")
# Dump the list to a JSON file with indents
with open(output_file_path, 'w') as json_file:
    json.dump(data_list, json_file, indent=4)

toinfer_file_path = F'{args.output_dir}/to_inference_codes.json'
print(F"Outputing to {toinfer_file_path}")
# Dump the list to a JSON file with indents
with open(toinfer_file_path, 'w') as json_file:
    json.dump(to_inference_codes, json_file, indent=4)
# for data
#     model_outputs[0].outputs[0].text
