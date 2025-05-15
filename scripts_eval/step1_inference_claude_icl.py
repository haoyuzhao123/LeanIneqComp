import re
import os
from transformers import AutoTokenizer
import anthropic

import json
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--input_path',  type=str)
parser.add_argument('--icl_folder',  type=str, default="/scratch/gpfs/haoyu/Deepseek/datasets/amgm_valid")
parser.add_argument('--model_path', type=str)
parser.add_argument('--output_dir',  type=str)
parser.add_argument('--split', default="none", type=str)
parser.add_argument('--n', default=2, type=int)
parser.add_argument('--gpu', default=1, type=int)
parser.add_argument('--seed', default=1, type=int)

args = parser.parse_args()

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

full_code_list = []
if "amgm" in args.icl_folder:
    for i in range(1,26):
        fn_single = f"amgm_p{i}.lean"
        fn = os.path.join(icl_folder, fn_single)
        full_code_list.append(read_lean(fn))
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
        full_code_list.append(read_lean(fn))
else:
    raise ValueError("Not implemented ICL folder")

if "claude-3-5-haiku-20241022" or "claude-3-7-sonnet-20250219" in args.model_path:
    client = anthropic.Anthropic(
    # defaults to os.environ.get("ANTHROPIC_API_KEY")
    api_key="YOUR-CLAUDE-API",
)

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

model_inputs = []
model_outputs = []

token_count_total_input = 0
token_count_total_output = 0

assert len(full_code_list) == len(data_list), "length mismatch for icl and inputs"


for data, icl_code in zip(data_list, full_code_list):
    max_retries = 999
    retry_count = 0
    
    prompt = "Give a proof for the following problem written in lean 4:\n\n```lean4\n{header}{informal_prefix}{formal_statement}```.\n\nFollowing is the solution for a related problem written in Lean 4. You can fully trust the provided code and it has already passed the Lean 4 compilation.\n{icl_code}\n\nPlease follow the provided code such that you don't make more mistakes. Your code should be self-contained, i.e., you should first prove the provided example inside your whole proof (not as a separate theorem outside the proof of the problem) if you want to use the result. You should wrap your answer in the lean code block\n\n```lean4\n<You answer>\n```".format(
            header=data.get('header', LEAN4_DEFAULT_HEADER),
            informal_prefix=data.get('informal_prefix', str()),
            formal_statement=data['formal_statement'],
            icl_code=icl_code,
        )
    model_inputs.append(prompt)
    answer_list = []
    for i in range(args.n):
        while retry_count < max_retries:
            try:
                message = client.messages.create(
                    model=args.model_path,
                    max_tokens=8192,
                    messages=[
                        {"role": "user", "content": prompt}
                    ]
                )
                num_input_tokens = message.usage.input_tokens
                num_output_tokens = message.usage.output_tokens
                token_count_total_input += num_input_tokens
                token_count_total_output += num_output_tokens
                if args.model_path == "claude-3-5-haiku-20241022":
                    ic = 0.8 * 0.001 * 0.001
                    oc = 4.0 * 0.001 * 0.001
                    tc = ic * token_count_total_input + oc * token_count_total_output
                    print(f"total cost so far: {tc}")
                elif args.model_path == "claude-3-7-sonnet-20250219":
                    ic = 3 * 0.001 * 0.001
                    oc = 15.0 * 0.001 * 0.001
                    tc = ic * token_count_total_input + oc * token_count_total_output
                    print(f"total cost so far: {tc}")

                response = message.content[0].text
                #print(response)
                answer_list.append(response)
                break
                
            except Exception as e:
                print(e)
                retry_count += 1
                if retry_count == max_retries:
                    print(f"API failure, retried {max_retries} times. Error: {str(e)}")

                    raise e
                print(f"API failure, retrying for {retry_count} time...")
    model_outputs.append(answer_list)
    

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
    data_list[i]["model_outputs"] = [output for output in model_outputs[i]]
    #change the following
    data_list[i]["full_code"] = [(extrac_code(output)) for output in model_outputs[i]]
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
