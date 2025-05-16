import pandas as pd
import numpy as np
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--input_path',  type=str)
parser.add_argument('--output_path',  type=str)
parser.add_argument('--field', default="complete",choices=["complete", "pass"], type=str)
args = parser.parse_args()


input_file= args.input_path
df = pd.read_json(input_file)

df["correct"] = df.compilation_result.apply(lambda x: x[args.field])

df_grp = df.groupby("name")["correct"].sum() 

result = {
  "total": len(df_grp),
  "correct": sum(df_grp > 0),
  "accuracy": F"{sum(df_grp > 0) / len(df_grp)  * 100:.2f}",
  "field": args.field
}
import json
with open(args.output_path, "w") as f:
    json.dump(result, f)

#
df_grp.reset_index()[["name", "correct"]].to_csv(args.output_path.replace(".json", ".csv"), index=False, header=True, sep='\t', quoting=1, na_rep='Missing')

