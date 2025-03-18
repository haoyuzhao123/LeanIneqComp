import os
import argparse

import pandas as pd
from termcolor import colored

from prover.utils import get_datetime, load_config, load_jsonl_objects


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=str)
    parser.add_argument("--log_dir", type=str)
    parser.add_argument("--model_path", type=str, default="")
    parser.add_argument("--data_path", type=str, default="", help="for example, val:test, split by ':'. ")
    parser.add_argument("--data_split", type=str, default="")
    args = parser.parse_args()

    cfg = load_config(args.config)
    if len(args.model_path) > 0:
        cfg.model_path = args.model_path
    if len(args.data_path) > 0:
        cfg.data_path = args.data_path
    if len(args.data_split) > 0:
        cfg.data_split = args.data_split.split(":")
    dataset = load_jsonl_objects(cfg.data_path)
    log_dir_dict = {
        os.path.basename(args.log_dir): args.log_dir,
    }

    for data in dataset:
        data['success'] = dict()
    for runname, log_dir in log_dir_dict.items():
        for prob_idx, data in enumerate(dataset):
            res_dir = os.path.join(log_dir, f'{prob_idx}_{dataset[prob_idx]["name"]}')
            _success_flag = False
            if os.path.exists(res_dir):
                for filename in os.listdir(res_dir):
                    if filename[:7] == 'success':
                        _success_flag = True
            data['success'][runname] = _success_flag
    
    def make_inner_list(info):
        return {key: [val] for key, val in info.items()}
    
    def add_color(info):
        return {key: colored(val, 'cyan', attrs=['bold']) for key, val in info.items()} if info['prob_type'] == '<all>' else info

    def aggregate(split, prob_type):
        info = dict(split=split, prob_type=prob_type)
        for runname in log_dir_dict:
            success_count, total_count = 0, 0
            for prob_idx, data in enumerate(dataset):
                if data['split'] == split and (data['name'].startswith(prob_type) or prob_type == '<all>'):
                    total_count += 1
                    success_count += int(data['success'][runname])
            info[runname] = '{:3d} / {:3d} = {:.3f}'.format(success_count, total_count, success_count / total_count)
            info["success_count"] = success_count
            info["total_count"] = total_count
        return (info)
    
    summary = pd.DataFrame([
        aggregate(split, '<all>')
        for split in set(cfg.data_split)
    ])
    print('DateTime:', get_datetime(readable=True))
    # print(summary.to_markdown(index=False, tablefmt="github", colalign=["left"] * 2 + ["right"] * len(log_dir_dict)))
    success_partition = summary.success_count > 0
    print(F"Success/Total={sum(summary.success_count)}/{sum(summary.total_count[success_partition])}={sum(summary.success_count[success_partition])/sum(summary.total_count[success_partition]):.3f}, Total_partition={len(summary.success_count)}, Success_partition={sum(summary.success_count > 0)}")
    csv_result = log_dir+"_summarize.csv"
    result_dict = {
        "Success":sum(summary.success_count),
        "Total": sum(summary.total_count[success_partition]),
        "Ratio": sum(summary.success_count[success_partition])/sum(summary.total_count[success_partition])
    }
    import pandas as pd
    pd.DataFrame([result_dict]).to_csv(csv_result)
