import os
import copy
import time
import warnings
import argparse
from prover.utils import AttrDict
from prover.algorithms import Sampling

import torch

from prover.workers import DataLoader, Scheduler, ProcessScheduler, GeneratorProcess, SearchProcess
from prover.lean.verifier import Lean4ServerScheduler
from prover.utils import get_datetime, load_config, AttrDict


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=str)
    parser.add_argument("--log_dir", type=str, default=f'logs/{get_datetime()}')
    parser.add_argument("--node_rank", type=int, default=0)
    parser.add_argument("--model_path", type=str, default="/scratch/gpfs/st3812/models/DeepSeek-Prover-V1.5-SFT")
    parser.add_argument("--data_path", type=str, default="/scratch/gpfs/yl7690/projects/DeepSeek-Prover-V1.5/datasets/minif2f.jsonl")
    parser.add_argument("--data_split", type=str, default="valid", help="for example, val:test, split by ':'. ")
    parser.add_argument("--sample_num", type=int, default=32)
    parser.add_argument("--world_size", type=int, default=1)
    parser.add_argument("--batch_size", type=int, default=32)
    parser.add_argument("--n_search_procs", type=int, default=64)
    args = parser.parse_args()
    os.makedirs(args.log_dir, exist_ok=True)

    # verifier
    lean_max_concurrent_requests = 128
    lean_memory_limit = 10
    lean_timeout = 300

    model_args = AttrDict(
        mode='cot',  # `cot` or `non-cot`
        temperature=1,
        max_tokens=2048,
        top_p=0.95,
    )
    sampler = dict(
        algorithm=Sampling,
        sample_num=args.sample_num,
        log_interval=args.sample_num,
    )
    os.makedirs(args.log_dir, exist_ok=True)

    ngpus = torch.cuda.device_count()
    assert ngpus >= 1
    
    # create data loader
    splits = args.data_split.split(":")
    print(F"We are annotating {len(splits)} splits")
    data_loader = DataLoader(
        data_path=args.data_path,
        data_split=splits,
        data_repeat=1,
        node_rank=args.node_rank,
        world_size=args.world_size,
        log_dir=args.log_dir,
    )

    # build Lean verifier
    verifier_scheduler = Lean4ServerScheduler(
        max_concurrent_requests=lean_max_concurrent_requests,
        memory_limit=lean_memory_limit,
        timeout=lean_timeout,
        name='verifier',
    )

    # load LLM models on gpus
    generator_scheduler = ProcessScheduler(batch_size=args.batch_size, name='generator')
    llm_processes = [
        GeneratorProcess(
            local_rank=local_rank,
            node_rank=args.node_rank,
            model_path=args.model_path,
            task_queue=generator_scheduler.task_queue,
            request_statuses=generator_scheduler.request_statuses,
            lock=generator_scheduler.lock,
            args=model_args,
        )
        for local_rank in range(ngpus)
    ]

    # create a unified scheduler interface
    scheduler = Scheduler(dict(
        verifier=verifier_scheduler,
        generator=generator_scheduler,
    ))

    # launch search processes
    search_processes = [
        SearchProcess(
            idx=i+args.node_rank*args.n_search_procs,
            log_dir=args.log_dir,
            tokenizer_path=args.model_path,
            scheduler=scheduler,
            data_loader=data_loader,
            sampler=sampler,
            model_args=model_args
        )
        for i in range(min(args.n_search_procs, data_loader.size()))
    ]
    for p in search_processes:
        p.start()
    print(f'Complete launching {len(search_processes)} SearchProcesses')

    for p in llm_processes:
        p.start()
    print(f'Complete launching {len(llm_processes)} LLMProcesses')

    for p in search_processes:
        p.join()
    print(f'All {len(search_processes)} SearchProcesses stopped')

    scheduler.close()

    for p in llm_processes:
        p.join()
    print(f'All {len(llm_processes)} LLMProcesses stopped')
