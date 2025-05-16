import pandas as pd

def jsonl_to_parquet(jsonl_path, parquet_path):
    # Read the JSONL file into a pandas DataFrame
    df = pd.read_json(jsonl_path, lines=True)

    # Save the DataFrame to a Parquet file
    df.to_parquet(parquet_path, engine='pyarrow', index=False)

# Example usage
file_name="benchmark/real"
jsonl_to_parquet(f"{file_name}.jsonl", f"{file_name}.parquet")