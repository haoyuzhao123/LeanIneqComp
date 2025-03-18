import os

# Specify the current directory
directory = "."  # Current directory

# List to hold files containing 'pkl' in their contents
files_with_pkl = []

# Walk through the directory
for root, dirs, files in os.walk(directory):
    for file in files:
        file_path = os.path.join(root, file)
        
        # Try to open and read the file
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                if 'pkl' in content:
                    files_with_pkl.append(file_path)
        except (UnicodeDecodeError, FileNotFoundError):
            # Handle files that cannot be read as text (e.g., binary files)
            continue

# Print the found files
print("Files containing 'pkl' in their contents:")
for file in files_with_pkl:
    print(file)
