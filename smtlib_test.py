import os
import re
import subprocess

current_benchmark = 'abs'
directory = os.getcwd()

# Define the regex pattern
pattern = re.compile(rf"{re.escape(current_benchmark)}_synth_\d+_\d+\.smt2")

# List to store the matching files
matching_files = []

# Walk through the directory
for root, _, files in os.walk(directory):
    for filePath in files:
        if pattern.match(filePath):
            matching_files.append(os.path.join(root, filePath))


for filePath in matching_files:
    res = subprocess.run(['cvc5', filePath, '--produce-models'], capture_output=True).stdout.decode('utf-8').strip()
    print(filePath, res)

