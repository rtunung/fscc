#!/usr/bin/env python3

# A quick tool for quickly compiling files during development

import sys
import os

if len(sys.argv) < 3:
    print("Usage: ./compile [input] [output]")
    exit()
    
input = sys.argv[1]
output = sys.argv[2]

output_assembly = input + ".s"

exit_code = os.system(f"dotnet run {input} > {output_assembly}")

if exit_code != 0:
    print("Something went wrong! See the error message above!")
    exit()

os.system(f"gcc {output_assembly} -o {output}")
