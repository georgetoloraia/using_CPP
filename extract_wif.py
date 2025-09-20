import re

# Regular expression to match WIF= followed by non-whitespace characters
pattern = re.compile(r'WIF=(\S+)')

with open('recovered_keys.txt', 'r') as input_file, \
     open('wifs.txt', 'w') as output_file:
    
    for line in input_file:
        match = pattern.search(line)
        if match:
            wif_key = match.group(1)
            output_file.write(wif_key + '\n')
