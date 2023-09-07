#!/usr/bin/env python3
import json
import subprocess

FROM_BRANCH=''
TO_BRANCH='develop'

# This command is needed to get the current branch name
command = ['gh', 'pr', 'list', '-s', 'merged', '-B', 'develop', '-L', '1']

# Try to run the command
try:
    result = subprocess.run(command,stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)

    # Check for errors
    if result.returncode != 0:
        print("Error:", result.stderr)
        exit(1)
    else:
        FROM_BRANCH = result.stdout.split('\t')[-3]

except subprocess.CalledProcessError as e:
    # Handle any errors or exceptions here
    print("Error:", e)

print("Exporting last bencher report from", FROM_BRANCH, "to", TO_BRANCH)

# This command will generate a JSON file with a list containing the last reports
# sorted in descendenting order for the project.
command = ["bencher", "report", "list", "--project", "k-framework", "--sort",
           "date_time", "--direction", "desc", "--per-page", "255"]

print(" ".join(command))
# Try to run the command
try:
    result = subprocess.run(command, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)

    # Check for errors
    if result.returncode != 0:
        print("Error:", result.stderr)
        exit(1)
except subprocess.CalledProcessError as e:
    # Handle any errors or exceptions here
    print("Error:", e)

data = json.loads(result.stdout)

# Collect all elemnts where the key 'project' is 'k_framework'
k_framework = [item for item in data if item['project']['slug'] == 'k-framework'
               and item['branch']['slug'] == FROM_BRANCH]

# Append the last 6 reports to the list, they correspond to the last performance
# execution on the last commit in FROM_BRANCH
data = {}
for i in range(0,6):
    item = k_framework[i]
    results = item['results']
    benchmark_name = results[0][0]['benchmarks'][0]['name']

    memory = results[0][0]
    metric_name_memory = memory['metric_kind']['slug']
    value_memory = memory['benchmarks'][0]['metric']['value']

    size = results[0][1]
    metric_name_size = size['metric_kind']['slug']
    value_size = size['benchmarks'][0]['metric']['value']

    branch = item['branch']
    print("Appended:", benchmark_name, "created in", item['created'],
          "on branch", branch['name'], "with version", branch['version']['number'])

    data.update({benchmark_name: {metric_name_size: {"value": value_size},
                                  metric_name_memory: {"value": value_memory}}
                 })

json.dump(data, open('.profiling-results.json', 'w'), indent=4)
