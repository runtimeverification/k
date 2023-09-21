#!/usr/bin/env python3
import json
import sys
import subprocess

COMMIT_SHA = sys.argv[1]
FROM_BRANCH=''
TO_BRANCH='develop'

def execute_command(command):
    # Try to run the command
    try:
        result = subprocess.run(command,stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)

        # Check for errors
        if result.returncode != 0:
            print("Error:", result.stderr)
            exit(1)

    except subprocess.CalledProcessError as e:
        # Handle any errors or exceptions here
        print("Error:", e)
        exit(1)

    return result.stdout

# curl command to get the branch name of last commit in develop
API_URL = 'https://api.github.com/repos/runtimeverification/k/commits/' \
        + COMMIT_SHA + '/pulls'
branch_command = ['curl', '-L', '-H', 'Accept:', 'application/vnd.github+json',
                  '-H', '\"Authorization', 'Bearer', '${GITHUB_TOKEN}\"', '-H',
                  '\"X-GitHub-Api-Version:', '2022-11-28\"', API_URL]
FROM_BRANCH = json.loads(execute_command(branch_command))[0]['head']['label']

# If FROM_BRANCH contains user information get only the branch name
if ':' in FROM_BRANCH: FROM_BRANCH = FROM_BRANCH.split(':')[1]

print("Exporting last bencher report from", FROM_BRANCH, "to", TO_BRANCH)

# This command will generate a JSON file with a list containing the last reports
# sorted in descendenting order for the project.
bencher_command = ["bencher", "report", "list", "--project", "k-framework",
                   "--sort", "date_time", "--direction", "desc", "--per-page",
                   "255"]
data = json.loads(execute_command(bencher_command))

# Collect all elemnts where the key 'project' is 'k_framework'
k_framework = [item for item in data if item['project']['slug'] == 'k-framework'
               and item['branch']['slug'] == FROM_BRANCH]

print("Found", len(k_framework), "reports for k-framework in", FROM_BRANCH)

# Append the last 6 reports to the list, they correspond to the last performance
# execution on the last commit in FROM_BRANCH
def get_name_and_value(item):
    return item['metric_kind']['slug'], item['benchmarks'][0]['metric']['value']

data = {}
for i in range(0,6):
    item = k_framework[i]
    results = item['results']
    benchmark_name = results[0][0]['benchmarks'][0]['name']
    metric_name_memory, value_memory = get_name_and_value(results[0][0])
    metric_name_size, value_size = get_name_and_value(results[0][1])

    branch = item['branch']
    print("Appended:", benchmark_name, "created in", item['created'],
          "on branch", branch['name'], "with id", branch['version']['number'])

    data.update({benchmark_name: {metric_name_size: {"value": value_size},
                                  metric_name_memory: {"value": value_memory}}
                 })

json.dump(data, open('.profiling-results.json', 'w'), indent=4)
