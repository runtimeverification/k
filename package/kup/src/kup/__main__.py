import os
import json
import subprocess
from argparse import ArgumentParser
from terminaltables import SingleTable

INSTALLED = "🟢 \033[92minstalled\033[0m"
AVAILABLE = "🔵 \033[94mavailable\033[0m"
UPDATE = "🟠 \033[93mnewer version available\033[0m"
LOCAL = "(not managed by kup)"

kup_packages = {
  "kup": {
    "repo": "k",
    "package": "kup"
  },
  "k": {
    "repo": "k",
    "package": "k"
  },
  "evm-semantics": {
    "repo": "evm-semantics",
    "package": "kevm"
  },
  "ksummarize": {
    "repo": "ksummarize",
    "package": "ksummarize"
  }
}

packages = []
installed_packages = []

def nix(args):
  extraFlags = [
    '--option', 'extra-substituters', 'https://k-framework.cachix.org https://cache.iog.io',
    '--option', 'extra-trusted-public-keys', 'k-framework.cachix.org-1:jeyMXB2h28gpNRjuVkehg+zLj62ma1RnyyopA/20yFE= hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=',
    '--extra-experimental-features', 'nix-command flakes'
  ]
  return subprocess.run(['nix'] + args + extraFlags, stdout=subprocess.PIPE)


def check_package_version(package: str, currentUrl: str ) -> str:
  result = nix(['flake', 'metadata', 'github:runtimeverification/' + package, '--json'])
  meta = json.loads(result.stdout)

  if meta["url"] == currentUrl:
    return INSTALLED
  else:
    return UPDATE


def reload_packages():
  global packages, installed_packages
  with open(os.getenv("HOME")+"/.nix-profile/manifest.json") as manifest_file:
    manifest = json.loads(manifest_file.read())["elements"]
    # print(json.dumps(manifest, indent=4))

    kup = next(({
      "name": "kup",
      "version": m["url"].removeprefix("github:runtimeverification/k/"),
      "status": INSTALLED,
      "immutable": len(m["originalUrl"].removeprefix("github:runtimeverification/k").split("/")) > 1,
      "storePaths": m["storePaths"]
    } for m in manifest if 
      "url" in m and 
      "github:runtimeverification/k/" in m["url"] and 
      "attrPath" in m and 
      "kup" in m["attrPath"]), 
    {
      "name": "kup",
      "version": "-",
      "status": LOCAL
    })

    packages = [kup]

    for m in manifest:
      if "originalUrl" in m and m["originalUrl"].startswith("github:runtimeverification/"):
        name = m["originalUrl"].removeprefix("github:runtimeverification/").split("/")[0]
        # print(json.dumps(check_package_version(name), indent=4))
        packages.append({
          "name": name,
          "version": m["url"].removeprefix("github:runtimeverification/" + name + "/"),
          "status": check_package_version(name, m["url"]),
          "immutable": len(m["originalUrl"].removeprefix("github:runtimeverification/").split("/")) > 1,
          "storePaths": m["storePaths"]
        })
    installed_packages = [ p["name"] for p in packages ]
    for p in kup_packages.keys():
      if p not in installed_packages:
        packages.append({
          "name": p,
          "version": "",
          "immutable": False,
          "status": AVAILABLE
        })

def find_package_index(storePaths):
  global packages, installed_packages
  with open(os.getenv("HOME")+"/.nix-profile/manifest.json") as manifest_file:
    manifest = json.loads(manifest_file.read())["elements"]
    return next((idx for idx, m in enumerate(manifest) if m["storePaths"] == storePaths), -1)

def main() -> None:
  parser = ArgumentParser(description='The K Framework installer')
  subparser = parser.add_subparsers(dest='command')
  subparser.add_parser('list', help='Show the active and installed K semantics')

  install = subparser.add_parser('install', help='Download and install the stated package')
  install.add_argument('package', type=str)

  uninstall = subparser.add_parser('uninstall', help='Uninstall the given package')
  uninstall.add_argument('package', type=str)

  update = subparser.add_parser('update', help='Update the package to the latest version')
  update.add_argument('package', type=str)
  update.add_argument('--version', type=str)


  shell = subparser.add_parser('shell', help='Add the selected package to the current shell (temporary)')
  shell.add_argument('package', type=str)
  shell.add_argument('--version', type=str)

  args = parser.parse_args()

  if args.command == "list":
    reload_packages()
    table_data = [
        ['Package', "Installed version", "Status"],
    ] + [ [ p["name"], p["version"], p["status"] ] for p in packages ]
    table = SingleTable(table_data)
    print(table.table)
  
  elif args.command == "update":
    reload_packages()
    if args.package not in kup_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    if args.package not in installed_packages:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is not currently installed. Use \'\033[92mkup install {args.package}\033[0m\' to install the latest version.')
      return
    package = next(p for p in packages if p["name"] == args.package)
    if package["status"] == LOCAL:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is not managed by kup.')
      return
    if package["status"] == INSTALLED:
      print(f'The package \'\033[94m{args.package}\033[0m\' is already up to date.')
      return
    # print(package)
    nix_profile_index = find_package_index(package["storePaths"])

    if package["immutable"]:
      nix(['profile', 'remove', str(nix_profile_index)])
      nix(['profile', 'install', f'github:runtimeverification/{kup_packages[args.package]["repo"]}#{kup_packages[args.package]["package"]}'])
  
    else:
      nix(['profile', 'upgrade', str(nix_profile_index)])

  elif args.command == "uninstall":
    reload_packages()
    if args.package not in kup_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    if args.package not in installed_packages:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is not currently installed.')
      return
    package = next(p for p in packages if p["name"] == args.package)
    if package["status"] == LOCAL:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is not managed by kup.')
      return
    nix_profile_index = find_package_index(package["storePaths"])

    nix(['profile', 'remove', str(nix_profile_index)])

  elif args.command == "install":
    reload_packages()
    if args.package not in kup_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    if args.package in installed_packages:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is already installed.')
      return

    nix(['profile', 'install', f'github:runtimeverification/{kup_packages[args.package]["repo"]}#{kup_packages[args.package]["package"]}'])
  
  else:
    print(args)


if __name__ == '__main__':
    main()
