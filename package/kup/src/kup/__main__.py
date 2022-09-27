import os, sys
import json
import subprocess
from argparse import ArgumentParser
from terminaltables import SingleTable

INSTALLED = "🟢 \033[92minstalled\033[0m"
AVAILABLE = "🔵 \033[94mavailable\033[0m"
UPDATE = "🟠 \033[93mnewer version available\033[0m"
LOCAL = "\033[3mnot managed by kup\033[0m"

NIX_SUBSTITUTERS = [
  '--option', 'extra-substituters', 'https://k-framework.cachix.org https://cache.iog.io',
  '--option', 'extra-trusted-public-keys', 'k-framework.cachix.org-1:jeyMXB2h28gpNRjuVkehg+zLj62ma1RnyyopA/20yFE= hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ='
]

def nix(args, extraFlags = NIX_SUBSTITUTERS):
  return subprocess.run(['nix'] + args + ['--extra-experimental-features', 'nix-command flakes'] + extraFlags, stdout=subprocess.PIPE)

SYSTEM = nix(['eval', '--impure', '--expr', 'builtins.currentSystem'], extraFlags = []).stdout.decode('utf8').strip().replace('"', '')

class AvailablePackage:
  def __init__(self, repo:str, package:str):
    self.repo = repo
    self.package = package

available_packages:dict[str,AvailablePackage] = {
  'kup': AvailablePackage('k', f'packages.{SYSTEM}.kup'),
  'k': AvailablePackage('k', f'packages.{SYSTEM}.k'),
  'kevm': AvailablePackage('evm-semantics', f'packages.{SYSTEM}.kevm'),
  'kore-exec': AvailablePackage('haskell-backend', f'packages.{SYSTEM}.kore:exe:kore-exec'),
  # 'ksummarize': AvailablePackage('ksummarize', f'packages.{SYSTEM}.ksummarize'),
}


class ConcretePackage:
  def __init__(self, repo: str, package: str, status: str, version: str = '-', immutable: bool = True, index: int = -1):
    self.repo = repo
    self.package = package
    self.version = version
    self.status = status
    self.immutable = immutable
    self.index = index

packages: dict[str, ConcretePackage] = {}
installed_packages: list[str] = []


def check_package_version(p: AvailablePackage, currentUrl: str ) -> str:
  result = nix(['flake', 'metadata', f'github:runtimeverification/{p.repo}', '--json'])
  meta = json.loads(result.stdout)

  if meta["url"] == currentUrl:
    return INSTALLED
  else:
    return UPDATE


def reload_packages():
  global packages, installed_packages
  packages = {}
  installed_packages = []
  with open(f'{os.getenv("HOME")}/.nix-profile/manifest.json') as manifest_file:
    manifest = json.loads(manifest_file.read())['elements']
    available_packages_lookup = { p.package: (key, p) for key, p in available_packages.items() }

    for idx, m in enumerate(manifest):
      if 'attrPath' in m and m['attrPath'] in available_packages_lookup:
        (name, available_package) = available_packages_lookup[m['attrPath']]
        if 'originalUrl' in m and m['originalUrl'].startswith(f'github:runtimeverification/{available_package.repo}'):
          version = m['url'].removeprefix(f'github:runtimeverification/{available_package.repo}/')
          status = check_package_version(available_package,m['url'])
          immutable = len(m['originalUrl'].removeprefix(f'github:runtimeverification/{available_package.repo}')) > 1,
          packages[name] = ConcretePackage(available_package.repo, available_package.package, status, version, immutable, idx)
        else:
          packages[name] = ConcretePackage(available_package.repo, available_package.package, LOCAL, index = idx)


    installed_packages = [ p for p in packages ]
    for p in available_packages:
      if p not in installed_packages:
        package = available_packages[p]
        packages[p] = ConcretePackage(package.repo, package.package, AVAILABLE, '')
        

def main() -> None:
  parser = ArgumentParser(description='The K Framework installer')
  subparser = parser.add_subparsers(dest='command')
  subparser.add_parser('list', help='Show the active and installed K semantics')

  install = subparser.add_parser('install', help='Download and install the stated package')
  install.add_argument('package', type=str)
  install.add_argument('--version', type=str)

  uninstall = subparser.add_parser('remove', help='Remove the given package from the user\'s PATH')
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
    ] + [ [ name, p.version, p.status ] for name, p in packages.items() ]
    table = SingleTable(table_data)
    print(table.table)
  
  elif args.command == "update":
    reload_packages()
    if args.package not in available_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    if args.package not in installed_packages:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is not currently installed. Use \'\033[92mkup install {args.package}\033[0m\' to install the latest version.')
      return
    package = packages[args.package]
    if package.status == INSTALLED and not args.version:
      print(f'The package \'\033[94m{args.package}\033[0m\' is already up to date.')
      return

    if package.immutable or args.version:
      nix(['profile', 'remove', str(package.index)])
      version = '/' + args.version if args.version else ''
      nix(['profile', 'install', f'github:runtimeverification/{package.repo}{version}#{package.package}'])
    else:
      nix(['profile', 'upgrade', str(package.index)])

  elif args.command == "remove":
    reload_packages()
    if args.package not in available_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    if args.package not in installed_packages:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is not currently installed.')
      return

    if args.package == "kup" and len(installed_packages) > 1:
      print(f'⚠️ You are about to remove \'\033[94mkup\033[0m\' with other K framework packages still installed. Are you sure you want to continue? [y/N]')

      yes = {'yes','y', 'ye', ''}
      no = {'no','n'}

      choice = input().lower()
      if choice in no:
        return
      if choice in yes:
        pass
      else:
        sys.stdout.write("Please respond with '[y]es' or '[n]o'")
        return
    package = packages[args.package]
    nix(['profile', 'remove', str(package.index)])

  elif args.command == "install":
    reload_packages()
    if args.package not in available_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    if args.package in installed_packages:
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' is already installed. Use \'\033[92mkup update {args.package}\033[0m\' to update to the latest version.')
      return
    package = available_packages[args.package]
    version = '/' + args.version if args.version else ''
    nix(['profile', 'install', f'github:runtimeverification/{package.repo}{version}#{package.package}'])
  
  elif args.command == "shell":
    reload_packages()
    if args.package not in available_packages.keys():
      print(f'❗ The package \'\033[94m{args.package}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.')
      return
    package = available_packages[args.package]
    version = '/' + args.version if args.version else ''
    nix(['profile', 'install', f'github:runtimeverification/{package.repo}{version}#{package.package}'])
  
if __name__ == '__main__':
    main()
