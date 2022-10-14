import json
import os
import subprocess
import sys
import textwrap
from argparse import ArgumentParser
from typing import Optional, Union

import requests
from terminaltables import SingleTable  # type: ignore

INSTALLED = "🟢 \033[92minstalled\033[0m"
AVAILABLE = "🔵 \033[94mavailable\033[0m"
UPDATE = "🟠 \033[93mnewer version available\033[0m"
LOCAL = "\033[3mlocal checkout\033[0m"

NIX_SUBSTITUTERS = [
    '--option',
    'extra-substituters',
    'https://k-framework.cachix.org https://cache.iog.io',
    '--option',
    'extra-trusted-public-keys',
    'k-framework.cachix.org-1:jeyMXB2h28gpNRjuVkehg+zLj62ma1RnyyopA/20yFE= hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=',
]


def nix_raw(args: list[str], extra_flags: list[str] = NIX_SUBSTITUTERS, gc_dont_gc: bool = True) -> bytes:
    my_env = os.environ.copy()
    if gc_dont_gc:
        my_env["GC_DONT_GC"] = "1"
    try:
        output = subprocess.check_output(
            ['nix'] + args + ['--extra-experimental-features', 'nix-command flakes'] + extra_flags, env=my_env
        )
    except subprocess.CalledProcessError as exc:
        print('❗ \033[91mThe operation could not be completed. See above for the error output ...\033[0m')
        sys.exit(exc.returncode)
    else:
        return output


SYSTEM = (
    nix_raw(['eval', '--impure', '--expr', 'builtins.currentSystem'], extra_flags=[])
    .decode('utf8')
    .strip()
    .replace('"', '')
)

# nix tends to fail on macs with a segfault so we add `GC_DONT_GC=1` if on macOS (i.e. darwin)
# The `GC_DONT_GC` simply disables the garbage collector used during evaluation of a nix
# expression. This may cause the process to run out of memory, but hasn't been observed for our
# derivations in practice, so should be ok to do.
def nix(args: list[str], extra_flags: list[str] = NIX_SUBSTITUTERS) -> bytes:
    return nix_raw(args, extra_flags, True if "darwin" in SYSTEM else False)


def nix_detach(args: list[str], extra_flags: list[str] = NIX_SUBSTITUTERS) -> None:
    my_env = os.environ.copy()
    if "darwin" in SYSTEM:
        my_env["GC_DONT_GC"] = "1"
    nix = subprocess.check_output(['which', 'nix']).decode('utf8').strip()
    os.execve(nix, [nix] + args + ['--extra-experimental-features', 'nix-command flakes'] + extra_flags, my_env)


class AvailablePackage:
    __slots__ = ["repo", "package"]

    def __init__(self, repo: str, package: str):
        self.repo = repo
        self.package = package


available_packages: dict[str, AvailablePackage] = {
    'kup': AvailablePackage('k', f'packages.{SYSTEM}.kup'),
    'k': AvailablePackage('k', f'packages.{SYSTEM}.k'),
    'kevm': AvailablePackage('evm-semantics', f'packages.{SYSTEM}.kevm'),
    'kore-exec': AvailablePackage('haskell-backend', f'packages.{SYSTEM}.kore:exe:kore-exec'),
}


class ConcretePackage:
    __slots__ = ["repo", "package", "status", "version", "immutable", "index"]

    def __init__(
        self, repo: str, package: str, status: str, version: str = '-', immutable: bool = True, index: int = -1
    ):
        self.repo = repo
        self.package = package
        self.version = version
        self.status = status
        self.immutable = immutable
        self.index = index


packages: dict[str, ConcretePackage] = {}
installed_packages: list[str] = []


def check_package_version(p: AvailablePackage, current_url: str) -> str:
    result = nix(['flake', 'metadata', f'github:runtimeverification/{p.repo}', '--json'])
    meta = json.loads(result)

    if meta["url"] == current_url:
        return INSTALLED
    else:
        return UPDATE


def reload_packages() -> None:
    global packages, installed_packages

    if os.path.exists(f'{os.getenv("HOME")}/.nix-profile/manifest.json'):
        manifest_file = open(f'{os.getenv("HOME")}/.nix-profile/manifest.json')
        manifest = json.loads(manifest_file.read())['elements']
        manifest_file.close()
    else:
        manifest = []

    packages = {}
    available_packages_lookup = {p.package: (key, p) for key, p in available_packages.items()}

    for idx, m in enumerate(manifest):
        if 'attrPath' in m and m['attrPath'] in available_packages_lookup:
            (name, available_package) = available_packages_lookup[m['attrPath']]
            if 'originalUrl' in m and m['originalUrl'].startswith(
                f'github:runtimeverification/{available_package.repo}'
            ):
                version = m['url'].removeprefix(f'github:runtimeverification/{available_package.repo}/')
                status = check_package_version(available_package, m['url'])
                immutable = (
                    len(m['originalUrl'].removeprefix(f'github:runtimeverification/{available_package.repo}')) > 1
                )
                packages[name] = ConcretePackage(
                    available_package.repo, available_package.package, status, version, immutable, idx
                )
            else:
                packages[name] = ConcretePackage(available_package.repo, available_package.package, LOCAL, index=idx)

    installed_packages = list(packages.keys())
    for pkg_name in available_packages:
        if pkg_name not in installed_packages:
            available_package = available_packages[pkg_name]
            packages[pkg_name] = ConcretePackage(available_package.repo, available_package.package, AVAILABLE, '')


class PackageVersion:
    __slots__ = ["sha", "message", "tag", "merged_at"]

    def __init__(self, sha: str, message: str, tag: Optional[str], merged_at: str):
        self.sha = sha
        self.message = message
        self.tag = tag
        self.merged_at = merged_at


def highlight_row(condition: bool, xs: list[str]) -> list[str]:
    if condition:
        return [f'\033[92m{x}\033[0m' for x in xs]
    else:
        return xs


def list_package(package_name: str) -> None:
    reload_packages()
    if package_name != 'all':
        if package_name not in available_packages.keys():
            print(
                f'❗ The package \'\033[94m{package_name}\033[0m\' does not exist. Use \'\033[92mkup list\033[0m\' to see all the available packages.'
            )
            return
        listed_package = available_packages[package_name]

        tags = requests.get(f'https://api.github.com/repos/runtimeverification/{listed_package.repo}/tags')
        commits = requests.get(f'https://api.github.com/repos/runtimeverification/{listed_package.repo}/commits')
        tagged_releases = {t['commit']['sha']: t for t in tags.json()}
        all_releases = [
            PackageVersion(
                c['sha'],
                c['commit']['message'],
                tagged_releases[c['sha']]['name'] if c['sha'] in tagged_releases else None,
                c['commit']['committer']['date'],
            )
            for c in commits.json()
            if not c['commit']['message'].startswith("Merge remote-tracking branch 'origin/develop'")
        ]

        installed_packages_sha = {p.version for p in packages.values()}

        table_data = [['Version \033[92m(installed)\033[0m', "Commit", "Message"],] + [
            highlight_row(
                p.sha in installed_packages_sha,
                [p.tag if p.tag else "", p.sha[:7], textwrap.shorten(p.message, width=50, placeholder="...")],
            )
            for p in all_releases
        ]
        table = SingleTable(table_data)
        print(table.table)
    else:
        table_data = [
            ['Package', "Installed version", "Status"],
        ] + [[name, p.version, p.status] for name, p in packages.items()]
        table = SingleTable(table_data)
        print(table.table)


def update_or_install_package(
    package: Union[AvailablePackage, ConcretePackage], version: Optional[str], local_path: Optional[str]
) -> None:
    version = '/' + version if version else ''
    path = f'github:runtimeverification/{package.repo}{version}' if not local_path else local_path
    if type(package) is ConcretePackage:
        if package.immutable or version or local_path:
            nix(['profile', 'remove', str(package.index)])
            nix(['profile', 'install', f'{path}#{package.package}'])
        else:
            nix(['profile', 'upgrade', str(package.index)])
    else:
        nix(['profile', 'install', f'{path}#{package.package}'])


def install_package(package_name: str, package_version: Optional[str], local_path: Optional[str]) -> None:
    reload_packages()
    if package_name not in available_packages.keys():
        print(
            f'❗ \033[91mThe package \'\033[94m{package_name}\033[91m\' does not exist.\033[0m\nUse \'\033[92mkup list\033[0m\' to see all the available packages.'
        )
        return
    if package_name in installed_packages and not (package_version or local_path):
        print(
            f'❗ The package \'\033[94m{package_name}\033[0m\' is already installed.\nUse \'\033[92mkup update {package_name}\033[0m\' to update to the latest version.'
        )
        return
    if package_name in installed_packages:
        package = packages[package_name]
        update_or_install_package(package, package_version, local_path)
    else:
        new_package = available_packages[package_name]
        update_or_install_package(new_package, package_version, local_path)


def update_package(package_name: str, package_version: Optional[str], local_path: Optional[str]) -> None:
    reload_packages()
    if package_name not in available_packages.keys():
        print(
            f'❗ \033[91mThe package \'\033[94m{package_name}\033[91m\' does not exist.\033[0m\nUse \'\033[92mkup list\033[0m\' to see all the available packages.'
        )
        return
    if package_name not in installed_packages:
        print(
            f'❗ The package \'\033[94m{package_name}\033[0m\' is not currently installed.\nUse \'\033[92mkup install {package_name}\033[0m\' to install the latest version.'
        )
        return
    package = packages[package_name]
    if package.status == INSTALLED and not (package_version or local_path):
        print(f'The package \'\033[94m{package_name}\033[0m\' is up to date.')
        return

    update_or_install_package(package, package_version, local_path)


def remove_package(package_name: str) -> None:
    reload_packages()
    if package_name not in available_packages.keys():
        print(
            f'❗ \033[91mThe package \'\033[94m{package_name}\033[91m\' does not exist.\033[0m\nUse \'\033[92mkup list\033[0m\' to see all the available packages.'
        )
        return
    if package_name not in installed_packages:
        print(f'❗ The package \'\033[94m{package_name}\033[0m\' is not currently installed.')
        return

    if package_name == "kup" and len(installed_packages) > 1:
        print(
            '⚠️ \033[93mYou are about to remove \'\033[94mkup\033[93m\' with other K framework packages still installed.\033[0m\nAre you sure you want to continue? [y/N]'
        )

        yes = {'yes', 'y', 'ye', ''}
        no = {'no', 'n'}

        choice = input().lower()
        if choice in no:
            return
        elif choice in yes:
            pass
        else:
            sys.stdout.write("Please respond with '[y]es' or '[n]o'\n")
            # in case the user selected a wrong opion we want to short-circuit and
            # not try to remove kup twice
            return remove_package(package_name)
    package = packages[package_name]
    nix(['profile', 'remove', str(package.index)])


def main() -> None:
    parser = ArgumentParser(description='The K Framework installer')
    subparser = parser.add_subparsers(dest='command')
    list = subparser.add_parser('list', help='Show the active and installed K semantics')
    list.add_argument('package', nargs='?', default='all', type=str)

    install = subparser.add_parser('install', help='Download and install the stated package')
    install.add_argument('package', type=str)
    install.add_argument('--version', type=str)
    install.add_argument('--local', type=str)

    uninstall = subparser.add_parser('remove', help='Remove the given package from the user\'s PATH')
    uninstall.add_argument('package', type=str)

    update = subparser.add_parser('update', help='Update the package to the latest version')
    update.add_argument('package', type=str)
    update.add_argument('--version', type=str)
    update.add_argument('--local', type=str)

    shell = subparser.add_parser('shell', help='Add the selected package to the current shell (temporary)')
    shell.add_argument('package', type=str)
    shell.add_argument('--version', type=str)
    shell.add_argument('--local', type=str)

    args = parser.parse_args()

    if args.command == "list":
        list_package(args.package)
    elif args.command == "install":
        install_package(args.package, args.version, args.local)
    elif args.command == "update":
        update_package(args.package, args.version, args.local)
    elif args.command == "remove":
        remove_package(args.package)
    elif args.command == "shell":
        reload_packages()
        if args.package not in available_packages.keys():
            print(
                f'❗ \033[91mThe package \'\033[94m{args.package}\033[91m\' does not exist.\033[0m\nUse \'\033[92mkup list\033[0m\' to see all the available packages.'
            )
            return
        temporary_package = available_packages[args.package]
        version = '/' + args.version if args.version else ''
        path = f'github:runtimeverification/{temporary_package.repo}{version}' if not args.local else args.local
        nix_detach(['shell', f'{path}#{temporary_package.package}'])


if __name__ == '__main__':
    main()
