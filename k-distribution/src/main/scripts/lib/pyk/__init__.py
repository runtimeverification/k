#!/usr/bin/env python3

import argparse
import subprocess
import sys
import tempfile

def notif(msg):
    print()
    print(msg)
    print(''.join(['=' for c in msg]))
    sys.stdout.flush()

def warning(msg):
    notif('[WARNING] ' + msg)

def fatal(msg):
    notif('[FATAL] ' + msg)
    sys.exit(1)

def _runK(command, definitionDir, fileName, kArgs):
    return kProc.returnCode

pykArgs = argparse.ArgumentParser()

pykArgs.add_argument('command' , choices = ['parse', 'run', 'prove'])
_kexec = { 'parse' : 'kast'
         , 'run'   : 'krun'
         , 'prove' : 'kprove'
         }

pykArgs.add_argument('-d', '--definition')

pykArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
pykArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')

pykArgs.add_argument('-f', '--from', default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
pykArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])

pykArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

def __main__():
    args = pykArgs.parse_args()

    inputFile = pykArgs.input.name
    if inputFile == '-':
        with tempfile.NamedTemporaryFile(mode = 'w') as tempf:
            tempf.write(pykArgs.input.read())
            inputFile = tempf.name

    kCommand = [ _kexec[pykArgs.command], '--directory', pykArgs.definition, inputFile
               , '--input'  , pykArgs['from']
               , '--output' , pykArgs.to
               ] + kArgs
    notif('Running: ' + str(kCommand))
    kProc = subprocess.run(kCommand)

if __name__ == '__main__':
    __main__()
