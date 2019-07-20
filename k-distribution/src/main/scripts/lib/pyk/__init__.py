#!/usr/bin/env python3

import argparse
import subprocess
import sys
import tempfile

def _teeProcessStdout(args, tee = True, buffer_size = 80):
        process = subprocess.Popen(args, stdout = subprocess.PIPE, stderr = subprocess.PIPE, universal_newlines = True)
        capture = ""
        s = process.stdout.read(buffer_size)
        while len(s) > 0:
            if tee:
                sys.stdout.write(s)
                sys.stdout.flush()
            capture += s
            s = process.stdout.read(buffer_size)
        if tee:
            sys.stderr.write(stderr)
            sys.stderr.flush()
        return (process.returncode, capture, stderr)

def _notif(msg):
    print()
    print(msg)
    print(''.join(['=' for c in msg]))
    sys.stdout.flush()

def _warning(msg):
    _notif('[WARNING] ' + msg)

def _fatal(msg, code = 1):
    _notif('[FATAL] ' + msg)
    sys.exit(code)

pykArgs = argparse.ArgumentParser()

pykArgs.add_argument('command' , choices = ['parse', 'run', 'prove'])
_kexec = { 'parse' : 'kast' , 'run' : 'krun' , 'prove' : 'kprove' }

pykArgs.add_argument('-d', '--definition')

pykArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
pykArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')

pykArgs.add_argument('-f', '--from', default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
pykArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])

pykArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

def __main__(args):

    inputFile = args['input'].name
    if inputFile == '-':
        with tempfile.NamedTemporaryFile(mode = 'w') as tempf:
            tempf.write(args['input'].read())
            inputFile = tempf.name

    kCommand = [ _kexec[args['command']] , '--directory' , args['definition'] , inputFile
               , '--input'  , args['from'] , '--output' , args['to']
               ] + args['kArgs']
    _notif('Running: ' + str(kCommand))
    (returncode, stdout, stderr) = _teeProcessStdout(kCommand, tee = teeOutput)

    args['output'].write(stdout)

    if returnCode != 0:
        _fatal('Non-zero exit code (' + str(returnCode) + ': ' + str(kCommand), code = returnCode)

if __name__ == '__main__':
    __main__(pykArgs.parse_args())
