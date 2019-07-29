#!/usr/bin/env python3

import argparse
import subprocess
import sys
import tempfile

from .kast      import _notif, _warning, _fatal
from .kastManip import *

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
            sys.stderr.write(process.stderr.read())
            sys.stderr.flush()
        process.wait()
        return (process.returncode, capture, process.stderr.read())

def _runK(command, definition, inputFile, kArgs = [], teeOutput = True, kRelease = None):
    if kRelease is not None:
        command = kRelease + '/bin/' + command
    kCommand = [ command , '--directory' , definition , inputFile ] + kArgs
    _notif('Running: ' + ' '.join(kCommand))
    return _teeProcessStdout(kCommand, tee = teeOutput)

def kast(definition, inputFile, kastArgs = [], teeOutput = True, kRelease = None):
    return _runK('kast', definition, inputFile, kArgs = kastArgs, teeOutput = teeOutput, kRelease = kRelease)

def krun(definition, inputFile, krunArgs = [], teeOutput = True, kRelease = None):
    return _runK('krun', definition, inputFile, kArgs = krunArgs, teeOutput = teeOutput, kRelease = kRelease)

def kprove(definition, inputFile, kproveArgs = [], teeOutput = True, kRelease = None):
    return _runK('kprove', definition, inputFile, kArgs = kproveArgs, teeOutput = teeOutput, kRelease = kRelease)

pykArgs = argparse.ArgumentParser()

pykArgs.add_argument('command' , choices = ['parse', 'run', 'prove'])

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

    definition = args['definition']
    if args['command'] == 'parse':
        (returncode, stdout, stderr) = kast(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
    elif args['command'] == 'run':
        (returncode, stdout, stderr) = krun(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
    elif args['command'] == 'prove':
        (returncode, stdout, stderr) = kprove(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])

    args['output'].write(stdout)

    if returnCode != 0:
        _fatal('Non-zero exit code (' + str(returnCode) + ': ' + str(kCommand), code = returnCode)

if __name__ == '__main__':
    __main__(pykArgs.parse_args())
