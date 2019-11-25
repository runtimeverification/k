#!/usr/bin/env python3

import os
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
    elif 'K_RELEASE' in os.environ:
        command = os.environ['K_RELEASE'] + '/bin/' + command
    kCommand = [ command , '--directory' , definition , inputFile ] + kArgs
    _notif('Running: ' + ' '.join(kCommand))
    return _teeProcessStdout(kCommand, tee = teeOutput)

def kast(definition, inputFile, kastArgs = [], teeOutput = True, kRelease = None):
    return _runK('kast', definition, inputFile, kArgs = kastArgs, teeOutput = teeOutput, kRelease = kRelease)

def krun(definition, inputFile, krunArgs = [], teeOutput = True, kRelease = None):
    return _runK('krun', definition, inputFile, kArgs = krunArgs, teeOutput = teeOutput, kRelease = kRelease)

def kprove(definition, inputFile, kproveArgs = [], teeOutput = True, kRelease = None):
    return _runK('kprove', definition, inputFile, kArgs = kproveArgs, teeOutput = teeOutput, kRelease = kRelease)

def kastJSON(definition, inputJSON, kastArgs = [], teeOutput = True, kRelease = None, keepTemp = False):
    with tempfile.NamedTemporaryFile(mode = 'w', delete = not keepTemp) as tempf:
        tempf.write(json.dumps(inputJSON))
        tempf.flush()
        return kast(definition, tempf.name, kastArgs = kastArgs, teeOutput = teeOutput, kRelease = kRelease)

def krunJSON(definition, inputJSON, krunArgs = [], teeOutput = True, kRelease = None, keepTemp = False):
    with tempfile.NamedTemporaryFile(mode = 'w', delete = not keepTemp) as tempf:
        tempf.write(json.dumps(inputJSON))
        tempf.flush()
        (rC, out, err) = krun(definition, tempf.name, krunArgs = krunArgs + ['--output', 'json', '--parser', 'cat'], teeOutput = teeOutput, kRelease = kRelease)
        out = None if out == '' else json.loads(out)['term']
        return (rC, out, err)

def kproveJSON(definition, inputJSON, symbolTable, kproveArgs = [], teeOutput = True, kRelease = None, keepTemp = False):
    if not isKDefinition(inputJSON):
        sys.stderr.write(inputJSON)
        _fatal("Not a K Definition!")
    with tempfile.NamedTemporaryFile(mode = 'w', delete = not keepTemp) as tempf:
        tempf.write(prettyPrintKast(inputJSON, symbolTable))
        tempf.flush()
        (rC, out, err) = kprove(definition, tempf.name, kproveArgs = kproveArgs + ['--output', 'json'], teeOutput = teeOutput, kRelease = kRelease)
        out = None if out == '' else json.loads(out)['term']
        return (rC, out, err)
