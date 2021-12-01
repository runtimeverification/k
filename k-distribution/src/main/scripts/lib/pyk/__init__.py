#!/usr/bin/env python3

import os
import subprocess
import sys
import tempfile

from .util       import *
from .kast       import *
from .kastManip  import *
from .coverage   import *
from .definition import *

def _teeProcessStdout(args, tee = True, buffer_size = 80, timeout = None):
    process = subprocess.Popen(args, stdout = subprocess.PIPE, stderr = subprocess.PIPE, universal_newlines = True)
    try:
        (stdout_data, stderr_data) = process.communicate(input = None, timeout = timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        sys.stderr.write('TIMED OUT')
        sys.stderr.flush()
        return (-1, '', '')
    return (process.returncode, stdout_data, stderr_data)

def _runK(command, definition, inputFile, kArgs = [], teeOutput = True, kRelease = None):
    if kRelease is not None:
        command = kRelease + '/bin/' + command
    elif 'K_RELEASE' in os.environ:
        command = os.environ['K_RELEASE'] + '/bin/' + command
    kCommand = [ command , '--directory' , definition , inputFile ] + kArgs
    notif('Running: ' + ' '.join(kCommand))
    return _teeProcessStdout(kCommand, tee = teeOutput)

def kast(definition, inputFile, kastArgs = [], teeOutput = True, kRelease = None):
    return _runK('kast', definition, inputFile, kArgs = kastArgs, teeOutput = teeOutput, kRelease = kRelease)

def krun(definition, inputFile, krunArgs = [], teeOutput = True, kRelease = None):
    return _runK('krun', definition, inputFile, kArgs = krunArgs, teeOutput = teeOutput, kRelease = kRelease)

def kastJSON(definition, inputJSON, kastArgs = [], teeOutput = True, kRelease = None, keepTemp = False):
    with tempfile.NamedTemporaryFile(mode = 'w', delete = not keepTemp) as tempf:
        tempf.write(json.dumps(inputJSON))
        tempf.flush()
        return kast(definition, tempf.name, kastArgs = kastArgs, teeOutput = teeOutput, kRelease = kRelease)

def krunJSON(definition, inputJSON, kastArgs = [], krunArgs = [], teeOutput = True, kRelease = None, keepTemp = False):
    with tempfile.NamedTemporaryFile(mode = 'w', delete = not keepTemp) as tempJSON:
        tempJSON.write(json.dumps(inputJSON))
        tempJSON.flush()
        (rC, kore, err) = kast(definition, tempJSON.name, kastArgs = ['--output', 'kore', '--input', 'json'] + kastArgs, teeOutput = teeOutput, kRelease = kRelease)
        with tempfile.NamedTemporaryFile(mode = 'w', delete = not keepTemp) as tempKore:
            tempKore.write(kore)
            tempKore.flush()
            (rC, out, err) = krun(definition, tempKore.name, krunArgs = krunArgs + ['--output', 'json', '--parser', 'cat'], teeOutput = teeOutput, kRelease = kRelease)
            out = None if out == '' else json.loads(out)['term']
            return (rC, out, err)
