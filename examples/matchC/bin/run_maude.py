#!/usr/local/bin/python3

import os
import subprocess
import sys
import time

from ansi_colors import *


### 
print_prefix = '\{print'
print_suffix = '\}'
timer_flag = 't'
reset_flag = 'r'
open_flag = 'o'


def format_timer(timer):
    return '[' + cyan_color + '%.3f' % timer + 's' + no_color + ']'


def default_filter(line):
    return


def run(args, path=None, filter=default_filter, epilog=''):
    if path != None:

        cmd = [os.path.abspath(os.path.join(path, 'maude'))]
    else:
        cmd = ['bin/maude2.6/maude']
    cmd += args

    print("Loading Maude .......", end=' ')
    start = time.time()

    maude = None
    if os.name == 'posix' or os.name == 'mac':
        try:
            import pty
            (master, slave) = pty.openpty()
            maude_out = os.fdopen(master, 'r')
            maude = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=slave)
        except OSError:
            maude = None 
    if maude == None:
        maude = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE)
        maude_out = maude.stdout
    maude.stdin.close()

    while True:
        line = maude_out.readline()
        if line.startswith("Bye"):
            end = time.time()
            elapsed = round(end - start, 3)
            print(epilog + ' ' + format_timer(elapsed))
            break

        print_suffix_index = line.find(print_suffix)
        if line.startswith(print_prefix) and print_suffix_index != -1:
            content = line[print_suffix_index + len(print_suffix):].rstrip('\n')
            format = line[len(print_prefix):print_suffix_index].strip(' ')

            isTimer = isReset = isOpen = False
            isFormat = True
            for c in format:
                if c == timer_flag:
                    isTimer = True
                elif c == reset_flag:
                    isReset = True
                elif c == open_flag:
                    isOpen = True
                else:
                    isFormat = False
            if not isFormat:
                filter(line)
                continue

            end = time.time()
            elapsed = round(end - start, 3)
            if isReset: start = end

            formated_line = content
            if isTimer:
                formated_line += ' ' + format_timer(elapsed)
            if isOpen:
                print(formated_line, end=' ')
            else:
                print(formated_line)
        else:
            filter(line)
    return maude.wait()


