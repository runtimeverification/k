#!/usr/local/bin/python

import argparse
import os
import sys
import subprocess
import tempfile
import time

from ansi_colors import *
import maude_runner

k_root_dir = os.path.expanduser(os.path.join('~', 'k-framework'))
k_tools_dir = os.path.join(k_root_dir, 'tools')

ml_lang = 'matchC'
ml_root_dir = os.path.join(k_root_dir, 'examples', 'matchC')
ml_lib_dir = os.path.join(ml_root_dir, 'lib')
ml_lib_utils = os.path.join(ml_lib_dir, 'utils.maude')
ml_parser_dir = os.path.join(ml_root_dir, 'parser')
ml_parser_main_class = 'KernelCPreK'
ml_semantics_dir = os.path.join(ml_root_dir, 'semantics')
ml_semantics_compiled = os.path.join(ml_semantics_dir,
                                     ml_lang + '-compiled.maude')
ml_viewer_dir = os.path.join(ml_root_dir, 'bin')
ml_viewer_text_main_class = 'TextViewer'
ml_viewer_visual_main_class = 'VisualViewer'

antlr_jar = os.path.join(k_tools_dir, 'antlr', 'antlrworks-1.4.jar')

ml_prog = 'prog'
ml_prog_header = ['load ' + ml_semantics_compiled + '\n',
    'load ' + ml_lib_utils + '\n',
    'mod ' + ml_prog.upper() + ' is inc ' + ml_lang.upper() + ' + UTILS .\n']
ml_prog_footer = ['endm\n\n',
    'set print attribute on .\n',
    'rew check(' + ml_prog + ') .\n',
    'q\n']


### compile c program with ml annotation into labeled k (maude format)
def compile(in_filename, out_filename):
    cmd = ['java', '-cp', antlr_jar + ':' + ml_parser_dir, ml_parser_main_class]
    in_file = open(in_filename, 'r')
    out_file = open(out_filename, 'w')

    out_file.writelines(ml_prog_header)
    out_file.flush()
    start = time.time()
    print 'Compiling program ...',

    retcode = subprocess.call(cmd, bufsize=-1, stdin=in_file, stdout=out_file)
    if retcode != 0: sys.exit(retcode)

    out_file.writelines(ml_prog_footer)
    in_file.close()
    out_file.close()
    end = time.time()
    elapsed = yellow_color + "%.3f" % round(end - start, 3) + "s" + no_color
    print 'DONE! [' + elapsed + ']'


def verify(prog_filename, log=None):
    args = ['-no-banner', '-no-wrap', '-no-ansi-color']
    if log != None:
        args += ['-xml-log=' + log]
    args += [prog_filename]
    maude_runner.run(args, filter=output_filter, epilog='DONE! ')

    if verified:
        print green_color + 'Verification succeeded!' + no_color, statistics
        if output_stream != None:
            print 'Output:', output_stream
    else:
        print red_color + 'Verification failed!' + no_color, statistics


verified = True
statistics = None
output_stream = None
def output_filter(line):
    global verified
    global statistics
    global output_stream

    line = line.strip()
    if line.startswith('rewrites'):
        rewrites = cyan_color + line.split()[1] + no_color
        statistics = '[' + rewrites + ' rewrites, '
    elif line.startswith('< feasible >'):
        feasible = green_color + line.split()[3][15:-10] + no_color
        statistics += feasible + ' feasible and '
    elif line.startswith('< infeasible >'):
        infeasible = red_color + line.split()[3][15:-10] + no_color
        statistics += infeasible + ' infeasible paths]'
    elif line.startswith('< tasks >'):
        verified = False
    elif line.startswith('< out >') and verified:
        output_stream = line.replace(' @ ', ' ')
        output_stream = output_stream.replace('[', '').replace(']', '')
        output_stream = output_stream[15:-10]


###
def main():
    parser = argparse.ArgumentParser(
        description='Matching logic verifier',
        prog='matchC')
    parser.add_argument(
        '-o',
        help='place tool output into file',
        metavar='file',
        dest='output')
    parser.add_argument(
        '-m', '--main-only',
        action='store_true',
        default=False,
        help='execute main only, do not verify other functions',
        dest='main')
    parser.add_argument(
        '-c', '--compile-only',
        action='store_true',
        default=False,
        help='compile progam and specifications into labeled k (maude format)' \
            +' only; do not verify any function',
        dest='compile')
    parser.add_argument(
        '-d', '--display',
        action='store_true',
        default=False,
        help='display verifier output into a java widget')
    parser.add_argument(
        '-s', '--silent',
        action='store_true',
        default=False,
        help='do not generate any verifier output')
    parser.add_argument(
        'file',
        help='file to verify',
        metavar='file')
    args = parser.parse_args()

    if args.output == None:
        rootname = os.path.splitext(os.path.basename(args.file))[0]
        if not args.compile:
            args.output = rootname + '.kml'
        else:
            args.output = rootname + '.maude'

    if not os.path.isfile(args.file):
        sys.exit('matchC: ' + args.file + ': no such file or directory')

    if not args.compile:
        compiled_file = tempfile.mktemp('.maude')
    else:
        compiled_file = args.output
    compile(args.file, compiled_file)
    if args.compile: return

    if not args.silent:
        log_file = tempfile.mktemp('.xml')
        verify(compiled_file, log=log_file)
    else:
        verify(compiled_file)

    if not args.silent and not args.display:
        cmd = ['java', '-cp', ml_viewer_dir, ml_viewer_text_main_class,
              log_file, args.output]

        start = time.time()
        print 'Generating output ...',

        retcode = subprocess.call(cmd)
        if retcode != 0: sys.exit(retcode)

        end = time.time()
        elapsed = yellow_color + "%.3f" % round(end - start, 3) + "s" + no_color
        print 'DONE! [' + elapsed + ']'

        print 'Check ' + args.output + ' for the complete output.'


main()


