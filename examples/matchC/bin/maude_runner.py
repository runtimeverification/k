import subprocess
import time

from ansi_colors import *


### 
print_prefix = '\{print'
print_suffix = '\}'
timer_flag = 't'
reset_flag = 'r'
open_flag = 'o'


def run(args, output_filter):
    cmd = ['unbuffer', 'maude'] + args

    print "Loading Maude .......",
    start = time.time()

    maude = subprocess.Popen(cmd, stdout=subprocess.PIPE)

    while True:
        line = maude.stdout.readline()
        if line.startswith("Bye"): break

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
                print line,
                continue

            end = time.time()
            elapsed = round(end - start, 3)
            if isReset: start = end

            print content,
            if isTimer:
                time_display = yellow_color + '%.3f' % elapsed + 's' + no_color
                if isOpen:
                  print '[' + time_display + ',',
                else:
                  print '[' + time_display + ']',
            if not isOpen:
                print
        else:
            output_filter(line) 

