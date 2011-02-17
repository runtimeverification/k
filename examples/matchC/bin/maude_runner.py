import sys
import subprocess
import time

### 
maude_output_prefix = "maude-output"
maude_timer_prefix = "-timer"
maude_rewrites_prefix = "-rewrites"
tmp_out_filename=".tmp_out_file"

black_color  = "\033[1;30m"
red_color    = "\033[1;31m"
green_color  = "\033[1;32m"
yellow_color = "\033[1;33m"
blue_color   = "\033[1;34m"
purple_color = "\033[1;35m"
cyan_color   = "\033[1;36m"
white_color  = "\033[1;37m"
no_color     = "\033[0m"
###


if len(sys.argv) != 2: sys.exit("maude_runner: invalid number of arguments")

tmp_out_file=open(".tmp_out_file", "w")

maude_args = "unbuffer maude -no-banner -no-wrap -no-ansi-color " + sys.argv[1]
maude = subprocess.Popen(maude_args, shell=True, stdout=subprocess.PIPE)


print "Loading Maude .......",
start = time.time()
while True:
  maude_output_line = maude.stdout.readline()
  if maude_output_line.startswith("Bye"): break

  if maude_output_line.startswith(maude_output_prefix):
    maude_output_line = maude_output_line[len(maude_output_prefix):]
    maude_output_line = maude_output_line.rstrip("\n")

    if maude_output_line.startswith(maude_timer_prefix):
      maude_output_line = maude_output_line[len(maude_timer_prefix):]
      end = time.time()
      elapsed = yellow_color + "%.3f" % round(end - start, 3) + "s" + no_color
      start = end
      print maude_output_line + " [" + elapsed + "]"
    elif maude_output_line.startswith(maude_rewrites_prefix):
      maude_output_line = maude_output_line[len(maude_rewrites_prefix):]
      end = time.time()
      elapsed = yellow_color + "%.3f" % round(end - start, 3) + "s" + no_color
      print maude_output_line + " [" + elapsed + ",",
    else:
      print maude_output_line,
  else:
    if maude_output_line.startswith("rewrites"):
      rewrites = cyan_color + maude_output_line.split()[1] + no_color
      print rewrites + " rewrites,",
    elif maude_output_line.strip().startswith("< feasible >"):
      counter = maude_output_line.strip().split()[3][15:-10]
      feasible = green_color + counter + no_color
      print feasible + " feasible and",
    elif maude_output_line.strip().startswith("< infeasible >"):
      counter = maude_output_line.strip().split()[3][15:-10]
      infeasible = red_color + counter + no_color
      print infeasible + " infeasible paths]",
    else:
      tmp_out_file.write(maude_output_line)

