import sys
import socket
import subprocess


TIMEOUT = 0.5                   # SMT querry timeout, in seconds
HOST = 'localhost'              # Symbolic name meaning all available interfaces
PORT = 7070                     # Arbitrary non-privileged port
BUFSIZ = 4096                   # Buffer size
MAUDE_EOF = '###EOMTCP###';     # Maude querry string terminator


Z3_cmd_list = ["(declare-sorts (IntSeq))",
               "(declare-funs ((len IntSeq Int)))",
               "(assert (forall (A IntSeq) (>= (len A) 0)))"]


def initZ3():
    cmd = "z3"
    cmd += " -smtc"
    cmd += " -si"
    cmd += " -t:" + str(TIMEOUT)
    Z3 = subprocess.Popen(cmd, shell=True, bufsize=0,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    
    for Z3_cmd in Z3_cmd_list:
        Z3.stdin.writelines([Z3_cmd + "\n"])
        print Z3_cmd + "\n" + Z3.stdout.readline().strip()
    
    return Z3


def callZ3(Z3_querry):
    Z3.stdin.writelines(["(push)\n"])
    if Z3.stdout.readline().strip() != "success": return "unknown"
    
    for Z3_cmd in Z3_querry:
        Z3.stdin.writelines([Z3_cmd + "\n"])
        result = Z3.stdout.readline().strip()
        print Z3_cmd + "\n" + result
        if result != "success": break
    
    Z3.stdin.writelines(["(pop)\n"])
    if Z3.stdout.readline().strip() != "success": return "unknown"    
    
    return result


Z3 = initZ3()
len = len(sys.argv)
if len > 1: HOST = sys.argv[1]
if len > 2: PORT = int(sys.argv[2])

serversocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
serversocket.bind((HOST, PORT))
serversocket.listen(1)

while True:
    conn, addr = serversocket.accept()
    print "receiving querry from ", addr
    
    msg = ""
    while True:
        data = conn.recv(BUFSIZ)
        msg += data
        if not data or data.find(MAUDE_EOF) != -1: break
    querry = msg[0:data.find(MAUDE_EOF)].split("\n")
    
    result = callZ3(querry)

    print "sending result to", addr
    conn.send(result)
    conn.close()
