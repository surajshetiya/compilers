#!/usr/bin/python
import glob
import subprocess
import os

op = [];
for file in glob.glob('tests/*'):
    command1 = 'scala /home/ubuntu/workspace/pcat/lib/pcat.jar 4 /home/ubuntu/workspace/pcat/'+file;
    op1 = os.popen(command1).read()
    command2 = 'scala /home/ubuntu/workspace/pcat/pcat-solution.jar 4 /home/ubuntu/workspace/pcat/'+file;
    op2 = os.popen(command2).read()
    if(op1 != op2):
        op.append(file);
print("Mismatch : " + str(op))