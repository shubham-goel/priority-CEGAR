import sys
import subprocess
import pickle

def load_from_file(filename):
	file = open(filename, 'rb')
	return  pickle.load(file)


def save_to_file(S,filename):
	file = open(filename, 'wb')
	pickle.dump(S, file, protocol=2)
	file.close()

def vaildate_exit_code(exit_code):
	acceptable=[0,10,20]
	if exit_code in acceptable:
		return True
	else:
		return False

def run_bash(cmd,timeout=None):
	try:
		exit_code = subprocess.call([cmd],shell=True,timeout=timeout)
		if not vaildate_exit_code(exit_code) :
			print("Exit Status error! status={}\nError cmd={}".format(exit_code,cmd))
			return 'error'
		else:
			return 'success'
	except :
		return 'timeout'

cmd=load_from_file(sys.argv[1])

if len(sys.argv) < 4:
	timeout=None
else:
	timeout=int(sys.argv[3])

output = run_bash(cmd,timeout=timeout)

save_to_file(str(output),str(sys.argv[2]))
