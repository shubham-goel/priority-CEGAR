import sys
import subprocess
import pickle
import threading

class Command(object):
    def __init__(self, cmd):
        self.cmd = cmd
        self.process = None

    def run(self, timeout):
        def target():
            print('Thread started')
            self.process = subprocess.Popen(self.cmd, shell=True)
            print('pid=',self.process.pid)
            self.process.communicate()
            print('Thread finished')

        thread = threading.Thread(target=target)
        thread.start()

        thread.join(timeout)
        if thread.is_alive():
            print('Terminating process')
            self.process.kill()
            # thread.join()
            print ('returncode=',self.process.returncode)
            return 'timeout'
        print ('returncode=',self.process.returncode)
        if self.process.returncode == 0:
        	return 'success'
        else:
        	return 'error'


def load_from_file(filename):
	file = open(filename, 'rb')
	return  pickle.load(file)


def save_to_file(S,filename):
	file = open(filename, 'wb')
	pickle.dump(S, file, protocol=2)
	file.close()

def run_bash(cmd,timeout=None):
	try:
		if subprocess.call([cmd],shell=True,timeout=timeout) == 1 :
			print("Exit Status error!")
			return 'error'
		else:
			return 'success'
	except :
		return 'timeout'

print('RUNNING PY3!')

cmd=load_from_file(sys.argv[1])
print('cmd',cmd)

if len(sys.argv) < 4:
	timeout=None
else:
	timeout=int(sys.argv[3])

# .......................
# cmd = Command(cmd)
# output = cmd.run(timeout=timeout)
# .......................
output = run_bash(cmd,timeout=timeout)
# .......................
print('output',output)

save_to_file(str(output),str(sys.argv[2]))
