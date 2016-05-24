import sys

sys.path.append("bin")

import time
import pickle
import itertools
import subprocess
from optparse import OptionParser

from z3 import *

from Objects import *
from Graph import GenerateSetting

def save_to_file(S,filename):
	file = open(filename, 'w')
	pickle.dump(S, file)
	file.close()

def GeneratePriorities(stng, mdl, M):
	priorities={}
	for v in stng.g.V:
		priorities[v]={}

	for m in M:
		for v in stng.UFSv[m]:
			for i in range(len(M)):
				if is_true(mdl[stng.vars.priority(m,v,i)]):
					priorities[v][m] = i

	return priorities

def definePriorityVariables(stng, M):
	'''
	Initaializes/defines message priority variables
	'''
	for m in M:
		for v in stng.UFSv[m]:
			# message m has priority j at vertex v
			for j in range(t):
				stng.vars.def_priority(m,v,j)

def addPriorityConstraints(stng, M, s=None):
	'''
	Adds priority-uniqueness contraints to solvers:
	No 2 messages have the same priority
	Every message has exactly one priority
	'''
	if s is None:
		s=Solver()
		definePriorityVariables(stng, M)

	for m in M:
		for v in stng.UFSv[m]:

			# No 2 messages have the same priority
			unique_message = []
			# Every message has at most one priority
			unique_priority = []

			for i in range(len(M)):
				
				unique_message = [stng.vars.priority(m2,v,i)
								for m2 in M if  m2 != m and v in stng.UFSv[m2]]
				unique_priority = [stng.vars.priority(m,v,j)
								for j in range(len(M)) if  j != i]
				
				disconjunct = Or([Or(unique_message),Or(unique_priority)])
				
				s.add(Implies(stng.vars.priority(m,v,i),Not(disconjunct)))

			# Every message has at least one priority
			priority_existence = [stng.vars.priority(m,v,j)
									for j in range(len(M))]
			s.add(Or(priority_existence))

	return s

def getModel(s):
	if s.check() == sat:
		return s.model()
	else:
		return False

def defineSimulationVariables(stng, M, t,
	k_omission=0, k_crashes=0, k_delays=0):
	'''
	Initiate/Define the following variables for simulating network:
	-configuration variables
	-used variables
	-message arrival variables
	-crash variables
	-delay variables
	-omission variables
	'''
	for m in M:
		
		for v in stng.UFSv[m]:
			# is message m at vertex v at time i
			for i in range(t):
				stng.vars.def_config(m,v,i)

		for e in stng.FCe[m]:
			for i in range(len(M)):
				# is message m using e at i
				stng.vars.def_used(m,e,i)

		# has message arrived destination
		stng.vars.def_msgArrive(m)

	for e in stng.g.E:
		for i in range(t):
			
			if k_omission>0:
				stng.vars.def_omit(e,i)
			
			if k_crashes>0:
				stng.vars.def_crash(e,i)
			
			if k_delays>0:
				stng.vars.def_delay(e,i)

# TODO
def addSimulationConstraints(stng,s, S, M, t, l,
	k_omission=0,k_crashes=0,k_delays=0):
	'''
	Add simulation contraints to solver s
	'''
	return False

def saboteurStrategy(stng, S, M, t, l,
	k_omission=0, k_crashes=0, k_delays=0):
	'''
	Returns a Saboteur stratergy, if any
	Returns False if no such Stratergy Exists
	'''
	# Initiate new solver for network simulation
	s = Solver()
	
	defineSimulationVariables(stng, M, t,
		k_omission=k_omission,k_crashes=k_crashes,k_delays=k_delays)

	addSimulationConstraints(stng, s, S, M, t, l,
		k_omission=k_omission,k_crashes=k_crashes,k_delays=k_delays)

	crash_mdl=getModel(s)

	return crash_mdl

# TODO
def learnConstraints(stng, s, crash_mdl, M, t, optimize, l, S=None):
	'''
	Learn constraints from crash_mdl,
	Add them to solver s
	
	Return False if no such constraints exist,
	Then no (k-l) resistant schedules exist
	'''
	return False

def CEGAR(stng, M, t, l,
	k_omission=0, k_crashes=0, k_delays=0,
	optimize=False, showProgress=False, countFaults=False):
	'''
	:param M: The messages to be sent
	:param t: The timeout.
	:param l: At least l messages should arrive.
	:return: A (k,l)-resistant schedule, if it exists, and otherwise False.
	'''
	#redundant: j = 1
	#redundant: counter=1

	s = Solver()

	# Add priority uniqueness constraints
	definePriorityVariables(stng, M)
	addPriorityConstraints(stng, M, s=s)

	# Add HERE more heuristics/constraints
	# for getting good initial priorities

	mdl = getModel(s)
	if not mdl:
		#redundant: print 'NO valid model EXISTS'
		return False

	while True:
		#redundant: print j,counter
		#redundant: j += 1
		#redundant: counter += 1

		#redundant: if counter > 20:
			#redundant: return "Timeout"

		#mdl is has the information about the priorities
		S = GeneratePriorities(stng, mdl, M)

		crash_mdl = saboteurStrategy(stng, S, M, t, l,
			k_omission=k_omission, k_crashes=k_crashes, k_delays=k_delays)

		if not crash_mdl:
			#redundant: print 'FOUND (k-l) resistant schedule', "k=",','.join([k_omission,k_crashes,k_delays]),"l=",l
			#redundant: print S
			#redundant: save_to_file(S,'schedules/Schedule_k'+','.join([k_omission,k_crashes,k_delays])+'_l'+str(l))
			l+=1
			#redundant: counter=1
			continue

		#redundant: if showProgress:
		#redundant: 	printProgress(stng, S, M, t, l,
		#redundant: 		k_omission=k_omission, k_crashes=k_crashes, k_delays=k_delays)

		learnt = learnConstraints(stng, s, crash_mdl, M, t, optimize, l, S=S)
		if  learnt is False:
			#redundant: print 'NO (k-l) resistant schedule EXISTS', "k=",k,"l=",l
			return False
			
		#redundant: print 'start check()', time.time()
		mdl = getModel(s)
		#redundant: print 'end check()', time.time()

		if mdl is False:
			#redundant: print 'NO (k-l) resistant schedule EXISTS', "k=",k,"l=",l
			return False


def printProgress(stng, S, M, t, l, k):
	low = 0
	high = l
	rest = 0

	mid = (high + low)/2
	mdl,s = printProgress(stng, S, M, t, mid,
				k_omission=k_omission, k_crashes=k_crashes, k_delays=k_delays, returnSolver=True)
	while low < high:
		#redundant: print 'print progress start iteration', time.time()
		if mdl is False:
			low = mid+1
			rest = mid
		else:
			high = mid-1

		mid = (high + low)/2

		s.pop()
		s.push()
		s.add(Sum([If(stng.vars.config(m.t, m, t), 1, 0) for m in M]) < mid)

		if s.check() == sat:
			print mid
			#redundant: printCounterexample(stng, s.model(), t, M)
			mdl = True
		else:
			rest = mid
			mdl = False
	#redundant: print 'The schedule is (%d, %d)-resistant'%(rest, k)

def printMessagesInfo(stng, M):
	for m in M:
		print m.id, '%s --> %s'%(m.s, m.t)
		print ', '.join([str(v) for v in stng.FCv[m]])
		print ', '.join(['%s --> %s'%(str(v), str(v.nextS(m))) for v in stng.UFSv[m]])
		print '################'

	lengths = [len(stng.FCe[m]) for m in M]
	print 'max length = ', max(lengths), "min length = ", min(lengths)

def getEdgePriorities(g, FCv, UFSv, M):
	'''
	Return Edge Priority data from First and Second Path
	Return first and second priority edges as:
	edge_priority[m][v][0] and edge_priority[m][v][1]
	'''
	edge_priority = {}
	for m in M:
		edge_priority[m]= {}
		for v in g.V:
			edge_priority[m][v] = []
		for v in FCv[m]:
			edge_priority[m][v].append(g(v,v.nextF(m)))
		for v in UFSv[m]:
			edge_priority[m][v].append(g(v,v.nextS(m)))
	return edge_priority

def main(n, m, e, t, l,
	k_omission=0, k_crashes=0, k_delays=0,
	filename=None, save=False, load=False,
	optimize=False, showProgress=False, weight=False, countFaults=False):

	(g, M, FCv, FCe, SCv, SCe, UFSv) = GenerateSetting(n, m, e, save=save,
		load=load, filename=filename, weight=weight)
	vars = Vars()

	stng = Glbl(g, vars, FCe, FCv, SCv, SCe, UFSv, getEdgePriorities(g, FCv, UFSv, M))
	printMessagesInfo(stng, M)

	S = CEGAR(stng, M, t, l,
		k_omission=k_omission, k_crashes=k_crashes, k_delays=k_delays,
		optimize=optimize, showProgress=showProgress, countFaults=countFaults)

	if S == "Timeout":
		print 'Script Timed out'
		return 1
	else:
		print 'Finished CEGAR!'
		return 0

def parse_arguments():
	parser = OptionParser()
	parser.add_option('-t','--timeout', dest="t",
				  help="The timeout, should be an integer")
	# parser.add_option("-l", dest="l",
	# 			  help="The guarantee on the number of messages that should arrive.")
	parser.add_option("-k", dest="k",
				  help="#edges that are allowed to crash.")
	parser.add_option("-n", dest="n",
				  help="#vertices in the network.")
	parser.add_option("-m", dest="m",
				  help="#messages in the network.")
	parser.add_option("-e", dest="e",
				  help="#edges in the network.")

	parser.add_option("-l","--load",
				  action="store_true", dest="load", default=False,
				  help="Load setting from file")
	parser.add_option("-b","--brute",
				  action="store_false", dest="optimize", default=True,
				  help="Dont Optimize")
	parser.add_option("-v","--verbose",
				  action="store_true", dest="showProgress", default=False,
				  help="Dont show progress")
	parser.add_option("--nw","--no-weight",
				  action="store_false", dest="weight", default=True,
				  help="Choose paths without weights")
	parser.add_option("-d","--no-diff",
				  action="store_true", dest="diff", default=False,
				  help="Check if schedules generated are different")
	parser.add_option("-c","--count",
				  action="store_true", dest="countFaults", default=False,
				  help="Counts number of Sabeteur winning stratergies given Schedule")
	return parser.parse_args()

def clearFolder(folder):
	cmd = "rm -r "+ folder
	subprocess.call([cmd],shell=True)
	cmd = "mkdir "+ folder
	subprocess.call([cmd],shell=True)


if __name__ == '__main__':
	(options, args) = parse_arguments()

	save = not options.load
	load = options.load
	optimize = options.optimize
	showProgress = options.showProgress
	weight = options.weight
	diff = options.diff
	countFaults = options.countFaults
	n = int(sys.argv[1])
	m = int(sys.argv[2])
	e = int(sys.argv[3])
	t = int(sys.argv[4])
	l = int(sys.argv[5])
	k = int(sys.argv[6])

	# filename='{}-{}-{}-{}-{}-{}.setting'.format(n,m,e,t,k,l)
	filename="settings.curr"

	# Remove old Schedules
	clearFolder("schedules/")

	# main(n, m, e, t, k, l, filename=None, save=False, load=False, optimize=False, showProgress=False, weight=False):
	# main(int(options.n), int(options.m), int(options.e), int(options.t), int(options.l), int(options.k))
	# main(10, 30, 15, 7, 26, 1, filename, save=True, load=False, optimize=True, showProgress=True, weight=True)
	exit_status = main(n,m,e,t,l,
		k_omission=k,filename=filename, save=save, load=load, optimize=optimize,
		showProgress=showProgress, weight=weight, countFaults=countFaults)
