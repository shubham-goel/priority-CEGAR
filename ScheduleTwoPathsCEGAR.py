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
from Utilities import *

def save_to_file(S,filename):
	file = open(filename, 'w')
	pickle.dump(S, file)
	file.close()

def GeneratePriorities(stng, mdl, M):
	'''
	Returns (message) priorities such that for every vertex v,
	priorities[v] is a list of messages ordered in descending message priority
	'''
	if not mdl:
		return mdl

	priorities={}
	for v in stng.g.V:
		priorities[v]=[]

	for m in M:
		for v in stng.UFSv[m]:
			for i in range(len(M)):
				if is_true(mdl[stng.vars.priority(m,v,i)]):
					priorities[v].append((i,m))

	for v in stng.g.V:
		priorities[v] = sorted(priorities[v], key=lambda student: student[0])
		priorities[v] = [priorities[v][j][1] for j in range(len(priorities[v]))]

	return priorities

def definePriorityVariables(stng, M):
	'''
	Initaializes/defines message priority variables
	'''
	for m in M:
		for v in stng.UFSv[m]:
			# message m has priority j at vertex v
			for j in range(len(M)):
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

def getUniqueConfigConstr(stng,m,v,i):
	'''
	Returns a constraint that guarantees that m is on v at time i, and not on any other vertex.
	'''
	notThere = And([Not(stng.vars.config(m, u, i)) for u in stng.UFSv[m] if u != v])
	here = stng.vars.config(m, v, i)
	return And(here, notThere)

def getUniqueUsedConstr(stng,m,v,e,i):
	'''
	Returns a constraint that guarantees that m at v uses e at time i, and not on any other edge.
	'''
	notThere = And([Not(stng.vars.used(m, e1, i)) for e1 in stng.edge_priority[m][v] if e1 != e])
	here = stng.vars.used(m, e, i)
	return And(here, notThere)

def defineSimulationVariables(stng, M, t,
	k_omissions=0, k_crashes=0, k_delays=0):
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
			for i in range(t+1):
				stng.vars.def_config(m,v,i)

			for e in stng.edge_priority[m][v]:
				for i in range(t):
					# is message m using e at i
					stng.vars.def_used(m,e,i)

		# has message arrived destination
		stng.vars.def_msgArrive(m)

	for e in stng.g.E:
		for i in range(t):

			# Is there an omission fault at e at time i
			if k_omissions>0:
				stng.vars.def_omit(e,i)

			# Is there a crash fault at e at time i
			if k_crashes>0:
				stng.vars.def_crash(e,i)

			# Is there a delay fault at e at time i
			if k_delays>0:
				stng.vars.def_delay(e,i)

def print_priorities(stng,M):
	'''
	print edge priorities
	'''
	for m in M:
		print "Message " + str(m) + " :: {}-->{}".format(str(m.s),str(m.t))
		print "------------\n"

		for v in stng.UFSv[m]:
			print "\tvertex : " + str(v)
			for e in stng.edge_priority[m][v]:
				print "\t\tEdge "+str(e)

def print_message_priorities(stng,mdl,M):
	'''
	print edge priorities
	'''
	pr = GeneratePriorities(stng,mdl,M)
	print "\nMESSAGE PRIORITIES"
	print "------------------"

	for v in stng.g.V:
		print "Vertex : " + str(v)
		for m in pr[v]:
			print "\tMessage "+str(m)

def generalSimulationConstraints(stng,s, M, t, l, immediatefailure=False):
	'''
	Adds constraints that depend neither on k nor on priority model
	'''

	# messages start at their origin
	for m in M:
		s.add(getUniqueConfigConstr(stng, m, m.s, 0))


	# if a message reaches its destination, it stays there.
	for m in M:
		for i in range(t):
			s.add(Implies(stng.vars.config(m, m.t, i), getUniqueConfigConstr(stng, m, m.t, i+1)))

	s.add(Sum([If(stng.vars.config(m, m.t, t), 1, 0) for m in M]) < l)


	for m in M:
		for v in stng.UFSv[m]:
			for e in stng.edge_priority[m][v]:
				for i in range(t):

					# If e is omitted, stay where you are. Else, move
					if_else = If(stng.vars.omit(e,i),
									getUniqueConfigConstr(stng,m,e.s,i+1),
									getUniqueConfigConstr(stng,m,e.t,i+1))

					s.add(Implies(stng.vars.used(m,e,i),if_else))

	for e in stng.g.E:
		for i in range(t):
			# once an edge crashes, it stays down
			if i > 0:
				s.add(Implies(stng.vars.crash(e, i-1), stng.vars.crash(e, i)))

		#require that if an edge fails, it fails at time 0
		if immediatefailure:
			s.add(Implies(stng.vars.crash(e, t-1), stng.vars.crash(e, 0)))

def specificSimulationConstraints(stng,s, pr, M, t, l,
	k_omissions=0,k_crashes=0,k_delays=0):
	'''
	Add simulation contraints specific to pr and not to k
	'''

	for v in stng.g.V:
		for m in pr[v]:

			lhss = []
			for i in range(t):
				lhss.append([])

			for e in stng.edge_priority[m][v]:
				# assert e.s == v
				for i in range(t):
					# No higher priority message uses e
					mj_e = []
					for m2 in pr[v]:
						if m2 == m: break
						mj_e.append(stng.vars.used_ex(m2,e,i))

					# Message doesnt use higher priority edge
					m_ej = []
					for e2 in stng.edge_priority[m][v]:
						if e2 == e: break
						m_ej.append(stng.vars.used(m,e2,i))

					pos = stng.vars.config(m,v,i)
					nocrash = Not(stng.vars.crash(e,i))
					# Edge e is free according to priorities
					free_edge = And(Not(Or(mj_e)),Not(Or(m_ej)))

					lhs = And(pos,nocrash,free_edge)
					s.add(Implies(lhs,getUniqueUsedConstr(stng,m,v,e,i)))

					lhss[i].append(lhs)

			for i in range(t):
				# No lhs is satisfied
				no_lhs = Not(Or(lhss[i]))
				# m doesnt use any edge at i
				# This implies m stays at v, if it is at vertex v at time i
				lst = Not(Or([stng.vars.used(m,e,i) for e in stng.edge_priority[m][v]]))
				s.add(Implies(no_lhs,lst))
				s.add(Implies(And(lst,stng.vars.config(m,v,i)),getUniqueConfigConstr(stng,m,v,i+1)))

def k_maxSimulationConstraints(stng,s, t, exact=False,
	k_omissions=0,k_crashes=0,k_delays=0):
	'''
	Add constraints specific to k only
	'''

	# Take care of number of omissions
	sum_expr = []
	for e in stng.g.E:
		for i in range(t):
			sum_expr.append(If(stng.vars.omit(e,i),1,0))
	if exact:
		s.add(Sum(sum_expr) == k_omissions)
	else:
		s.add(Sum(sum_expr) <= k_omissions)


	# Take care of number of crashes
	if exact:
		s.add(Sum([If(stng.vars.crash(e,t-1), 1, 0) for e in stng.g.E]) == k_crashes)
	else:
		s.add(Sum([If(stng.vars.crash(e,t-1), 1, 0) for e in stng.g.E]) <= k_crashes)

	# Take care of number of delays
	sum_expr = []
	for e in stng.g.E:
		for i in range(t):
			sum_expr.append(If(stng.vars.delay(e,i),1,0))
	if exact:
		s.add(Sum(sum_expr) == k_delays)
	else:
		s.add(Sum(sum_expr) <= k_delays)

def saboteurStrategy(stng, S, M, t, l,
	k_omissions=0, k_crashes=0, k_delays=0):
	'''
	Returns a Saboteur stratergy, if any
	Returns False if no such Stratergy Exists
	'''
	# Initiate new solver for network simulation
	s = Solver()

	defineSimulationVariables(stng, M, t,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
	generalSimulationConstraints(stng,s, M, t, l)
	specificSimulationConstraints(stng, s, S, M, t, l,)
	k_maxSimulationConstraints(stng,s, t, exact=False,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

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

def excludeCrashModel(stng,s,crash_model,t,
	omissions=False,crashes=False,delays=False):
	crashes = []
	for e in stng.g.E:
		for i in range(t):
			# omissions
			if omissions:
				if is_true(crash_model[stng.vars.omit(e,i)]):
					crashes.append(stng.vars.omit(e,i))
				else:
					crashes.append(Not(stng.vars.omit(e,i)))

			# crashes
			if crashes:
				if is_true(crash_model[stng.vars.crash(e,i)]):
					crashes.append(stng.vars.crash(e,i))
				else:
					crashes.append(Not(stng.vars.crash(e,i)))

			# delays
			if delays:
				if is_true(crash_model[stng.vars.delay(e,i)]):
					crashes.append(stng.vars.delay(e,i))
				else:
					crashes.append(Not(stng.vars.delay(e,i)))
	s.add(Not(And(crashes)))

def count_WFS(stng, pr, M, t, l,
	k_omissions=0,k_crashes=0,k_delays=0):
	'''
	Count number of fault sequence that performs at most k faults
	and in which less than l messages arrive
	'''
	s = Solver()

	defineSimulationVariables(stng, M, t,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
	generalSimulationConstraints(stng,s, M, t, l)
	specificSimulationConstraints(stng, s, pr, M, t, l)
	k_maxSimulationConstraints(stng,s, t, exact=False,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	counter = 0

	while True:
		if s.check() == sat:
			crash_model = s.model()
			print "FOUND {}".format(counter)
			printCounterexample(stng, crash_model, t, M)
			printConfigurations(stng, crash_model, t, M)
			counter += 1
			excludeCrashModel(stng,s,crash_model,t,
				omissions=(k_omissions>0),crashes=(k_crashes>0),delays=(k_delays>0))
		else:
			break

	return counter

def successProb(stng, pr, M, t, l,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	Returns the probability of pr failing, given the crash parameters
	Exactly k_(omissions/crashes/delays) omissions/crashes/delays occur
	'''
	s = Solver()

	defineSimulationVariables(stng, M, t,
		k_omissions=1,k_crashes=1,k_delays=1)
	generalSimulationConstraints(stng,s, M, t, l)
	specificSimulationConstraints(stng, s, pr, M, t, l)

	lower_bound=0
	upper_bound=1


	k_omissions=0
	k_crashes=0
	k_delays=0

	while True:
		if AskContinue(lower_bound,upper_bound,k_crashes) is False:
			break

		# create backtracking point for successive values of k
		s.push()


		k_maxSimulationConstraints(stng,s, t, exact=False,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

		p1 = saboteurProbability(stng,s,t,M,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
			p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
		p2 = crashesProbability(stng,M,t,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
			p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

		# Update Bounds
		lower_bound += p2 - p1
		upper_bound -= p1

		s.pop()

		k_omissions=0
		k_crashes=k_crashes+1
		k_delays=0

	return (lower_bound,upper_bound)

def saboteurProbability(stng,s,t,M,
	k_omissions=0,k_crashes=0,k_delays=0,
	p_omissions=0,p_crashes=0,p_delays=0):

	checkSupport(k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	crash_data_sum = []
	while True:
		if s.check() == sat:
			crash_model = s.model()

			dat = get_crash_data(stng,crash_model,t,M)
			sum_i = math.fsum([x[1] for x in dat])
			crash_data_sum.append(sum_i)

			excludeCrashModel(stng,s,crash_model,t,
				omissions=(k_omissions>0),crashes=(k_crashes>0),delays=(k_delays>0))
		else:
			break
	return prob_not_AMA(len(stng.g.E),t,
			p_crashes=p_crashes,k_crashes=k_crashes,k_crashes_list=crash_data_sum)

def crashesProbability(stng,M,t,
	k_omissions=0,k_crashes=0,k_delays=0,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	Returns the probability that exactly k crashes/delays/omissions occur
	'''
	checkSupport(k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	num_edges = len(stng.g.E)
	return prob_crash_parameters(num_edges,t,
			p_crashes=p_crashes,k_crashes=k_crashes)

def checkSupport(k_omissions=0, k_crashes=0, k_delays=0):
	if k_delays > 0:
		raise
	if k_omissions > 0:
		raise

def CEGAR(stng, M, t, l,
	k_omissions=0, k_crashes=0, k_delays=0,
	optimize=False, showProgress=False, countFaults=False,
	probabalistic=False):
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
	# for getting good initial message priorities

	mdl = getModel(s)
	if not mdl:
		#redundant: print 'NO valid model EXISTS'
		return False

	if countFaults:
		pr = GeneratePriorities(stng, mdl, M)
		print_message_priorities(stng,mdl,M)
		print "\n\nCounting Sabeteur Strategies for Schedule now...", time.time()
		start_time = time.time()

		num_faults = count_WFS(stng, pr, M, t, l,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

		end_time = time.time()
		count_time = end_time-start_time
		print "Number of distinct stratergies = {}\n\n".format(str(num_faults))
		print "Time taken = {}\n\n".format(str(count_time))
		print "End Time", time.time()
		return (num_faults,count_time)

	elif probabalistic:
		pr = GeneratePriorities(stng, mdl, M)
		print_message_priorities(stng,mdl,M)

		p_omissions=0.01
		p_crashes=0.01
		p_delays=0.01

		print "\nCalculating Probabilities now...", time.time()
		start_time = time.time()

		prob = successProb(stng, pr, M, t, l,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

		end_time = time.time()
		count_time = end_time-start_time
		print "\nProbability Interval = {}\n\n".format(prob)
		print "Time taken = {}\n\n".format(str(count_time))
		print "End Time", time.time()
		return (prob,count_time)

	else:
		raise ValueError("Only implemented counting of faults and probablistic setting")

	while True:
		#redundant: print j,counter
		#redundant: j += 1
		#redundant: counter += 1

		#redundant: if counter > 20:
			#redundant: return "Timeout"

		#mdl is has the information about the message priorities
		pr = GeneratePriorities(stng, mdl, M)

		crash_mdl = saboteurStrategy(stng, pr, M, t, l,
			k_omissions=k_omissions, k_crashes=k_crashes, k_delays=k_delays)

		if not crash_mdl:
			#redundant: print 'FOUND (k-l) resistant schedule', "k=",','.join([k_omissions,k_crashes,k_delays]),"l=",l
			#redundant: print pr
			#redundant: save_to_file(pr,'schedules/Schedule_k'+','.join([k_omissions,k_crashes,k_delays])+'_l'+str(l))
			l+=1
			#redundant: counter=1
			continue

		#redundant: if showProgress:
		#redundant: 	printProgress(stng, pr, M, t, l,
		#redundant: 		k_omissions=k_omissions, k_crashes=k_crashes, k_delays=k_delays)

		learnt = learnConstraints(stng, s, crash_mdl, M, t, optimize, l, S=pr)
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
				k_omissions=k_omissions, k_crashes=k_crashes, k_delays=k_delays, returnSolver=True)
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
			edge = g(v,v.nextF(m))
			if edge is not None:
				edge_priority[m][v].append(edge)
		for v in UFSv[m]:
			edge = g(v,v.nextS(m))
			if edge is not None:
				edge_priority[m][v].append(edge)
	return edge_priority

def printConfiguration(stng, crash_model, t, M, i):
	for m in M:
		for v in stng.UFSv[m]:
			if is_true(crash_model[stng.vars.config(m,v,i)]):
				print "{} at vertex {} at time {}".format(m,v,i)

def printConfigurations(stng, crash_model, t, M):
	for i in range(t):
		print "TIME {}".format(i)
		printConfiguration(stng, crash_model, t, M, i)

def get_crash_data(stng, mdl, t, M):
	res = []
	for e in stng.g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.crash(e,i)]):
				# print 'edge: %s crashed at time %d'%(str(e), i)
				res.append((e,i))
				break
	return res

def printCounterexample(stng, mdl, t, M):
	for e in stng.g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.omit(e,i)]):
				print 'edge: %s omitted at time %d'%(str(e), i)
	return

def main(n, m, e, t, l,
	k_omissions=0, k_crashes=0, k_delays=0,
	filename=None, save=False, load=False,
	optimize=False, showProgress=False, weight=False, countFaults=False,
	probabalistic=False):

	(g, M, FCv, FCe, SCv, SCe, UFSv) = GenerateSetting(n, m, e, save=save,
		load=load, filename=filename, weight=weight)
	vars = Vars()

	stng = Glbl(g, vars, FCe, FCv, SCv, SCe, UFSv, getEdgePriorities(g, FCv, UFSv, M))
	printMessagesInfo(stng, M)
	print_priorities(stng,M)

	S = CEGAR(stng, M, t, l,
		k_omissions=k_omissions, k_crashes=k_crashes, k_delays=k_delays,
		optimize=optimize, showProgress=showProgress, countFaults=countFaults,
		probabalistic=probabalistic)

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
				  help="Counts number of Saboteur winning stratergies given Schedule")
	parser.add_option("-p","--prob",
				  action="store_true", dest="probabalistic", default=False,
				  help="Calculates probability of winning given Runner Stratergy (Priorities)")
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
	probabalistic = options.probabalistic
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
		k_omissions=k,filename=filename, save=save, load=load, optimize=optimize,
		showProgress=showProgress, weight=weight, countFaults=countFaults,
		probabalistic=probabalistic)
