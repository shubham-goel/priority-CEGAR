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
from Constraints import *

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

def excludeCrashModel(stng,s,crash_model,t,add_crashes=False,at_t_only=False,
	omissions=False,crashes=False,delays=False):
	exclude_crashes = []
	for e in stng.g.E:
		for i in range(t):

			if at_t_only:
				i = t

			# omissions
			if omissions:
				if is_true(crash_model[stng.vars.omit(e,i)]):
					exclude_crashes.append(stng.vars.omit(e,i))
				else:
					exclude_crashes.append(Not(stng.vars.omit(e,i)))

			# crashes
			if crashes:
				if is_true(crash_model[stng.vars.crash(e,i)]):
					exclude_crashes.append(stng.vars.crash(e,i))
				else:
					exclude_crashes.append(Not(stng.vars.crash(e,i)))

			# delays
			if delays:
				if is_true(crash_model[stng.vars.delay(e,i)]):
					exclude_crashes.append(stng.vars.delay(e,i))
				else:
					exclude_crashes.append(Not(stng.vars.delay(e,i)))

			if at_t_only:
				break

	if add_crashes:
		s.add(And(exclude_crashes))
	else:
		s.add(Not(And(exclude_crashes)))

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
	k_maxSimulationConstraints(stng,s, t, exact=True,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	counter = 0

	while True:
		if s.check() == sat:
			crash_model = s.model()
			print "FOUND {}".format(counter)
			printCounterexample(stng, crash_model, t, M)
			# printConfigurations(stng, crash_model, t, M)
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

	defineSimulationVariables(stng, M, t)
	generalSimulationConstraints(stng,s, M, t, l)
	specificSimulationConstraints(stng, s, pr, M, t, l)

	lower_bound=0
	upper_bound=1


	k_omissions=0
	k_crashes=0
	k_delays=0

	end_time=0
	start_time=0

	while True:
		count_time = end_time-start_time
		print "Time taken = {}".format(count_time)
		if AskContinue(lower_bound,upper_bound,k_crashes) is False:
			break

		# create backtracking point for successive values of k
		s.push()

		start_time = time.time()

		k_maxSimulationConstraints(stng,s, t, exact=True,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

		p1 = saboteurProbability(stng,s,pr,M,t,l,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
			p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
		p2 = crashesProbability(stng,M,t,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
			p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

		end_time = time.time()

		# Update Bounds
		lower_bound += p2 - p1
		upper_bound -= p1

		s.pop()

		k_omissions=0
		k_crashes=k_crashes+1
		k_delays=0

	return (lower_bound,upper_bound)

def saboteurProbability(stng,s,pr,M,t,l,
	k_omissions=0,k_crashes=0,k_delays=0,
	p_omissions=0,p_crashes=0,p_delays=0,
	optimize=False):

	# print "Crash parameters",k_omissions,k_crashes,k_delays
	checkSupport(k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	count=0
	prob = 0
	while True:
		if s.check() == sat:
			crash_model = s.model()
			# printCounterexample(stng, crash_model, t, M)

			# This part is for permanent crashes only
			if optimize is True:

				doomed = get_doomed_state(stng, pr, M, t, l,
							k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

				omitted,crashed,delayed = printCounterexample(stng, crash_model, doomed, M,count=True)
				p1 = get_model_prob(stng,crash_model,doomed,M,
						p_crashes=p_crashes,k_crashes=k_crashes)
				p2 = crashesProbability(stng,M,t-doomed,crashed=crashed,
						k_omissions=k_omissions-omitted,k_crashes=k_crashes-crashed,k_delays=k_delays-delayed,
						p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
				prob += p1*p2
				excludeCrashModel(stng,s,crash_model,doomed,
					omissions=(k_omissions>0),crashes=(k_crashes>0),delays=(k_delays>0))
			else:
				prob += get_model_prob(stng,crash_model,t,M,
							p_crashes=p_crashes,k_crashes=k_crashes)

				excludeCrashModel(stng,s,crash_model,t,
					omissions=(k_omissions>0),crashes=(k_crashes>0),delays=(k_delays>0))
				count += 1
		else:
			break
	print "Count = {}".format(count)
	return prob

def get_doomed_state(stng, pr, M, t, l,
	k_omissions=0,k_crashes=0,k_delays=0):
	'''
	Returns the smallest time t such that the configuration at t is doomed
	All crash models which follow crash_model till time t and have k crashes
	result in <l messages to be delivered
	'''
	sOpt = solver()
	defineSimulationVariables(stng, M, t)
	generalSimulationConstraints(stng,sOpt, M, t, l,l_is_upperBound=False)
	specificSimulationConstraints(stng, sOpt, pr, M, t, l)
	k_maxSimulationConstraints(stng,sOpt, t, exact=True,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	doomed = 0

	while True:
		crash_model = getModel(sOpt)
		if crash_model is False:
			break
		excludeCrashModel(stng,sOpt,crash_model,doomed,add_crashes=True,at_t_only=True,
			omissions=True,crashes=True,delays=True)
		doomed += 1

	return doomed

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
		k_crashes=k,filename=filename, save=save, load=load, optimize=optimize,
		showProgress=showProgress, weight=weight, countFaults=countFaults,
		probabalistic=probabalistic)
