import sys

sys.path.append("bin")

import time
import pickle
import itertools
import subprocess
import math
from optparse import OptionParser
from decimal import Decimal

from z3 import *

import global_vars as glbl_vars
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
	if at_t_only:
		begin_time=t
		end_time=t+1
	else:
		begin_time=0
		end_time=t

	exclude_crashes = []

	for e in stng.g.E:
		for i in range(begin_time,end_time):

			assert ((at_t_only is False) or (i==t))
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

def successProb(stng, pr, M, t, l,optimize=False,naive=True,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	Returns the probability of pr failing, given the crash parameters
	'''
	print p_omissions,p_crashes,p_delays
	if naive:
		s = Solver()
	else:
		s = myGoal()

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
		if k_crashes>len(stng.g.E): break

		# create backtracking point for successive values of k
		s.push()

		start_time = time.time()

		if naive:
			k_maxSimulationConstraints(stng,s, t, exact=True,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

			p1 = saboteurProbability(stng,s,pr,M,t,l,optimize=optimize,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
			p2 = crashesProbability(stng,M,t,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

			# Update Bounds
			lower_bound += p2 - p1
			upper_bound -= p1

		else:
			# COMPUTES ONLY BOUNDS ON PRIORITY
			k_maxSimulationConstraints_BOOL(stng,s, t, exact=True,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

			# Process and save Formula to file
			glbl_vars.init()
			cnf_file = "umc_dimacs{}.txt".format(k_crashes)
			sol_file = "num_sols.txt"
			# tact = Tactic('tseitin-cnf')
			tact = With('tseitin-cnf',distributivity=False)
			print_time("cnf to dimacs...")
			cnf = tact(s.get_goal())[0]
			print "Number of clauses = ",len(cnf)
			dimacs = cnf_to_DIMACS(cnf)
			print_time("saving dimacs to file...")
			save_DIMACS_to_file(dimacs,cnf_file)

			print "k_crashes=",k_crashes

			# approxMC, cryptominsat take too long to run
			# # Run approxMC on file
			# # print_time("##################running MIS on file...")
			# # cmd = 'cd mis/ && python MIS.py -output=../mis.out {}'.format('../'+cnf_file)
			# # run_bash(cmd)
			# # with open("mis.out", "r") as f_temp:
			# # 	c_ind = f_temp.read()
			# # 	c_ind = "c ind {}".format(c_ind[2:])
			# # with open("mis.out", "w") as f_temp:
			# # 	f_temp.write(c_ind)
			# # cmd = "cat {} >> {} && mv {} {}".format(cnf_file,'mis.out','mis.out',cnf_file)
			# # run_bash(cmd)
			# print_time("##################running approxMC on file...")
			# cmd = "./scalmc --pivotAC 71 --tApproxMC 3 {} > {}".format(cnf_file, sol_file)
			# run_bash(cmd)

			# Run sharpSAT on file
			print_time("#################running sharpSAT on file...")
			cmd = "./sharpSAT {} > {}".format(cnf_file, sol_file)
			run_bash(cmd)

			# Process sharpSat output to get #Sols
			print_time("################reading sharpSat's output...")
			numSols = process_sharpSat_output(sol_file)
			print "num_sols={}".format(numSols)

			lb=numSols*((1-p_crashes)**(t*(len(stng.g.E))-k_crashes))*(p_crashes**k_crashes)
			ub=numSols*((1-p_crashes)**(t*(len(stng.g.E)-k_crashes)))*(p_crashes**k_crashes)
			print "lb={}, ub={}".format(lb,ub)

			p2 = crashesProbability(stng,M,t,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
			print "p2={}".format(p2)

			# Update Bounds
			lower_bound += p2 - ub
			upper_bound -= lb

			if lower_bound<0:
				lower_bound = 0

			# USE FOR DEBUGGING
			# counter = 0
			# s_solver = s.get_solver()

			# print "USING NAIVE APPROACH NOW"
			# while True:
			# 	if s_solver.check() == sat:
			# 		crash_model = s_solver.model()
			# 		print "FOUND {}".format(counter)
			# 		# printCounterexample(stng, crash_model, t, M)
			# 		# printConfigurations(stng, crash_model, t, M)
			# 		counter += 1
			# 		excludeCrashModel(stng,s_solver,crash_model,t,
			# 			omissions=(k_omissions>0),crashes=(k_crashes>0),delays=(k_delays>0))
			# 	else:
			# 		break

			# assert counter==numSols

		end_time = time.time()

		s.pop()

		k_omissions=0
		k_crashes=k_crashes+1
		k_delays=0

	return (lower_bound,upper_bound)

def priorityScore(stng, pr, M, t, l,optimize=False,precision=0,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	Serves the same purpose as successProb
	Returns the probability of pr failing, given the crash parameters
	'''
	assert l==len(M)
	s = Goal()

	glbl_vars.init()

	print_time("Simulating network...")
	defineSimulationVariables(stng, M, t, basic_names=False)
	generalSimulationConstraints(stng,s, M, t, l, l_is_upperBound=False)
	specificSimulationConstraints(stng, s, pr, M, t, l)

	print_time("setting weight vars...")
	weight_vars, normalization_factor = set_weight_vars(stng, s, M, t,precision=precision,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

	print_time("converting to unweighted...")
	denom = wieghted_to_unweighted(stng,s,weight_vars,t,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

	print "denom = 2**{}".format(math.log(denom,2))
	print "normalization_factor = {}".format(normalization_factor)

	# Process and save Formula to file
	glbl_vars.init()
	cnf_file = "umc_dimacs.txt"
	sol_file = "num_sols.txt"
	# t = Tactic('tseitin-cnf')
	t = With('tseitin-cnf',distributivity=False)
	print_time("cnf to dimacs...")
	cnf = t(s)[0]
	print "Number of clauses = ",len(cnf)
	dimacs = cnf_to_DIMACS(cnf)
	print_time("saving dimacs to file...")
	save_DIMACS_to_file(dimacs,cnf_file)

	# Run SharpSat on file
	print_time("running SharpSat on file...")
	cmd = "./sharpSAT {} > {}".format(cnf_file, sol_file)
	if subprocess.call([cmd],shell=True) == 1 :
		print("Exit Status error!")
	else:
		print("SUCCESS!")

	# Process SharpSat output to get #Sols
	print_time("reading SharpSat's output...")
	numSols = process_sharpSat_output(sol_file)

	denom = Decimal(normalization_factor)*Decimal(denom)
	prob = Decimal(numSols)/denom
	print "\n\n"
	print "numSols = {}".format(numSols)
	print "denom = {}".format(denom)
	print "prob = {}".format(+prob)

	return +prob

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

				doomed = get_doomed_state(stng, crash_model, pr, M, t, l,
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

def get_doomed_state(stng, crash_model, pr, M, t, l,
	k_omissions=0,k_crashes=0,k_delays=0):
	'''
	Returns the smallest time t such that the configuration at t is doomed
	All crash models which follow crash_model till time t and have k crashes
	result in <l messages to be delivered
	'''
	sOpt = Solver()
	defineSimulationVariables(stng, M, t)
	generalSimulationConstraints(stng,sOpt, M, t, l,l_is_upperBound=False)
	specificSimulationConstraints(stng, sOpt, pr, M, t, l)
	k_maxSimulationConstraints(stng,sOpt, t, exact=True,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
	# print "Added Constraints"

	doomed = 0

	while True:
		temp_crash_model = getModel(sOpt)
		if temp_crash_model is False:
			# There exists no crash sequence  in which at least l messages arrive
			# Hence, We have found a doomed state.
			break
		assert doomed<=t
		excludeCrashModel(stng,sOpt,crash_model,doomed,add_crashes=True,at_t_only=True,
			omissions=True,crashes=True,delays=True)
		doomed += 1

	# print "Returning doomed state={}\n".format(doomed)
	return doomed

def CEGAR(stng, M, t, l,
	k_omissions=0, k_crashes=0, k_delays=0,
	optimize=False, showProgress=False, countFaults=False,
	probabalistic=False,load_priority=False,save_priority=False):
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
	print_time("defining priority vars...")
	pr = definePriorityVariables(stng, M, heuristic=True)
	print_time("defining simulation vars...")
	defineSimulationVariables(stng, M, t)
	print_time("adding priority constraints...")
	addPriorityConstraints(stng, M, s=s) #BOTTLENECK1

	# Add HERE more heuristics/constraints
	# for getting good initial message priorities
	print_time("implementing heuristic...")
	prioritySimulationConstraints(stng, s, M, t, pr, l)

	print_time("solving z3 program...")
	mdl = getModel(s)
	if not mdl:
		print 'NO valid model EXISTS'
		return False

	if countFaults:
		pr = GeneratePriorities(stng, mdl, M)
		print_message_priorities(stng,mdl,M)
		print_time("\n\nCounting Sabeteur Strategies for Schedule now...")
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
		print_time("generating priorities...")
		pr = GeneratePriorities(stng, mdl, M)

		# if load_priority:
		# 	pr = load_priority_from_file(stng, M, "priorities.curr")
		# if save_priority:
		# 	save_priority_to_file(stng, pr, "priorities.curr")

		# print_message_priorities(stng,mdl,M)

		p_omissions=0
		p_crashes=0.01
		p_delays=0
		precision=7

		p_omissions=reduce_precision(p_omissions,precision)
		p_crashes=reduce_precision(p_crashes,precision)
		p_delays=reduce_precision(p_delays,precision)

		print_time("\nCalculating Probabilities now...")
		start_time = time.time()

		# prob = successProb(stng, pr, M, t, l,optimize=optimize,naive=False,
		# 		p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
		prob = priorityScore(stng, pr, M, t, l,optimize=optimize,precision=precision,
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

	print_time("generating setting...")
	(g, M, FCv, FCe, SCv, SCe, UFSv) = GenerateSetting(n, m, e, save=save,
		load=load, filename=filename, weight=weight)
	vars = Vars()

	stng = Glbl(g, vars, FCe, FCv, SCv, SCe, UFSv, getEdgePriorities(g, FCv, UFSv, M))
	# printMessagesInfo(stng, M)
	# print "\n"
	# print_priorities(stng,M)

	print_time("Starting Cegar loop...")
	S = CEGAR(stng, M, t, l,
		k_omissions=k_omissions, k_crashes=k_crashes, k_delays=k_delays,
		optimize=optimize, showProgress=showProgress, countFaults=countFaults,
		probabalistic=probabalistic,save_priority=save,load_priority=load)

	if S == "Timeout":
		print 'Script Timed out'
		return 1
	else:
		print 'Finished CEGAR!'
		return 0

if __name__ == '__main__':
	glbl_vars.init()
	glbl_vars.last_time = time.time()

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

	exit_status = main(n,m,e,t,l,
		k_crashes=k,filename=filename, save=save, load=load, optimize=optimize,
		showProgress=showProgress, weight=weight, countFaults=countFaults,
		probabalistic=probabalistic)
