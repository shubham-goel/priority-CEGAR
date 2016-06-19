import sys

sys.path.append("bin")

import time
import pickle
import itertools
import subprocess
import math
from optparse import OptionParser
from decimal import Decimal
import multiprocessing

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
	print 'RUNNING successProb'
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
			# BIT-ADDED BASED SAT COUNTING
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
	p_omissions=0,p_crashes=0,p_delays=0, RR='message'):
	'''
	Serves the same purpose as successProb
	Returns the probability of pr failing, given the crash parameters
	Implements a MessageRR Algorithm
	'''
	print 'RUNNING priorityScore'
	assert l==len(M)
	s = Goal()

	glbl_vars.init()

	print_time("Simulating network...")
	defineSimulationVariables(stng, M, t, basic_names=False)
	generalSimulationConstraints(stng,s, M, t, l, l_is_upperBound=False)
	specificSimulationConstraints(stng, s, pr, M, t, l, RR=RR)

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

def monte_carlo_Score(stng, pr, M, t, l,
	p_omissions=0,p_crashes=0,p_delays=0,
	epsilon=0.2,confidence=0.8,RR='edge'):
	print_time('RUNNING monte_carlo_Score')

	assert epsilon>0 and epsilon<1
	assert confidence>0 and confidence<1

	num_iterations = 1/(2*float(epsilon**2))*math.log(1/(1-float(confidence)))
	num_iterations = int(math.ceil(num_iterations))
	print 'num_iterations',num_iterations

	successful_iter = 0

	for i in range(num_iterations):
		if RR=='edge':
			sim_result = rand_sim_EdgeRR(stng, pr, M, t, l,
							p_omissions=p_omissions,p_crashes=p_crashes)
		elif RR=='message':
			sim_result = rand_sim_MessageRR(stng, pr, M, t, l,
							p_omissions=p_omissions,p_crashes=p_crashes)
		else:
			raise

		if sim_result:
			successful_iter += 1

	print_time('ENDED monte_carlo_Score')

	return float(successful_iter)/float(num_iterations)

def monte_carlo_Score_thread(stng, pr, M, t, l,
	p_omissions=0,p_crashes=0,p_delays=0,
	epsilon=0.2,confidence=0.8,RR='edge',
	num_threads = 5):
	print_time('RUNNING monte_carlo_Score_thread')

	assert epsilon>0 and epsilon<1
	assert confidence>0 and confidence<1

	num_iterations = 1/(2*float(epsilon)**2)*math.log(1/(1-float(confidence)))
	num_iterations = int(math.ceil(num_iterations))
	print 'num_iterations',num_iterations

	successful_iter = 0

	jobs=[]
	remaining_iter = num_iterations
	manager = multiprocessing.Manager()
	return_dict = manager.dict()

	for i in range(num_threads):
		n_iter = (remaining_iter)/(num_threads-i)
		remaining_iter -= n_iter

		if RR=='edge':
			p = multiprocessing.Process(target=rand_sim_EdgeRR_thread,
										args=(return_dict,n_iter, i, stng, pr,
										M, t, l, p_omissions,p_crashes,))
		elif RR=='message':
			p = multiprocessing.Process(target=rand_sim_MessageRR_thread,
										args=(return_dict,n_iter, i, stng, pr,
										M, t, l, p_omissions,p_crashes,))
		else:
			raise

		jobs.append(p)
		p.start()

	print 'WAITING FOR PROCESSES TO END...'
	for p in jobs:
		p.join()
	print 'ALL PROCESSES ENDED...'

	iter_count = 0
	for key in return_dict.keys():
		successful_iter += return_dict[key][0]
		iter_count += return_dict[key][1]

	assert iter_count == num_iterations

	print 'return_dict',return_dict
	print_time('ENDED monte_carlo_Score_thread')
	return float(successful_iter)/float(num_iterations)

def rand_sim_EdgeRR_thread(output_dict,num_iter,id_thread, stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):
	successful_iter = 0
	for i in range(num_iter):
		if rand_sim_EdgeRR(stng, pr, M, t, l,
				p_omissions=p_omissions,p_crashes=p_crashes):
			successful_iter+=1
	output_dict[id_thread] = (successful_iter,num_iter)
	return (successful_iter,num_iter)

def rand_sim_MessageRR_thread(output_dict,num_iter,id_thread, stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):
	successful_iter = 0
	for i in range(num_iter):
		if rand_sim_MessageRR(stng, pr, M, t, l,
				p_omissions=p_omissions,p_crashes=p_crashes):
			successful_iter+=1
	output_dict[id_thread] = (successful_iter,num_iter)
	return (successful_iter,num_iter)

def rand_sim_EdgeRR(stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):

	sim_vars = Sim_Vars()

	for e in stng.g.E:
		sim_vars.queue[e] = []

	# Setup Initial queues
	for m in M:
		v = m.s
		e = stng.edge_priority[m][v][0]
		sim_vars.queue[e].append(m)

	for e in stng.g.E:
		sim_vars.crash[e] = False

	msg_arrived = []
	T=[]

	# ITERATE FOR EVERY TIME
	for time in range(timeout):
		# Choose edges to crash
		for e in stng.g.E:
			sim_vars.crash[e] = sim_vars.crash[e] or get_prob_true(p_crashes)
			if sim_vars.crash[e]:
				T.append(e)

		# Move mesages to new queue
		for e in T:
			for m in sim_vars.queue[e]:

				# Find first message with lower priority that hasn't crashed
				e2 = e
				while e2!=None and sim_vars.crash[e2]:
					assert e2.s == e.s
					index_curr = stng.edge_priority[m][e2.s].index(e2)
					index_curr += 1
					try:
						e2 = stng.edge_priority[m][e2.s][index_curr]
					except IndexError:
						e2 = None

				if e2 is not None:
					sim_vars.queue[e].remove(m)
					sim_vars.queue[e2].append(m)

		# Attempt to send mesages over link
		for e in stng.g.E:
			if not sim_vars.crash[e]:
				# Find highest priority message in queue and send it
				status = True
				for m in pr[e.s]:
					if m in sim_vars.queue[e]:
						# Found message in queue
						if status:
							# This is the first message we got
							sim_vars.used[m] = e
							status = False

							assert m in sim_vars.queue[e]

						else:
							# All lower priority messages should not move
							sim_vars.used[m] = None
			else:
				# The messages in this queue should not move
				for m in sim_vars.queue[e]:
					sim_vars.used[m] = None

		# Decide if edges  omit
		for m in M:
			e = sim_vars.used[m]

			if e is not None:

				assert m in sim_vars.queue[e]

				sim_vars.omit[e] = get_prob_true(p_omissions)
				if sim_vars.omit[e] == False:
					if e.t == m.t:
						sim_vars.queue[e].remove(m)
						msg_arrived.append(m)
						sim_vars.used[m] = None
					else:
						next_edge = stng.edge_priority[m][e.t][0]
						sim_vars.queue[e].remove(m)
						sim_vars.queue[next_edge].append(m)

	return len(msg_arrived) >= l

def rand_sim_MessageRR(stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):

	sim_vars = Sim_Vars()

	# Setup initial config
	for m in M:
		sim_vars.config[m] = m.s

	# Reset vars
	for e in stng.g.E:
		sim_vars.crash[e] = False
		sim_vars.used[e] = False

	msg_arrived = []
	T=[]

	# ITERATE FOR EVERY TIME
	for time in range(timeout):
		# reset edge usage
		for e in stng.g.E:
			sim_vars.used[e] = False

		# Choose edges to crash
		for e in stng.g.E:
			sim_vars.crash[e] = sim_vars.crash[e] or get_prob_true(p_crashes)
			if sim_vars.crash[e]:
				T.append(e)

		# Attempt to send highest priority mesages over link
		for v in stng.g.V:
			for m in pr[v]:
				if v == sim_vars.config[m]:
					next_e = None
					for e in stng.edge_priority[m][v]:
						if not sim_vars.used[e] and not sim_vars.crash[e]:
							next_e = e
							break
					sim_vars.used[m] = next_e
					if next_e is not None:
						sim_vars.used[next_e] = True

		# Decide if edges  omit
		for m in M:
			e = sim_vars.used[m]
			if e is not None:
				assert sim_vars.config[m] == e.s
				sim_vars.omit[e] = get_prob_true(p_omissions)

				# Update message config
				if sim_vars.omit[e] == False:
					sim_vars.config[m] = e.t
					if e.t == m.t:
						msg_arrived.append(m)

	return len(msg_arrived) >= l

def saboteurProbability(stng,s,pr,M,t,l,
	k_omissions=0,k_crashes=0,k_delays=0,
	p_omissions=0,p_crashes=0,p_delays=0,
	optimize=False):

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
						p_crashes=p_crashes,k_crashes=crashed)
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
	# print_time("implementing heuristic...")
	# prioritySimulationConstraints(stng, s, M, t, pr, l)

	print_time("solving z3 program...")
	mdl = getModel(s)
	if not mdl:
		print 'NO valid model EXISTS'
		return False

	print_time("generating priorities...")
	pr = GeneratePriorities(stng, mdl, M)

	# if load_priority:
	# 	pr = load_priority_from_file(stng, M, "priorities.curr")
	# if save_priority:
	# 	save_priority_to_file(stng, pr, "priorities.curr")

	print_message_priorities(stng,mdl,M)

	if countFaults:

		print_time("\n\nCounting Sabeteur Strategies for Schedule now...")
		num_faults = count_WFS(stng, pr, M, t, l,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
		print_time("Ended Counting Sabeteur Strategies...")

		print "Number of distinct stratergies = {}\n\n".format(str(num_faults))
		print "End Time", time.time()

		return (num_faults,count_time)

	elif probabalistic:

		p_omissions=0.0
		p_crashes=0.25
		p_delays=0
		precision=50

		p_omissions=reduce_precision(p_omissions,precision)
		p_crashes=reduce_precision(p_crashes,precision)
		p_delays=reduce_precision(p_delays,precision)

		print_time("\nCalculating Probabilities now...")
		start_time = time.time()

		timings = {}

		# timings[-3]=time.time()
		# prob0o = successProb(stng, pr, M, t, l,optimize=True,naive=True,
		# 			p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
		# timings[-2]=time.time()
		# prob0a = successProb(stng, pr, M, t, l,optimize=False,naive=True,
		# 			p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
		timings[-1]=time.time()
		prob1e = priorityScore(stng, pr, M, t, l,optimize=optimize,precision=precision,
					p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays,
					RR='edge')
		timings[0]=time.time()
		prob1m = priorityScore(stng, pr, M, t, l,optimize=optimize,precision=precision,
					p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays,
					RR='message')
		timings[0.1]=time.time()
		# prob2e = monte_carlo_Score(stng, pr, M, t, l,RR='edge',
		# 			p_omissions=p_omissions,p_crashes=p_crashes,
		# 			epsilon=0.01,confidence=0.999)
		timings[1]=time.time()
		prob2et = monte_carlo_Score_thread(stng, pr, M, t, l,RR='edge',
					p_omissions=p_omissions,p_crashes=p_crashes,
					epsilon=0.01,confidence=0.999)
		timings[2]=time.time()
		# prob2m = monte_carlo_Score(stng, pr, M, t, l,RR='message',
		# 			p_omissions=p_omissions,p_crashes=p_crashes,
		# 			epsilon=0.01,confidence=0.999)
		timings[3]=time.time()
		prob2mt = monte_carlo_Score_thread(stng, pr, M, t, l,RR='message',
					p_omissions=p_omissions,p_crashes=p_crashes,
					epsilon=0.01,confidence=0.999)
		timings[4]=time.time()

		print ''
		print ''
		print '#Final Probabilities:'
		print ''
		# print 'successProb OPT              \t',prob0o,timings[-2]-timings[-3]
		# print 'successProb NO OPT           \t',prob0a,timings[-1]-timings[-2]
		print 'priorityScore edgeRR         \t',prob1e,timings[0]-timings[-1]
		print 'priorityScore messageRR      \t',prob1m,timings[0.1]-timings[0]
		# print 'monte_carlo edgeRR           \t',prob2e,timings[1]-timings[0.1]
		print 'monte_carlo thread edgeRR    \t',prob2et,timings[2]-timings[1]
		# print 'monte_carlo messageRR        \t',prob2m,timings[3]-timings[2]
		print 'monte_carlo thread messageRR \t',prob2mt,timings[4]-timings[3]
		print ''
		print ''

		prob = prob1e

		end_time = time.time()
		count_time = end_time-start_time
		print "Total Time taken = {}\n\n".format(str(count_time))
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

def main(n, m, e, t, l,
	k_omissions=0, k_crashes=0, k_delays=0,
	filename=None, save=False, load=False, custom=False,
	optimize=False, showProgress=False, weight=False, countFaults=False,
	probabalistic=False):

	print_time("generating setting...")
	(g, M, FCv, FCe, SCv, SCe, UFSv) = GenerateSetting(n, m, e, save=save,
		load=load, filename=filename, weight=weight, custom=custom)
	vars = Vars()

	stng = Glbl(g, vars, FCe, FCv, SCv, SCe, UFSv, getEdgePriorities(g, FCv, UFSv, M))
	print_edges(stng)
	printMessagesInfo(stng, M)
	print "\n"
	print_priorities(stng,M)

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

	custom = options.custom
	load = options.load or custom
	save = not load
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
		probabalistic=probabalistic, custom=custom)
