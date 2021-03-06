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
from AdverserialModel import *

def SAT_count(stng, pr, M, t, l, RR='message',
	exact=True, approximate=False, immediate_failure=False, build_MIS='no'):
	'''
	A simple SAT count of the number of formulae satisfying setting.
	This mimics temporary crashes with probability 0.5 and is the best formula
	a SAT counter can hope to obtain.
	'''
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING SAT_count...')
	print ''
	print "RR",RR
	print "exact",exact
	print "approximate",approximate
	print "immediate_failure",immediate_failure
	print "build_MIS",build_MIS
	print ''

	s = Goal()
	glbl_vars.init()

	defineSimulationVariables(stng, M, t, basic_names=False)
	generalSimulationConstraints(stng,s, M, t, l, l_is_upperBound=False,
									temporary_crashes=True)
	specificSimulationConstraints(stng, s, pr, M, t, l, RR=RR)
	no_crashConstraint(stng,s,t,crash_type='omit')

	if immediate_failure:
		immediatefailureConstraints(stng,s,t,0)
		denom = Decimal(2**len(stng.g.E))
	else:
		denom = Decimal(2**(len(stng.g.E)*t))

	glbl_vars.init()
	cnf_file = "umc_dimacs_{}.txt".format(len(stng.g.V))
	sol_file = "umc_dimacs_{}.txt.sol".format(len(stng.g.V))
	mis_cnf_file = cnf_file+'.ind'

	cnf_file = "umc_dimacs.txt"
	sol_file = "num_sols.txt"
	tact = With('tseitin-cnf',distributivity=False)
	cnf = tact(s)[0]
	dimacs = cnf_to_DIMACS(cnf)
	save_DIMACS_to_file(dimacs,cnf_file)

	if exact:
		# Run sharpSAT on file---------------------------
		print_time("\nrunning sharpSAT on file...")
		numSols,sharpSAT_time = run_sharpSAT(cnf_file,sol_file,return_time=True)
		if not (isinstance(numSols,int) or isinstance(numSols,long)):
			print "numSols is not integral"
			print "Type =",type(numSols)
			print "sharpSAT_time = {}".format(sharpSAT_time)
			print "numSols = {}".format(numSols)
			print "\n"
			prob = numSols
		else:
			prob = Decimal(numSols)/denom
			prob = +prob
			print "\n\n"
			print "sharpSAT_time = {}".format(sharpSAT_time)
			print "numSols = {}".format(numSols)
			print "prob = {}".format(prob)
			print "\n"

	if approximate:
		if build_MIS == 'yes' or build_MIS == 'both':
			# Run MIS+approxMC on file-----------------------
			print_time("\nrunning mis on file...")
			mis_output,mis_time=run_mis(cnf_file,mis_cnf_file)
			if mis_time != 'timeout':
				assert mis_output=='success'
				print_time("running approxMC on file...")
				numSols_approxMC_mis,approxMC_mis_time=run_approxMC(mis_cnf_file)
			else:
				numSols_approxMC_mis=0
				approxMC_mis_time='timeout'
			print "\n\n"
			print "mis_time = {}".format(mis_time)
			print "approxMC_mis_time = {}".format(approxMC_mis_time)
			print "numSols_approxMC_mis = {}".format(numSols_approxMC_mis)
			print "\n"
			# -----------------------------------------------

		if build_MIS == 'no' or build_MIS == 'both':
			# Run only ApproxMC on file---------------------------
			print_time("\nrunning approxMC on file...")
			numSols_approxMC,approxMC_time=run_approxMC(cnf_file)
			print "\n\n"
			print "approxMC_time = {}".format(approxMC_time)
			print "numSols_approxMC = {}".format(numSols_approxMC)
			print "\n"
			# -----------------------------------------------

def count_WFS(stng, pr, M, t, l,
	k_crashes=0,k_omissions=0,k_delays=0):
	'''
	NOT USED for Scoring
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: minimum number of messages that should arrive on time
	:param k_crashes: maximum number of edges that crash
	:param k_omissions: maximum number of edges that omit
	:param k_delays: (must be 0) maximum number of edges that delay

	:return: the number of at most k crash fault sequences with BAD outcome

	Less than l messages arrive in a BAD outcome
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

def weightMC(stng, pr, M, t, l,epsilon=0.01,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: (must be m) minimum number of messages that should arrive on time
	:param epsilon: the maximum desired uncertainity
	:param p_omissions: (must be 0) omission probability
	:param p_crashes: crash probability
	:param p_delays: (must be 0) delay probability

	:return: Approximate score of pr, within uncertainity epsilon

	This uses a distribution-aware-sampling approximate WMC tool
	'''
	assert p_omissions==0
	assert p_delays==0
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING weightMC...')
	print ''
	print 'p_omissions={}\np_crashes={}'.format(p_omissions,p_crashes)
	print ''

	s = myGoal()

	st_time=time.time()
	rt_dat = {}
	rt_dat['timing_time'] = 0
	rt_dat['k_maxSimulationConstraints_BOOL'] = {}
	rt_dat['z3 sat'] = {}
	rt_dat['z3 check'] = {}
	rt_dat['z3 to cnf'] = {}
	rt_dat['cnf to dimacs'] = {}
	rt_dat['timing_time'] += time.time() - st_time


	print 'Adding constraints...',time.time()
	st_time=time.time()
	defineSimulationVariables(stng, M, t)
	generalSimulationConstraints(stng,s, M, t, l, l_is_upperBound=True)
	specificSimulationConstraints(stng, s, pr, M, t, l)
	rt_dat['generate program'] = time.time() - st_time

	lower_bound=0
	upper_bound=1

	n = len(stng.g.V)
	m = len(M)
	e = len(stng.g.E)
	l = m

	k_omissions=0
	k_crashes=0
	k_delays=0

	end_time=0
	start_time=0
	func_start_time=time.time()

	print_time('STARTING weightMC Iterations')
	while True:
		# count_time = end_time-start_time
		# print "Time taken = {}".format(count_time)
		# if AskContinue(lower_bound,upper_bound,k_crashes) is False:
		if upper_bound-lower_bound < epsilon:
			break
		if k_crashes>len(stng.g.E): break
		print '----------------------k_crashes =',k_crashes,'-----------------------'

		# create backtracking point for successive values of k
		s.push()

		start_time = time.time()

		# BIT-ADDED BASED SAT COUNTING
		# COMPUTES ONLY BOUNDS ON PRIORITY
		print 'Adding k_maxSimulationConstraints...',time.time()
		st_time=time.time()
		k_maxSimulationConstraints_BOOL(stng,s, t, exact=True,
			k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
		rt_dat['k_maxSimulationConstraints_BOOL'][k_crashes] = time.time() - st_time

		flag=False
		temp_time=time.time()
		if s.get_solver().check() == sat:
			print 'Sat!'
			flag=True
			rt_dat['z3 sat'][k_crashes]=True
			rt_dat['z3 check'][k_crashes]=time.time()-temp_time

			magnification=1

			t3=print_time("setting weight vars...")
			weight_vars, normalization_factor, magnification = set_weight_vars(stng, s, M, t,precision=100,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays,
				magnification=magnification,output_range=8)
			glbl_vars.init()
			cnf_file = "weightMC_dimacs{}.txt".format(k_crashes)
			sol_file = "weightMC_num_sols{}.txt".format(k_crashes)
			# tact = Tactic('tseitin-cnf')
			tact = With('tseitin-cnf',distributivity=False)
			t4=print_time("z3 to cnf...")
			cnf = tact(s.get_goal())[0]
			t5=print_time("cnf to dimacs...")
			glbl_vars.init_weight_vars_to_number()
			dimacs = cnf_to_DIMACS(cnf,record_wv_mapping=True)
			t6=print_time("saving dimacs to file...")
			save_DIMACS_to_file(dimacs,cnf_file,weight_vars=weight_vars,magnification=magnification)

			# Run SharpSat on file
			t7=print_time("running weightMC on file...")
			weightMC_numSols, weightMC_time = run_weightMC(cnf_file,sol_file)

			st_time=time.time()
			rt_dat['z3 to cnf'][k_crashes]=t5-t4
			rt_dat['cnf to dimacs'][k_crashes]=t6-t5
			rt_dat['timing_time'] += time.time() - st_time
		else:
			print 'Unsat!'
			rt_dat['z3 sat'][k_crashes]=False
			rt_dat['z3 check'][k_crashes]=time.time()-temp_time
			weightMC_numSols=0
			normalization_factor=1
			weightMC_time=rt_dat['z3 check'][k_crashes]

		# =======================================
		# Uncomment this block to compare the approximation with
		# the answer returned by the literal WMC approach
		# ============Block Start================

		# if flag:
		# 	t3=print_time("Running SHARPSAT\nconverting to unweighted...")
		# 	denom = wieghted_to_unweighted(stng,s,weight_vars,t,
		# 				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

		# 	print ''
		# 	print "denom = 2**{}".format(math.log(denom,2))
		# 	print "normalization_factor = {}".format(normalization_factor)
		# 	print ''

		# 	# Process and save Formula to file
		# 	glbl_vars.init()
		# 	cnf_file = "umc_dimacs{}.txt".format(k_crashes)
		# 	sol_file = "umc_num_sols{}.txt".format(k_crashes)
		# 	# tact = Tactic('tseitin-cnf')
		# 	tact = With('tseitin-cnf',distributivity=False)
		# 	t4=print_time("z3 to cnf...")
		# 	cnf = tact(s.get_goal())[0]
		# 	t5=print_time("cnf to dimacs...")
		# 	dimacs = cnf_to_DIMACS(cnf)
		# 	t6=print_time("saving dimacs to file...")
		# 	save_DIMACS_to_file(dimacs,cnf_file)

		# 	# Run SharpSat on file
		# 	t7=print_time("running SharpSat on file...")
		# 	sharpSAT_numSols,sharpSAT_time = run_sharpSAT(cnf_file,sol_file,return_time=True)
		# 	if not (isinstance(sharpSAT_numSols,int) or isinstance(sharpSAT_numSols,long)):
		# 		print "\n\n"
		# 		print "numSols is not integral"
		# 		print "Type =",type(sharpSAT_numSols)
		# 		print "sharpSAT_time = {}".format(sharpSAT_time)
		# 		print "numSols = {}".format(sharpSAT_numSols)
		# 		print "\n"
		# 		prob = sharpSAT_numSols
		# 	else:
		# 		denom = Decimal(normalization_factor)*Decimal(denom)
		# 		prob = Decimal(sharpSAT_numSols)/denom
		# 		prob = +prob
		# 		print "\n\n"
		# 		print "sharpSAT_time = {}".format(sharpSAT_time)
		# 		print "numSols = {}".format(sharpSAT_numSols)
		# 		print "denom = {}".format(denom)
		# 		print "prob = {}".format(prob)
		# 		print "\n"

		# 	print "\n\nWMC method:",str(prob),sharpSAT_time
		# 	print "WeightMC method:",float(str(weightMC_numSols))/normalization_factor,weightMC_time,'\n\n'

		# ============Block End================

		if weightMC_numSols == 'timeout':
			print "Timeout"
			print_time('RETURNING weightMC...')
			print '###############################################'
			print '###############################################'
			print ''
			return ((lower_bound,upper_bound),'Timeout'),rt_dat

		print 'weightMC_numSols',weightMC_numSols
		print 'normalization_factor',normalization_factor

		p1 = float(str(weightMC_numSols))/normalization_factor
		p2 = crashesProbability(stng,M,t,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

		# Update Bounds
		lower_bound += p2 - p1
		upper_bound -= p1

		print '\n\n'
		print 'p1',p1
		print 'p2',p2
		print 'Time = {}'.format(weightMC_time)
		print 'Bounds',lower_bound,upper_bound
		print 'Uncertainity',upper_bound-lower_bound
		print '\n\n'

		s.pop()

		k_omissions=0
		k_crashes=k_crashes+1
		k_delays=0

	print_time('RETURNING weightMC...')
	print '###############################################'
	print '###############################################'
	print ''
	return (lower_bound,upper_bound),rt_dat

def IterativeApproach(stng, pr, M, t, l,distinct_crashes=True,optimize=False,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: (must be m) minimum number of messages that should arrive on time
	:param distinct_crashes: all crashes do NOT occur simultaneously, z3 Based
	:param optimize: use doomed state optimization. Works with distinct_crashes only
	:param p_omissions: (must be 0) omission probability
	:param p_crashes: crash probability
	:param p_delays: (must be 0) delay probability

	:return: Score of priority scheme

	The  number of crashes is fixed to k,
	the corresponding score is calculated for successive values of k.

	distinct_crashes=True
		The score is calculated by iterating (using z3) over
		all crash sequences that lead to BAD outcomes,
		and subtracting their probability from the score.

		When optimize=True,
			A dommed state optimization is used.
			Not all BAD outcomed crash sequences are iterated over.

	distinct_crashes=False
		The entire state space of k crashes occuring is not explored
		The space is limited to when all k crashes occur simultaneously
	'''
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING IterativeApproach...')
	print ''
	print 'optimize={}\ndistinct_crashes={}\np_omissions={}\np_crashes={}'.format(optimize,distinct_crashes,p_omissions,p_crashes)
	print ''
	if distinct_crashes:
		s = Solver()
	else:
		s = myGoal()

	st_time=time.time()
	rt_dat = {}
	rt_dat['timing_time'] = 0
	rt_dat['k_maxSimulationConstraints_BOOL'] = {}
	rt_dat['immediatefailureConstraints'] = {}
	rt_dat['saboteurProbability'] = {}
	rt_dat['numSols_sharpSAT'] = {}
	rt_dat['numSols_approxMC'] = {}
	rt_dat['numSols_approxMC_mis'] = {}
	rt_dat['sharpSAT_time'] = {}
	rt_dat['approxMC_time'] = {}
	rt_dat['mis_time'] = {}
	rt_dat['approxMC_mis_time'] = {}
	rt_dat['z3 to cnf'] = {}
	rt_dat['cnf to dimacs'] = {}
	rt_dat['timing_time'] += time.time() - st_time


	print 'Adding constraints...',time.time()
	st_time=time.time()
	defineSimulationVariables(stng, M, t)
	generalSimulationConstraints(stng,s, M, t, l)
	specificSimulationConstraints(stng, s, pr, M, t, l)
	rt_dat['generate program'] = time.time() - st_time

	lower_bound=0
	upper_bound=1

	n = len(stng.g.V)
	m = len(M)
	e = len(stng.g.E)
	l = m

	k_omissions=0
	k_crashes=0
	k_delays=0

	end_time=0
	start_time=0
	func_start_time=time.time()

	print_time('STARTING IterativeApproach Iterations')
	while True:
		count_time = end_time-start_time
		print "Time taken = {}".format(count_time)
		if AskContinue(lower_bound,upper_bound,k_crashes) is False:
			break
		if k_crashes>len(stng.g.E): break
		print '----------------------k_crashes =',k_crashes,'-----------------------'

		# create backtracking point for successive values of k
		s.push()

		st_time=time.time()
		rt_dat['immediatefailureConstraints'][k_crashes] = {}
		rt_dat['numSols_sharpSAT'][k_crashes] = {}
		rt_dat['numSols_approxMC'][k_crashes] = {}
		rt_dat['numSols_approxMC_mis'][k_crashes] = {}
		rt_dat['sharpSAT_time'][k_crashes] = {}
		rt_dat['approxMC_time'][k_crashes] = {}
		rt_dat['mis_time'][k_crashes] = {}
		rt_dat['approxMC_mis_time'][k_crashes] = {}
		rt_dat['z3 to cnf'][k_crashes] = {}
		rt_dat['cnf to dimacs'][k_crashes] = {}
		rt_dat['timing_time'] += time.time() - st_time

		start_time = time.time()

		if distinct_crashes:

			print 'Adding k_maxSimulationConstraints...',time.time()
			st_time=time.time()
			k_maxSimulationConstraints(stng,s, t, exact=True,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
			rt_dat['k_maxSimulationConstraints_BOOL'][k_crashes] = time.time() - st_time


			print 'Finding saboteurProbability...',time.time()
			st_time=time.time()
			p1 = saboteurProbability(stng,s,pr,M,t,l,optimize=optimize,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
			rt_dat['saboteurProbability'][k_crashes] = time.time() - st_time
			p2 = crashesProbability(stng,M,t,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

			if p1 =='Timeout':
				print_time('IterativeApproach Timeout...')
				print '###############################################'
				print '###############################################'
				print ''
				return ((lower_bound,upper_bound),'Timeout'),rt_dat

			# Update Bounds
			lower_bound += p2 - p1
			upper_bound -= p1

		else:
			# BIT-ADDED BASED SAT COUNTING
			# COMPUTES ONLY BOUNDS ON PRIORITY
			print 'Adding k_maxSimulationConstraints...',time.time()
			st_time=time.time()
			k_maxSimulationConstraints_BOOL(stng,s, t, exact=True,
				k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
			rt_dat['k_maxSimulationConstraints_BOOL'][k_crashes] = time.time() - st_time

			for fail_at in range(t):

				if time.time() - start_time > glbl_vars.timeout_limit:
					print_time('IterativeApproach Timeout...')
					print '###############################################'
					print '###############################################'
					print ''
					return ((lower_bound,upper_bound),'Timeout'),rt_dat

				print '\n----------k,fail_at = {},{}------------'.format(k_crashes,fail_at)

				s.push()

				#require that if an edge fails, it fails at time immediatefailure
				print 'Adding immediatefailureConstraints...',time.time()
				st_time=time.time()
				immediatefailureConstraints(stng, s, t, fail_at)
				rt_dat['immediatefailureConstraints'][k_crashes][fail_at] = time.time() - st_time

				# Process and save Formula to file
				glbl_vars.init()
				cnf_file = "umc_dimacs{}_{}_{}_{}_{}_{}_{}.txt".format(n,m,e,t,k_crashes,l,fail_at)
				sol_file = "umc_dimacs{}_{}_{}_{}_{}_{}_{}.txt.sol".format(n,m,e,t,k_crashes,l,fail_at)
				mis_cnf_file = cnf_file+'.ind'
				# tact = Tactic('tseitin-cnf')
				tact = With('tseitin-cnf',distributivity=False)
				st1=print_time("z3 to cnf...")
				cnf = tact(s.get_goal())[0]
				st2=print_time("cnf to dimacs...")
				dimacs = cnf_to_DIMACS(cnf)
				st3=print_time("saving dimacs to file...")
				save_DIMACS_to_file(dimacs,cnf_file)

				# Store Conversion Times
				rt_dat['z3 to cnf'][k_crashes][fail_at] = st2-st1
				rt_dat['cnf to dimacs'][k_crashes][fail_at] = st3-st2


				s.pop()

				# Run sharpSAT on file---------------------------
				print_time("\nrunning sharpSAT on file...")
				numSols_sharpSAT,sharpSAT_time = run_sharpSAT(cnf_file,sol_file,return_time=True)
				# -----------------------------------------------

				# Run MIS+approxMC on file-----------------------
				print_time("\nrunning mis on file...")
				mis_output,mis_time=run_mis(cnf_file,mis_cnf_file)
				if mis_time != 'timeout':
					assert mis_output=='success'
					print_time("running approxMC on file...")
					numSols_approxMC_mis,approxMC_mis_time=run_approxMC(mis_cnf_file)
				else:
					numSols_approxMC_mis=0
					approxMC_mis_time='timeout'
				# -----------------------------------------------

				# Run only ApproxMC on file---------------------------
				print_time("\nrunning approxMC on file...")
				numSols_approxMC,approxMC_time=run_approxMC(cnf_file)
				# -----------------------------------------------

				# Compare sharpSAT and approxMC results
				if isinstance(sharpSAT_time,float) and isinstance(approxMC_mis_time,float):
					diff=numSols_sharpSAT-numSols_approxMC_mis
					b1=(numSols_sharpSAT==0) and (numSols_approxMC==0)
					if not (b1 or ((float(diff)/(numSols_sharpSAT))**2 < 0.1)):
						sys.stderr.write('Comparison Errors between counting approaches! => '+
											'FILE: ' + cnf_file + ' counts=' +
											str((numSols_sharpSAT,numSols_approxMC_mis))+'\n\n')
						print('Comparison Errors between counting approaches! => '+
											'FILE: ' + cnf_file + ' counts=' +
											str((numSols_sharpSAT,numSols_approxMC_mis))+'\n\n')
				if isinstance(sharpSAT_time,float) and isinstance(approxMC_time,float):
					diff=numSols_sharpSAT-numSols_approxMC
					b1=(numSols_sharpSAT==0) and (numSols_approxMC==0)
					if not (b1 or ((float(diff)/(numSols_sharpSAT))**2 < 0.1)):
						sys.stderr.write('Comparison Errors between counting approaches! => '+
											'FILE: ' + cnf_file + ' counts=' +
											str((numSols_sharpSAT,numSols_approxMC))+'\n\n')
						print('Comparison Errors between counting approaches! => '+
											'FILE: ' + cnf_file + ' counts=' +
											str((numSols_sharpSAT,numSols_approxMC_mis))+'\n\n')

				# Print Different Results
				print ''
				print 'numSols_sharpSAT',numSols_sharpSAT
				print 'numSols_approxMC',numSols_approxMC
				print 'numSols_approxMC_mis',numSols_approxMC_mis
				print 'sharpSAT_time',sharpSAT_time
				print 'approxMC_time',approxMC_time
				print 'mis_time',mis_time
				print 'approxMC_mis_time',approxMC_mis_time
				print 'mis+approxMC time',mis_time+approxMC_mis_time
				print ''

				# Store Data into rt_dat
				st_time=time.time()
				rt_dat['numSols_sharpSAT'][k_crashes][fail_at] = numSols_sharpSAT
				rt_dat['numSols_approxMC'][k_crashes][fail_at] = numSols_approxMC
				rt_dat['numSols_approxMC_mis'][k_crashes][fail_at] = numSols_approxMC_mis
				rt_dat['sharpSAT_time'][k_crashes][fail_at] = sharpSAT_time
				rt_dat['approxMC_time'][k_crashes][fail_at] = approxMC_time
				rt_dat['mis_time'][k_crashes][fail_at] = mis_time
				rt_dat['approxMC_mis_time'][k_crashes][fail_at] = approxMC_mis_time
				rt_dat['timing_time'] += time.time() - st_time

				numSols = numSols_sharpSAT

				# Calculate Probabilities
				if isinstance(numSols,int) or isinstance(numSols,long):

					lb=numSols*((1-p_crashes)**(t*(len(stng.g.E)-k_crashes)+fail_at*k_crashes))*(p_crashes**k_crashes)
					ub=lb
					print "lb={}, ub={}".format(lb,ub)

					p2 = crashesProbability(stng,M,t,immediatefailure=fail_at,
						k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays,
						p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
					print "p2={}".format(p2)

					# Update Bounds
					lower_bound += p2 - ub
					upper_bound -= lb

					if lower_bound<0:
						lower_bound = 0

					print (lower_bound,upper_bound)

				elif numSols == 'timeout':
					print_time('IterativeApproach Timeout...')
					print '###############################################'
					print '###############################################'
					print ''
					return ((lower_bound,upper_bound),'Timeout'),rt_dat
				elif numSols == 'error':
					print_time('IterativeApproach error...')
					print '###############################################'
					print '###############################################'
					print ''
					return ((lower_bound,upper_bound),'error'),rt_dat
				else:
					print numSols,type(numSols)
					raise

				if k_crashes==0:
					break

		end_time = time.time()

		s.pop()

		k_omissions=0
		k_crashes=k_crashes+1
		k_delays=0

	print_time('RETURNING IterativeApproach...')
	print '###############################################'
	print '###############################################'
	print ''
	return (lower_bound,upper_bound),rt_dat

def literalWMC(stng, pr, M, t, l,precision=0,
	p_omissions=0,p_crashes=0,p_delays=0, RR='message'):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: (must be m) minimum number of messages that should arrive on time
	:param precision: fault probabilities are expressed using precision bits
	:param p_omissions: omission probability
	:param p_crashes: crash probability
	:param p_delays: (must be 0) delay probability
	:param RR: 'edge'/'message' specify the forwarding algorithm to be used

	:return: Score of priority scheme, calculated using literal WMC (and #SAT)
	'''
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING literalWMC...')
	print ''
	print 'precision={}\np_omissions={}\np_crashes={}\np_delays={}\nRR={}'.format(precision,p_omissions,p_crashes,p_delays,RR)
	print ''
	assert l==len(M)

	s = Goal()

	glbl_vars.init()
	st_time=time.time()
	rt_dat = {}
	rt_dat['timing_time'] = 0

	t1=print_time("Simulating network...")
	defineSimulationVariables(stng, M, t, basic_names=False)
	generalSimulationConstraints(stng,s, M, t, l, l_is_upperBound=False)
	specificSimulationConstraints(stng, s, pr, M, t, l, RR=RR)

	t2=print_time("setting weight vars...")
	weight_vars, normalization_factor = set_weight_vars(stng, s, M, t,precision=precision,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

	t3=print_time("converting to unweighted...")
	denom = wieghted_to_unweighted(stng,s,weight_vars,t,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)

	# print ''
	# print "denom = 2**{}".format(math.log(denom,2))
	# print "normalization_factor = {}".format(normalization_factor)
	# print ''

	# Process and save Formula to file
	glbl_vars.init()
	cnf_file = "umc_dimacs.txt"
	sol_file = "num_sols.txt"
	# tact = Tactic('tseitin-cnf')
	tact = With('tseitin-cnf',distributivity=False)
	t4=print_time("z3 to cnf...")
	cnf = tact(s)[0]
	t5=print_time("cnf to dimacs...")
	dimacs = cnf_to_DIMACS(cnf)
	t6=print_time("saving dimacs to file...")
	save_DIMACS_to_file(dimacs,cnf_file)

	# Run SharpSat on file
	t7=print_time("running SharpSat on file...")
	numSols,sharpSAT_time = run_sharpSAT(cnf_file,sol_file,return_time=True)
	if not (isinstance(numSols,int) or isinstance(numSols,long)):
		print "\n\n"
		print "numSols is not integral"
		print "Type =",type(numSols)
		print "sharpSAT_time = {}".format(sharpSAT_time)
		print "numSols = {}".format(numSols)
		print "\n"
		prob = numSols
	else:
		denom = Decimal(normalization_factor)*Decimal(denom)
		prob = Decimal(numSols)/denom
		prob = +prob
		print "\n\n"
		print "sharpSAT_time = {}".format(sharpSAT_time)
		print "numSols = {}".format(numSols)
		print "denom = {}".format(denom)
		print "prob = {}".format(prob)
		print "\n"

	print ''
	t8=print_time('RETURNING literalWMC...')

	st_time=time.time()
	rt_dat['generate program'] = t2-t1
	rt_dat['assign weights'] = t3-t2
	rt_dat['get umc'] = t4-t3
	rt_dat['z3 to cnf'] = t5-t4
	rt_dat['cnf to dimacs'] = t6-t5
	rt_dat['dimacs to file'] = t7-t6
	rt_dat['sharpsat'] = sharpSAT_time #t8-t7
	rt_dat['timing_time'] += time.time() - st_time

	print '###############################################'
	print '###############################################'
	print ''
	return prob, rt_dat

def monte_carlo_Score(stng, pr, M, t, l,
	p_omissions=0,p_crashes=0,p_delays=0,
	epsilon=0.2,confidence=0.8,RR='edge'):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: minimum number of messages that should arrive on time
	:param p_omissions: omission probability
	:param p_crashes: crash probability
	:param p_delays: (must be 0) delay probability
	:param epsilon: the maximum allowed error in the returned score
	:param confidence: the confidence with which the score is reported
	:param RR: 'edge'/'message' specify the forwarding algorithm to be used

	:return: Score of priority scheme, calculated using monte-carlo simulations
	'''
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING monte_carlo_Score...')
	print ''
	print 'epsilon={}\nconfidence={}\nRR={}'.format(epsilon,confidence,RR)
	print 'p_omissions={}\np_crashes={}\n'.format(p_omissions,p_crashes)
	print ''

	assert epsilon>0 and epsilon<1
	assert confidence>0 and confidence<1

	num_iterations = 1/(2*float(epsilon**2))*math.log(2/(1-float(confidence)))
	num_iterations = int(math.ceil(num_iterations))
	print 'num_iterations',num_iterations

	successful_iter = 0

	start_time = time.time()

	for i in range(num_iterations):
		if i%4096 == 0:
			print 'Progress:{:.2f}%'.format(i/float(num_iterations)*100)
		if time.time() - start_time > glbl_vars.timeout_limit:
			print_time('Timeout monte_carlo_Score...')
			print '###############################################'
			print '###############################################'
			print ''
			return (float(successful_iter)/float(i), 'Timeout at iter_count={}'.format(i))
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

	prob=float(successful_iter)/float(num_iterations)
	print ''
	print 'prob',prob
	print ''

	print_time('RETURNING monte_carlo_Score...')
	print '###############################################'
	print '###############################################'
	print ''

	return prob

def monte_carlo_Score_thread(stng, pr, M, t, l,
	p_omissions=0,p_crashes=0,p_delays=0,
	epsilon=0.2,confidence=0.8,RR='edge',
	num_threads = 4):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: minimum number of messages that should arrive on time
	:param p_omissions: omission probability
	:param p_crashes: crash probability
	:param p_delays: (must be 0) delay probability
	:param epsilon: the maximum allowed error in the returned score
	:param confidence: the confidence with which the score is reported
	:param RR: 'edge'/'message' specify the forwarding algorithm to be used
	:param num_threads: the number of concurrent threads to be spawned

	:return: Score of priority scheme, calculated using monte-carlo simulations
	'''
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING monte_carlo_Score_thread...')
	print ''
	print 'epsilon={}\nconfidence={}\nRR={}'.format(epsilon,confidence,RR)
	print 'p_omissions={}\np_crashes={}\n'.format(p_omissions,p_crashes)
	print ''

	assert epsilon>0 and epsilon<1
	assert confidence>0 and confidence<1

	num_iterations = 1/(2*float(epsilon)**2)*math.log(2/(1-float(confidence)))
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
		print 'Spawned Process',i

	print 'Waiting for processes to end...'
	for p in jobs:
		p.join()
	print 'All processes ended...'

	iter_count = 0
	for i in range(num_threads):
		successful_iter += return_dict[i][0]
		iter_count += return_dict[i][1]

	prob = float(successful_iter)/float(iter_count)
	print ''
	print 'prob',prob
	print ''

	# print 'return_dict',return_dict
	print_time('RETURNING monte_carlo_Score_thread...')
	print '###############################################'
	print '###############################################'
	print ''

	if iter_count != num_iterations:
		return (prob,'Timeout at iter_count={}'.format(iter_count))
	else:
		return prob

def rand_sim_EdgeRR_thread(output_dict,num_iter,id_thread, stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):
	'''
	:param output_dict: a dictionary to store results in
	:param num_iter: the number of iterations to be run
	:param id_thread: id of this thread
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: minimum number of messages that should arrive on time
	:param p_omissions: omission probability
	:param p_crashes: crash probability

	:return: Score of priority scheme, calculated using monte-carlo simulations

	This uses the Edge Round robin forwarding algorithm
	'''
	successful_iter = 0

	start_time = time.time()

	for i in range(num_iter):

		if i%4096 == 0:
			print 'Thread{} Progress:{:.2f}%'.format(id_thread,i/float(num_iter)*100)

		if time.time() - start_time > glbl_vars.timeout_limit:
			final_res = [successful_iter,i]
			output_dict[id_thread] = final_res
			return final_res
		res = rand_sim_EdgeRR(stng, pr, M, t, l,
					p_omissions=p_omissions,p_crashes=p_crashes)
		if res:
			successful_iter+=1
	final_res = [successful_iter,num_iter]
	output_dict[id_thread] = final_res
	return final_res

def rand_sim_MessageRR_thread(output_dict,num_iter,id_thread, stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):
	'''
	:param output_dict: a dictionary to store results in
	:param num_iter: the number of iterations to be run
	:param id_thread: id of this thread
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: minimum number of messages that should arrive on time
	:param p_omissions: omission probability
	:param p_crashes: crash probability

	:return: Score of priority scheme, calculated using monte-carlo simulations

	This uses the Message Round robin forwarding algorithm
	'''
	successful_iter = 0

	start_time = time.time()

	for i in range(num_iter):

		if i%4096 == 0:
			print 'Thread{} Progress:{:.2f}%'.format(id_thread,i/float(num_iter)*100)

		if time.time() - start_time > glbl_vars.timeout_limit:
			final_res = [successful_iter,i]
			output_dict[id_thread] = final_res
			return final_res
		res = rand_sim_MessageRR(stng, pr, M, t, l,
					p_omissions=p_omissions,p_crashes=p_crashes)
		if res:
			successful_iter+=1
	final_res = [successful_iter,num_iter]
	output_dict[id_thread] = final_res
	return final_res

def rand_sim_EdgeRR(stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param timeout: global timeout
	:param l: minimum number of messages that should arrive on time
	:param p_omissions: omission probability
	:param p_crashes: crash probability

	:return: weather a random simulation was successful or not

	This uses edge round robin forwarding algorithm
	'''
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
	for t in range(timeout):
		# Choose edges to crash
		for e in stng.g.E:
			sim_vars.crash[e] = sim_vars.crash[e] or get_prob_true(p_crashes)
			if sim_vars.crash[e]:
				T.append(e)

		# Move messages to new queue
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
	return (len(msg_arrived) >= l)

def rand_sim_MessageRR(stng, pr, M, timeout, l,
	p_omissions=0,p_crashes=0):
	'''
	:param stng: setting
	:param pr: priority scheme
	:param M: set of messages
	:param timeout: global timeout
	:param l: minimum number of messages that should arrive on time
	:param p_omissions: omission probability
	:param p_crashes: crash probability

	:return: weather a random simulation was successful or not

	This uses message round robin forwarding algorithm
	'''

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
	for t in range(timeout):
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

	return (len(msg_arrived) >= l)

def saboteurProbability(stng,s,pr,M,t,l,
	k_omissions=0,k_crashes=0,k_delays=0,
	p_omissions=0,p_crashes=0,p_delays=0,
	optimize=False):
	'''
	:param stng: setting
	:param s: solver
	:param pr: priority scheme
	:param M: set of messages
	:param t: global timeout
	:param l: minimum number of messages that should arrive on time
	:param k_crashes: exact number of edges that crash
	:param k_omissions: exact number of edges that omit
	:param k_delays: (must be 0) exact number of edges that delay
	:param p_omissions: omission probability
	:param p_crashes: crash probability
	:param p_delays: delay probability
	:param optimize: use doomed state optimizations

	:return: the joint probability of BAD outcomes, k crashes

	'''

	checkSupport(k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	count=0
	prob = 0
	start_time = time.time()
	while True:
		if time.time() - start_time > glbl_vars.timeout_limit:
		# if time.time() - start_time > glbl_vars.timeout_limit_small/len(stng.g.E):
			return 'Timeout'
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

	print "saboteurProbability Iteration Count = {}".format(count)
	return prob

def get_doomed_state(stng, crash_model, pr, M, t, l,
	k_omissions=0,k_crashes=0,k_delays=0):
	'''
	:param: parameters have usual meanings
	:returns: the smallest time t such that the configuration at t is doomed
	All crash sequences which follow crash_model till time t
	and have a total of k crashes will lead to a BAD outcome where
	number of messages delivered on time < l
	'''
	st0=time.time()
	sOpt = Solver()
	st = time.time()
	defineSimulationVariables(stng, M, t)
	generalSimulationConstraints(stng,sOpt, M, t, l,l_is_upperBound=False)
	specificSimulationConstraints(stng, sOpt, pr, M, t, l)
	k_maxSimulationConstraints(stng,sOpt, t, exact=True,
		k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)
	glbl_vars.doomed_state_rt['constraints'] += time.time() - st

	doomed = 0

	while True:
		st = time.time()
		temp_crash_model = getModel(sOpt)
		glbl_vars.doomed_state_rt['solving'] += time.time() - st
		if temp_crash_model is False:
			# There exists no crash sequence  in which at least l messages arrive
			# Hence, We have found a doomed state.
			break
		assert doomed<=t
		excludeCrashModel(stng,sOpt,crash_model,doomed,add_crashes=True,at_t_only=True,
			omissions=True,crashes=True,delays=True)
		st = time.time()
		glbl_vars.doomed_state_rt['excluding'] += time.time() - st
		doomed += 1

	glbl_vars.doomed_state_rt['total'] += time.time() - st0

	return doomed

def CEGAR(stng, M, t, l,
	k_omissions=0, k_crashes=0, k_delays=0,
	optimize=False, showProgress=False, countFaults=False,
	probabalistic=False,load_priority=False,save_priority=False):
	'''
	:param countFaults: a count of BAD outcomed crash sequences is returned
	:param probabalistic: the score of a priority scheme is returned
	:param load_priority: a previously saved priority scheme is loaded
	:param save_priority: the priority scheme generated is saved
	:return: Depends on the arguments
	'''
	#redundant: j = 1
	#redundant: counter=1
	print ''
	print '###############################################'
	print '###############################################'
	print_time('RUNNING CEGAR...')
	print ''

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

		p_omissions=0.01
		p_crashes=0.01
		p_delays=0
		precision=10

		epsilon=0.01
		confidence=0.99

		p_omissions=reduce_precision(p_omissions,precision)
		p_crashes=reduce_precision(p_crashes,precision)
		p_delays=reduce_precision(p_delays,precision)

		print_time("\nCalculating Probabilities now...")
		start_time = time.time()

		glbl_vars.init_doomed_rt()
		timings = {}
		prob = {}
		rt_dat = {}
		rt_dat['timing_time'] = 0

		# Here, Select the tools you wish to calulate probability with
		run = {}
		run['SAT_count']=True
		run['incremental k, z3-based naive counting']=False
		run['incremental k, z3-based naive counting, optimized']=False
		run['incremental k, bit-adder with weightMC']=False
		# Have enough Data
		run['WMC MessageRR']=False
		run['MonteCarlo MessageRR']=False
		run['MonteCarlo MessageRR threads']=False
		# Hardly Used
		run['incremental k, simultaneous crashes, bit-adder']=False
		run['WMC EdgeRR']=False
		run['MonteCarlo EdgeRR']=False
		run['MonteCarlo EdgeRR threads']=False

		if run['SAT_count']:
			t1=time.time()
			SAT_count(stng, pr, M, t, l, RR='message',
				exact=True, approximate=True, immediate_failure=False, build_MIS='both')
			rt_dat['SAT_count']=time.time()-t1

		if run['incremental k, simultaneous crashes, bit-adder']:
			t1=time.time()
			prob['0b'],rt_dat['0b_inner']=IterativeApproach(stng, pr, M, t, l,optimize=optimize,naive=False,
				p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
			rt_dat['0b']=time.time()-t1

		if run['incremental k, z3-based naive counting']:
			t1=time.time()
			prob['0a'],rt_dat['0a_inner']=IterativeApproach(stng, pr, M, t, l,optimize=False,naive=True,
					p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
			rt_dat['0a']=time.time()-t1

		if run['incremental k, z3-based naive counting, optimized']:
			t1=time.time()
			prob['0o'],rt_dat['0o_inner']=IterativeApproach(stng, pr, M, t, l,optimize=True,naive=True,
					p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays)
			rt_dat['0o']=time.time()-t1
			rt_dat['doomed_state_timing'] = glbl_vars.doomed_state_rt

		if run['incremental k, bit-adder with weightMC']:
			t1=time.time()
			prob['3m'],rt_dat['3m_inner'] = weightMC(stng, pr, M, t, l,
				p_omissions=0,p_crashes=p_crashes)
			rt_dat['3m']=time.time()-t1

		if run['WMC EdgeRR']:
			t1=time.time()
			prob['1e'],rt_dat['1e_inner']=literalWMC(stng, pr, M, t, l,precision=precision,
					p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays,
					RR='edge')
			rt_dat['1e']=time.time()-t1

		if run['WMC MessageRR']:
			t1=time.time()
			prob['1m'],rt_dat['1m_inner']=literalWMC(stng, pr, M, t, l,precision=precision,
					p_omissions=p_omissions,p_crashes=p_crashes,p_delays=p_delays,
					RR='message')
			rt_dat['1m']=time.time()-t1

		if run['MonteCarlo EdgeRR']:
			t1=time.time()
			prob['2e']=monte_carlo_Score(stng, pr, M, t, l,RR='edge',
					p_omissions=p_omissions,p_crashes=p_crashes,
					epsilon=epsilon,confidence=confidence)
			rt_dat['2e']=time.time()-t1

		if run['MonteCarlo EdgeRR threads']:
			t1=time.time()
			prob['2et']=monte_carlo_Score_thread(stng, pr, M, t, l,RR='edge',
					p_omissions=p_omissions,p_crashes=p_crashes,
					epsilon=epsilon,confidence=confidence)
			rt_dat['2et']=time.time()-t1

		if run['MonteCarlo MessageRR']:
			t1=time.time()
			prob['2m']=monte_carlo_Score(stng, pr, M, t, l,RR='message',
					p_omissions=p_omissions,p_crashes=p_crashes,
					epsilon=epsilon,confidence=confidence)
			rt_dat['2m']=time.time()-t1

		if run['MonteCarlo MessageRR threads']:
			t1=time.time()
			prob['2mt']=monte_carlo_Score_thread(stng, pr, M, t, l,RR='message',
					p_omissions=p_omissions,p_crashes=p_crashes,
					epsilon=epsilon,confidence=confidence)
			rt_dat['2mt']=time.time()-t1


		print ''
		print ''
		print '#Final Probabilities:'
		print ''
		try: print 'IterativeApproach bit-adder  \t',prob['0b'],rt_dat['0b']
		except: print ''
		try: print 'IterativeApproach NO OPT     \t',prob['0a'],rt_dat['0a']
		except: print ''
		try: print 'IterativeApproach OPT        \t',prob['0o'],rt_dat['0o']
		except: print ''
		try: print 'IterativeApproach weightMC   \t',prob['3m'],rt_dat['3m']
		except: print ''
		try: print 'literalWMC edgeRR            \t',prob['1e'],rt_dat['1e']
		except: print ''
		try: print 'literalWMC messageRR         \t',prob['1m'],rt_dat['1m']
		except: print ''
		try: print 'monte_carlo edgeRR           \t',prob['2e'],rt_dat['2e']
		except: print ''
		try: print 'monte_carlo thread edgeRR    \t',prob['2et'],rt_dat['2et']
		except: print ''
		try: print 'monte_carlo messageRR        \t',prob['2m'],rt_dat['2m']
		except: print ''
		try: print 'monte_carlo thread messageRR \t',prob['2mt'],rt_dat['2mt']
		except: print ''
		print ''
		print ''

		# Add parameters to object for saving
		n=len(stng.g.V)
		e=len(stng.g.E)
		m=len(M)
		t=t
		l=l
		k_omissions=k_omissions
		k_crashes=k_crashes
		k_delays=k_delays
		optimize=optimize
		showProgress=showProgress
		countFaults=countFaults
		probabalistic=probabalistic
		load_priority=load_priority
		save_priority=save_priority
		p_omissions=p_omissions
		p_crashes=p_crashes
		p_delays=p_delays
		precision=precision

		params = {}
		params['n'] = n
		params['e'] = e
		params['m'] = m
		params['t'] = t
		params['l'] = l
		params['optimize'] = optimize
		params['showProgress'] = showProgress
		params['countFaults'] = countFaults
		params['probabalistic'] = probabalistic
		params['load_priority'] = load_priority
		params['save_priority'] = save_priority
		params['k_omissions'] = k_omissions
		params['k_crashes'] = k_crashes
		params['k_delays'] = k_delays
		params['p_omissions'] = p_omissions
		params['p_crashes'] = p_crashes
		params['p_delays'] = p_delays
		params['precision'] = precision
		params['confidence'] = confidence
		params['epsilon'] = epsilon
		# params['M'] = [(msg.s.name, msg.t.name, msg.id) for msg in M]
		# params['edges'] = [(edge.s,edge.t) for edge in stng.g.E]

		# Return from CEGAR
		prob = 0

		# Store Parameters,Probabilities and run-time data to file
		save_scaling_data_to_file(run,params,rt_dat,0)

		end_time = time.time()
		count_time = end_time-start_time
		print "Total Time taken = {}\n\n".format(str(count_time))
		print "End Time", time.time()
		print '###############################################'
		print '###############################################'
		print ''
		return (prob,count_time)

	else:
		raise ValueError("Only implemented counting of faults and probablistic setting")
		return Adverserial(stng, pr, M, t, l,
					k_omissions=k_omissions, k_crashes=k_crashes, k_delays=k_delays,
					optimize=optimize, showProgress=showProgress)

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

	print ''
	print ''
	print ''
	print 'PARAMETERS:'
	print ''
	print 'custom\t',custom
	print 'load\t',load
	print 'save\t',save
	print 'optimize\t',optimize
	print 'showProgress\t',showProgress
	print 'weight\t',weight
	print 'diff\t',diff
	print 'countFaults\t',countFaults
	print 'probabalistic\t',probabalistic
	print 'n\t',n
	print 'm\t',m
	print 'e\t',e
	print 't\t',t
	print 'l\t',l
	print 'k\t',k
	print ''
	print ''
	print ''

	# filename='{}-{}-{}-{}-{}-{}.setting'.format(n,m,e,t,k,l)
	filename="settings.curr"

	exit_status = main(n,m,e,t,l,
		k_crashes=k,filename=filename, save=save, load=load, optimize=optimize,
		showProgress=showProgress, weight=weight, countFaults=countFaults,
		probabalistic=probabalistic, custom=custom)
