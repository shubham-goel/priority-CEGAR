import sys

sys.path.append("bin")

import time
import itertools

from z3 import *

import global_vars as glbl_vars
from Objects import *
from Graph import GenerateSetting
from Utilities import *
from Constraints import *

def saboteurStrategy(stng, S, M, t, l,
	k_omissions=0, k_crashes=0, k_delays=0):
	'''
	NOT USED
	Used with ADVERSERIAL Setting
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
	NOT USED
	Used with ADVERSERIAL Setting
	Learn constraints from crash_mdl,
	Add them to solver s

	Return False if no such constraints exist,
	Then no (k-l) resistant schedules exist
	'''
	return False

def Adverserial(stng, pr, M, t, l,
	k_omissions=0, k_crashes=0, k_delays=0,
	optimize=False, showProgress=False):
	'''
	NOT USED
	Adverserial setting.
	'''
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
