import math
from scipy.special import comb
from decimal import *

import time
import pickle
import itertools
import subprocess
from optparse import OptionParser

from z3 import *

from Objects import *
from Graph import GenerateSetting
from Constraints import *

#############
# PROBABILITY
#############

def prob_crash_parameters(e,t,p_crashes=0,k_crashes=0,precision=None):
	if precision is not None:
		a1=Decimal(comb(e,k_crashes,exact=True))

		with localcontext() as ctx:
			ctx.prec = precision   # Perform a high precision calculation

			one = Decimal(1)
			e=Decimal(e)
			t=Decimal(t)
			p_crashes=Decimal(p_crashes)
			k_crashes=Decimal(k_crashes)

			a = a1*((one-p_crashes)**((e-k_crashes)*t))
			b=one-((one-p_crashes)**(t))
			res = a*(b**k_crashes)
		res = +res
		return res
	else:
		a=comb(e,k_crashes,exact=True)*pow(1-p_crashes,(e-k_crashes)*t)
		b=1-pow(1-p_crashes,t)
		return a*pow(b,k_crashes)

def prob_not_AMA(e,t,p_crashes=0,k_crashes=0,k_crashes_sum=None,precision=None):
	if precision is not None:
		with localcontext() as ctx:
			ctx.prec = precision   # Perform a high precision calculation

			one = Decimal(1)
			e=Decimal(e)
			t=Decimal(t)
			p_crashes=Decimal(p_crashes)
			k_crashes=Decimal(k_crashes)
			a=(one-p_crashes)**((e-k_crashes)*t)*(p_crashes**k_crashes)
			b=(one-p_crashes)**(Decimal(k_crashes_sum))
			res = a*b
		res = +res
		return res
	else:
		a=pow(1-p_crashes,(e-k_crashes)*t)*pow(p_crashes,k_crashes)
		b=pow(1-p_crashes,k_crashes_sum)
		return a*b

def get_crash_data(stng, mdl, t, M):
	res = []
	for e in stng.g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.crash(e,i)]):
				# print 'edge: %s crashed at time %d'%(str(e), i)
				res.append((e,i))
				break
	return res

def get_model_prob(stng,crash_model,t,M,p_crashes=0,k_crashes=0):
	dat = get_crash_data(stng,crash_model,t,M)
	sum_i = math.fsum([x[1] for x in dat])

	return prob_not_AMA(len(stng.g.E),t,
			p_crashes=p_crashes,k_crashes=k_crashes,k_crashes_sum=sum_i)

def crashesProbability(stng,M,t,crashed=0,
	k_omissions=0,k_crashes=0,k_delays=0,
	p_omissions=0,p_crashes=0,p_delays=0):
	'''
	Returns the probability that exactly k crashes/delays/omissions occur
	'''
	checkSupport(k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	num_edges = len(stng.g.E)-crashed
	return prob_crash_parameters(num_edges,t,
			p_crashes=p_crashes,k_crashes=k_crashes)

######
# MISC
######

def AskContinue(lb,ub,k):
	print "Probability lies in ({},{})".format(lb,ub)
	print "Uncertainity = {}".format(ub-lb)
	ques="Do you want to continue with k={}".format(k)
	return query_yes_no(ques,default="yes")

# Ref : http://code.activestate.com/recipes/577058/
def query_yes_no(question, default="yes"):
	"""Ask a yes/no question via input() and return their answer.

	"question" is a string that is presented to the user.
	"default" is the presumed answer if the user just hits <Enter>.
		It must be "yes" (the default), "no" or None (meaning
		an answer is required of the user).

	The "answer" return value is True for "yes" or False for "no".
	"""
	valid = {"yes": True, "y": True, "ye": True,
			 "no": False, "n": False}
	if default is None:
		prompt = " [y/n] "
	elif default == "yes":
		prompt = " [Y/n] "
	elif default == "no":
		prompt = " [y/N] "
	else:
		raise ValueError("invalid default answer: '%s'" % default)

	while True:
		# sys.stdout.write(question + prompt)
		choice = raw_input(question + prompt).lower()
		# print(choice)
		if default is not None and choice == '':
			return valid[default]
		elif choice in valid:
			return valid[choice]
		else:
			sys.stdout.write("Please respond with 'yes' or 'no' "
							 "(or 'y' or 'n').\n")

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

def save_to_file(S,filename):
	file = open(filename, 'w')
	pickle.dump(S, file)
	file.close()

def load_from_file(filename):
	file = open(filename, 'r')
	return  pickle.load(file)

def getModel(s):
	if s.check() == sat:
		return s.model()
	else:
		return False

def checkSupport(k_omissions=0, k_crashes=0, k_delays=0):
	if k_delays > 0:
		raise
	if k_omissions > 0:
		raise

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

##########
# PRINTING
##########

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

def printConfiguration(stng, crash_model, t, M, i):
	for m in M:
		for v in stng.UFSv[m]:
			if is_true(crash_model[stng.vars.config(m,v,i)]):
				print "{} at vertex {} at time {}".format(m,v,i)

def printConfigurations(stng, crash_model, t, M):
	for i in range(t):
		print "TIME {}".format(i)
		printConfiguration(stng, crash_model, t, M, i)

def printCounterexample(stng, mdl, t, M,count=False):
	k_crashes=0
	k_omissions=0
	k_delays=0

	for e in stng.g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.omit(e,i)]):
				if count is False:
					print 'edge: %s omitted at time %d'%(str(e), i)
				else:
					k_omissions += 1
	for e in stng.g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.crash(e,i)]):
				if count is False:
					print 'edge: %s crashed at time %d'%(str(e), i)
				else:
					k_crashes += 1
				break
	for e in stng.g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.delay(e,i)]):
				if count is False:
					print 'edge: %s delayed at time %d'%(str(e), i)
				else:
					k_delays += 1

	if count is True:
		return (k_crashes,k_omissions,k_delays)

#############
# DEFINE VARS
#############

def definePriorityVariables(stng, M, heuristic=None):
	'''
	Initaializes/defines message priority variables
	'''
	for m in M:
		for v in stng.UFSv[m]:
			# message m has priority j at vertex v
			for j in range(len(M)):
				stng.vars.def_priority(m,v,j)

	if heuristic is not None:
		pr = {}
		for m in M:
			pr[m] = {}
			for v in stng.UFSv[m]:
				pr[m][v] = Int('priority of {} at vertex {}'.format(str(m),str(v)))
		return pr

def defineSimulationVariables(stng, M, t):
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
			stng.vars.def_omit(e,i)

			# Is there a crash fault at e at time i
			stng.vars.def_crash(e,i)

			# Is there a delay fault at e at time i
			stng.vars.def_delay(e,i)
