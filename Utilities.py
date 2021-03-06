import math
from scipy.special import comb
from decimal import *

import time
import pickle
import itertools
import subprocess
import numpy as np
from optparse import OptionParser

from z3 import *

import global_vars as glbl_vars
from Objects import *
from Graph import GenerateSetting

#############
# PROBABILITY
#############

def get_prob_true(p):
	r = np.random.choice(2,1,p=[1-p, p])
	return r[0]==1

def prob_crash_parameters(e,t,p_crashes=0,k_crashes=0,precision=None,immediatefailure=None):
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
			if immediatefailure is None:
				b=one-((one-p_crashes)**(t))
			else:
				b=((one-p_crashes)**(immediatefailure))*p_crashes
			res = a*(b**k_crashes)
		res = +res
		return res
	else:
		a=comb(e,k_crashes,exact=True)*pow(1-p_crashes,(e-k_crashes)*t)
		if immediatefailure is None:
			b=1-pow(1-p_crashes,t)
		else:
			b=pow(1-p_crashes,immediatefailure)*p_crashes
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
	p_omissions=0,p_crashes=0,p_delays=0,
	immediatefailure=None):
	'''
	Returns the probability that exactly k crashes/delays/omissions occur
	'''
	checkSupport(k_omissions=k_omissions,k_crashes=k_crashes,k_delays=k_delays)

	num_edges = len(stng.g.E)-crashed
	return prob_crash_parameters(num_edges,t,immediatefailure=immediatefailure,
			p_crashes=p_crashes,k_crashes=k_crashes)

######
# MISC
######

def save_scaling_data_to_file(run,params,rt_dat,prob,filename=None):

	n=params['n']
	m=params['m']
	e=params['e']
	t=params['t']
	l=params['l']

	if filename is None:
		filename = 'results/n{}-m{}-e{}-t{}-l{}.dat'.format(n,m,e,t,l)

	save_to_file((run,params,rt_dat,prob),filename)

def save_counting_parameters(n,m,e,t,k,l,result):
	parameter_file = "timings_counting_bitadder.txt"
	line = "{}\t{}\t{}\t{}\t{}\t{}\t{}\n".format(n,m,e,t,k,l,result)
	with open(parameter_file, "a") as myfile:
		myfile.write(line)

def AskContinue(lb,ub,k):
	print "Probability lies in ({},{})".format(lb,ub)
	print "Uncertainity = {}".format(ub-lb)
	ques="Do you want to continue with k={}".format(k)
	print ques
	return (ub-lb)>=0.01
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
	usage = "usage: %prog [options] nodes messages edges timeout l k"
	parser = OptionParser(usage=usage)
	# parser.add_option('-t','--timeout', dest="t",
	# 			  help="The timeout, should be an integer")
	# parser.add_option("-l", dest="l",
	# 			  help="The guarantee on the number of messages that should arrive.")
	# parser.add_option("-k", dest="k",
	# 			  help="#edges that are allowed to crash.")
	# parser.add_option("-n", dest="n",
	# 			  help="#vertices in the network.")
	# parser.add_option("-m", dest="m",
	# 			  help="#messages in the network.")
	# parser.add_option("-e", dest="e",
	# 			  help="#edges in the network.")

	parser.add_option("-l","--load",
				  action="store_true", dest="load", default=False,
				  help="Load setting from pickle-dumped file 'settings.curr'")
	parser.add_option("-m","--manual","--custom",
				  action="store_true", dest="custom", default=False,
				  help="Load setting from custom file 'custom.settings'")
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
				  help="Count the numer of BAD outcomed fault sequences with at most k crashes")
	parser.add_option("-p","--prob",
				  action="store_true", dest="probabalistic", default=False,
				  help="Score the forwarding scheme that is generated for the setting")
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

def save_priority_to_file(stng, pr, filename):
	pr_dict = {}
	for v in stng.g.V:
		pr_dict[str(v)] = []
		for m in pr[v]:
			pr_dict[str(v)].append(str(m))

	print pr_dict
	save_to_file(pr_dict, filename)

def load_priority_from_file(stng, M, filename):
	pr_dict = load_from_file(filename)
	pr = {}
	for v in stng.g.V:
		pr[v] = []
		for m_name in pr_dict[str(v)]:
			pr[v].append(M[int(m_name)])
	return pr

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

# Ref : https://rosettacode.org/wiki/Decimal_floating_point_number_to_binary#Python
def float_dec2bin(d, max_len = 25):
	d = float(d)
	assert d>0 and d<1
	if d in glbl_vars.float_dec2bin_dict.keys():
		return glbl_vars.float_dec2bin_dict[d]
	hx = float(d).hex()
	p = hx.index('p')
	bn = ''.join(glbl_vars.hex2bin.get(char, char) for char in hx[2:p])
	bin_string = bn.strip('0')

	exp = int(hx[p+2:])
	assert exp>=len(bin_string.split('.')[0])
	prefix = ''.join(['0' for i in range(exp-len(bin_string.split('.')[0]))])
	bin_string = prefix + bin_string.split('.')[0] + bin_string.split('.')[1]

	if len(bin_string) > max_len:
		bin_string = bin_string[:max_len].rstrip('0')
	exp = len(bin_string)

	glbl_vars.float_dec2bin_dict[d] = (bin_string,exp)
	return bin_string,exp

def reduce_precision(p,precision):
	if p==0:
		return 0
	elif p==1:
		return 1
	bin_str,expo= float_dec2bin(p,max_len=precision)
	number = 0
	power = 1
	for i in range(expo):
		power /= 2.0
		if bin_str[i] == '1':
			number += power
	return number

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

def help():
	print '''
	USAGE:
	$ python ScheduleTwoPathCEGAR.py n m e t l k [options]

		n    Number of Nodes
		m    Number of Messages
		e    Number of Edges
		t    Global timeout
		l    The minimum number of messages that should reach on time
		k    The number of edge crashes (Not relevent for scoring forwarding schemes with option --prob)

	OPTIONS:
		--prob   -p  Score the forwarding scheme that is generated for the setting
		--count  -c  Count the numer of BAD outcomed fault sequences with at most k crashes
		--load   -l  Load setting from pickle-dumped file 'settings.curr'
		--manual -m  Load setting from custom text file 'custom.setting'. Explained in detail later
		--custom     The same as --manual
	'''

##########
# PRINTING
##########

def print_dict(d,prefix=''):
	try:
		for key in d.keys():
			print prefix+str(key),'=> ('
			print_dict(d[key],prefix=prefix+'\t')
			print prefix+')'
	except AttributeError:
		try:
			for i,val in enumerate(d):
				print prefix+str(i),'=> ('
				print_dict(val,prefix=prefix+'\t')
				print prefix+')'
		except TypeError:
			print prefix+str(d)

def print_edges(stng):
	print ''
	print ''
	for i in range(len(stng.g.E)):
		print 'edge',i, str(stng.g.E[i])
	print ''
	print ''

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
					break
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
		return (k_omissions,k_crashes,k_delays)

def print_time(msg,update=True):
	new_time = time.time()
	if update:
		print msg,new_time,new_time-glbl_vars.last_time
		glbl_vars.last_time = new_time
	else:
		print msg,new_time
	return new_time

#############
# DEFINE VARS
#############

def definePriorityVariables(stng, M, heuristic=None, basic_names=False):
	'''
	Initaializes/defines message priority variables
	'''
	for m in M:
		for v in stng.UFSv[m]:
			# message m has priority j at vertex v
			for j in range(len(M)):
				stng.vars.def_priority(m,v,j,basic_names=basic_names)

	if heuristic is not None:
		pr = {}
		for m in M:
			pr[m] = {}
			for v in stng.UFSv[m]:
				pr[m][v] = Int('priority of {} at vertex {}'.format(str(m),str(v)))
		return pr

def defineSimulationVariables(stng, M, t, basic_names=False):
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
				stng.vars.def_config(m,v,i,basic_names=basic_names)

			for e in stng.edge_priority[m][v]:
				for i in range(t):
					# is message m using e at i
					stng.vars.def_used(m,e,i,basic_names=basic_names)

		# has message arrived destination
		stng.vars.def_msgArrive(m)

	for e in stng.g.E:
		for i in range(t):

			# Is there an omission fault at e at time i
			stng.vars.def_omit(e,i,basic_names=basic_names)

			# Is there a crash fault at e at time i
			stng.vars.def_crash(e,i,basic_names=basic_names)

			# Is there a delay fault at e at time i
			stng.vars.def_delay(e,i,basic_names=basic_names)

#########
# BOOLEAN
#########

def new_chain_formula(bit_str):
	ptr = len(bit_str)-1
	if ptr < 0:
		raise
	chain_form = new_unused_variable()
	ptr -= 1
	while ptr>=0:
		if bit_str[ptr] == '1':
			chain_form = Or(chain_form,new_unused_variable())
		elif bit_str[ptr] == '0':
			chain_form = And(chain_form,new_unused_variable())
		else:
			raise
		ptr -= 1
	return chain_form

def new_unused_variable():
	var = Bool('new_var'+str(glbl_vars.variable_number))
	glbl_vars.variable_number += 1
	return var

########
# DIMACS
########

def cnf_to_DIMACS(cnf,record_wv_mapping=False):
	'''
	Convert cnf formulaoutputted bu z3 into DIMACS Format
	'''
	glbl_vars.init()
	dimacs = [clause_to_DMACS(clause,record_wv_mapping=record_wv_mapping) for clause in cnf]

	return dimacs

def clause_to_DMACS(clause,record_wv_mapping=False):
	clause = str(clause)

	if clause[:3] == "Or(":
		clause = clause[3:-1]

	dmacs_clause = [literal_to_number(literal,record_wv_mapping=record_wv_mapping) for literal in clause.split(",")]

	return dmacs_clause

def literal_to_number(literal,record_wv_mapping=False):
	literal=literal.strip(" \t\n")
	neg = False
	if len(literal) > 5 and literal[:4]=="Not(":
		literal = literal[4:-1]
		neg = True
	literal=literal.strip(" \t\n")
	lit_num = None

	try:
		lit_num = glbl_vars.variable_name_to_number[literal]
	except KeyError:
		lit_num = glbl_vars.variable_number
		glbl_vars.variable_number += 1
		glbl_vars.variable_name_to_number[literal] = lit_num
		if record_wv_mapping:
			if literal[:3] == "WV_":
				assert not (literal[3:] in glbl_vars.weight_vars_to_number.keys())
				glbl_vars.weight_vars_to_number[literal[3:]] = lit_num
				# print 'Set WV -> '+literal[3:]

	if neg:
		return (-1*lit_num)
	else:
		return (lit_num)

def save_DIMACS_to_file(dimacs, filename, weight_vars=None, magnification=1):
	num_vars = glbl_vars.variable_number-1
	num_clauses = len(dimacs)
	with open(filename, "w") as f:
		header = "p cnf {} {}\n".format(num_vars,num_clauses)
		f.write(header)
		f.write(''.join([format_DIMACS_clause(clause) for clause in dimacs]))
		if weight_vars:
			weight_vars_data = []
			lit_weights_written = []
			for wv in weight_vars:
				try:
					lit_num = glbl_vars.weight_vars_to_number[wv.name]
					# if wv.weight == 0:
					# 	weight_vars_data.append('{} 0\n'.format(-1*lit_num))
					# else:
					weight_vars_data.append('w {} {}\n'.format(lit_num,wv.weight))
					# if wv.weight == 1:
					# 	weight_vars_data.append('{} 0\n'.format(lit_num))
					# else:
					weight_vars_data.append('w {} {}\n'.format(-1*lit_num,magnification-wv.weight))
					lit_weights_written.append(lit_num)
				except:
					raise
			for lit_num in [item for item in range(1,num_vars+1) if item not in lit_weights_written]:
					weight_vars_data.append('w {} {}\n'.format(lit_num,1))
					weight_vars_data.append('w -{} {}\n'.format(lit_num,1))
			f.write(''.join(weight_vars_data))
	print ''
	print "num_vars =",num_vars
	print "num_clauses =",num_clauses
	print ''

def format_DIMACS_clause(clause):
	formatted = ' '.join([str(lit) for lit in clause])+ " 0\n"
	return formatted

########
# WMC
########

def process_approxMC_output(sol_file):
	numSols = None
	with open(sol_file, "r") as f:
		status = 0
		for line in f:
			if line=="The input formula is unsatisfiable.\n":
				numSols=0
				break
			elif line[:24]=="Number of solutions is: ":
				print line[24:-1]
				expr = line[24:-1].split('x')
				num1 = int(expr[0])
				num2 = int(expr[1].split('^')[0])
				num3 = int(expr[1].split('^')[1])
				numSols = num1*(num2**num3)

		if numSols is None:
			sys.stderr.write('\n\n'+f.read()+'\n\n')
			return 'error'

	return numSols

def process_sharpSat_output(sol_file,return_time=False):
	numSols = None
	time_taken=None
	with open(sol_file, "r") as f:
		status = 0
		for line in f:
			if status == 0:
				if line=="# solutions \n":
					status += 1
			elif status == 1:
				numSols = int(line)
				status += 1
			elif status == 2:
				assert line=="# END\n"
				status += 1
			elif status == 3:
				assert line =="\n"
				status+=1
			elif status == 4:
				assert line[:6]=="time: "
				time_taken=float(line[6:-2])
				status+=1
			else:
				break
		assert (status==5)
		assert numSols is not None
		assert time_taken is not None

	if return_time:
		return numSols,time_taken
	else:
		return numSols

def process_weightMC_output(sol_file):
	numSols = None
	with open(sol_file, "r") as f:
		for line in f:
			if line=="The input formula is unsatisfiable.\n":
				numSols=0
				break
			elif line[:34]=='Approximate weighted model count: ':
				print line[34:-1]
				expr = line[34:-1].split('x')
				num1 = float(expr[0])
				num2 = float(expr[1].split('^')[0])
				num3 = float(expr[1].split('^')[1])
				numSols = num1*(num2**num3)

		if numSols is None:
			sys.stderr.write('\n\n'+f.read()+'\n\n')
			return 'error'

	return numSols

def set_weight_vars(stng, s, M, t,precision=0,
	p_omissions=0,p_crashes=0,p_delays=0,magnification=1,output_range = None):
	normalization_factor = 1
	weight_vars = []
	p_omissions1 = reduce_precision(p_omissions,precision)
	p_omissions2 = reduce_precision(1/(2-p_omissions),precision)
	p_crashes1 = reduce_precision(p_crashes,precision)
	p_crashes2 = reduce_precision(1/(2-p_crashes),precision)

	if output_range is not None:
		original_norm = 1
		mag_count = 0
		if p_omissions>0:
			original_norm *= ((1-p_omissions1)*p_omissions2)**(len(stng.g.E)*t)
			mag_count += len(stng.g.E)*t
		if p_crashes>0:
			original_norm *= ((1-p_crashes1)*p_crashes2)**(len(stng.g.E)*(t-1))
			mag_count += len(stng.g.E)*(t-1)
		magnification = (output_range*original_norm)**(-1.0/mag_count)
		print output_range, original_norm, mag_count, magnification

	p_omissions1 = p_omissions1*magnification
	p_omissions2 = p_omissions2*magnification
	p_crashes1 = p_crashes1*magnification
	p_crashes2 = p_crashes2*magnification

	for e in stng.g.E:
		for i in range(t):

			if p_omissions>0:
				# Omission weight variables
				ors= []
				for m in M:
					ors.append(stng.vars.used_ex(m,e,i))
				used = Or(ors)

				omit1 = weight_var(glbl_vars.variable_number,p=p_omissions1)
				glbl_vars.variable_number+=1
				omit2 = weight_var(glbl_vars.variable_number,p=p_omissions2)
				glbl_vars.variable_number+=1

				weight_vars.append(omit1)
				weight_vars.append(omit2)

				s.add(And(used,stng.vars.omit(e,i)) == omit1.var)
				s.add(And(Not(used),Not(stng.vars.omit(e,i))) == omit2.var)

				normalization_factor *= (magnification-p_omissions1)*p_omissions2

			if p_crashes>0:
				# Crash Weight Variables
				if i==0:
					crash1 = weight_var(glbl_vars.variable_number,p=p_crashes1)
					glbl_vars.variable_number+=1

					weight_vars.append(crash1)
					s.add(crash1.var == stng.vars.crash(e,i))
				else:
					crash1 = weight_var(glbl_vars.variable_number,p=p_crashes1)
					glbl_vars.variable_number+=1
					crash2 = weight_var(glbl_vars.variable_number,p=p_crashes2)
					glbl_vars.variable_number+=1

					weight_vars.append(crash1)
					weight_vars.append(crash2)

					s.add(crash1.var == And(stng.vars.crash(e,i),Not(stng.vars.crash(e,i-1))))
					s.add(crash2.var == And(stng.vars.crash(e,i),(stng.vars.crash(e,i-1))))

					normalization_factor *= (magnification-p_crashes1)*p_crashes2

	if output_range is not None:
		return weight_vars,normalization_factor,magnification
	else:
		return weight_vars,normalization_factor

def wieghted_to_unweighted(stng,s,weight_vars,t,
	p_omissions=0,p_crashes=0,p_delays=0):
	assert p_delays == 0
	denom = 1

	if p_omissions<=0:
		for e in stng.g.E:
			s.add(Not(Or([stng.vars.omit(e,i) for i in range(t)])))

	if p_crashes<=0:
		for e in stng.g.E:
			s.add(Not(Or([stng.vars.crash(e,i) for i in range(t)])))

	if p_delays<=0:
		for e in stng.g.E:
			s.add(Not(Or([stng.vars.delay(e,i) for i in range(t)])))

	for wv in weight_vars:
		(bits,expo) = float_dec2bin(wv.weight)
		cf = new_chain_formula(bits)
		s.add(wv.var == cf)
		denom *= 2**expo

	return denom

def vaildate_exit_code(exit_code):
	acceptable=[0,10,20]
	if exit_code in acceptable:
		return True
	else:
		return False

def run_bash(cmd,timeout=None):
	print('cmd >>>',cmd)
	if timeout is None:
		exit_code = subprocess.call([cmd],shell=True)
		if not vaildate_exit_code(exit_code) :
			print("Exit Status error! status={}\nError cmd={}".format(exit_code,cmd))
			return 'error'
		else:
			return 'success'
	else:
		temp_cmd_file = 'temp_cmd_file.txt'
		temp_status = 'temp_status.txt'
		save_to_file(cmd,temp_cmd_file)

		cmd='python3 run_cmd_py3.py {} {} {}'.format(temp_cmd_file,temp_status,timeout)
		run_bash(cmd)

		return load_from_file(temp_status)

def run_mis(cnf_file,output_cnf_file):
	'''
	Find MIS of cnf_file and save to output_cnf_file
	:return : 'timeout', 'success'
	'''

	start_t = time.time()

	# Run MIS on file
	cmd = 'cd mis/ && python MIS.py -output=../mis.out {}'.format('../'+cnf_file)
	bash_output=run_bash(cmd,timeout=glbl_vars.timeout_limit)
	print 'mis',bash_output

	end_t=time.time()
	run_time=end_t-start_t

	# Check output status
	if bash_output=='timeout':
		print 'Timeout'
		run_bash('./kill_mis.sh')
		return 'timeout','timeout'
	elif bash_output=='error':
		return 'error','error'
	else:
		assert bash_output=='success'
		with open("mis.out", "r") as f_temp:
			c_ind = f_temp.read()
			c_ind = "c ind {}".format(c_ind[2:])
		with open("mis.out", "w") as f_temp:
			f_temp.write(c_ind)
		cmd = "cat {} >> {} && mv {} {}".format(cnf_file,'mis.out','mis.out',output_cnf_file)
		run_bash(cmd)
		return 'success',run_time

def run_approxMC(cnf_file,mis=False):
	'''
	Run cryptominsat (./scalmc) on cnf_file
	:param mis: preprocess cnf_file to find MIS
	:return : 'timeout', approximate number of SAT assignments
	'''

	# run MIS on file
	if mis:
		cnf_file_ind=cnf_file+'.ind'
		return_status,mis_time = run_mis(cnf_file,cnf_file_ind)
		if return_status == 'timeout':
			return 'timeout'
		else:
			assert return_status=='success'
			approxMC_input = cnf_file_ind
	else:
		approxMC_input = cnf_file


	start_t = time.time()
	approxMC_output=approxMC_input+'.sol.approx'
	# run approxMC on file
	cmd = "./scalmc {} > {}".format(approxMC_input, approxMC_output)
	bash_output=run_bash(cmd,timeout=glbl_vars.timeout_limit)
	print 'approxMC',bash_output
	end_t=time.time()
	run_time=end_t-start_t

	# Check output status
	if bash_output=='timeout':
		print 'Timeout'
		run_bash('./kill_approxMC.sh')
		return 'timeout','timeout'
	# The exit codes returned by approxMC do not follow common convention
	else:
		# Process approxMC output to get #Sols/check for error
		print "reading approxMC's output..."
		numSols = process_approxMC_output(approxMC_output)
		if numSols=='error':
			run_bash('mkdir segmentation_faults')
			run_bash('cp {} segmentation_faults/{}'.format(approxMC_input,approxMC_input))
			return 'error','error'
		else:
			return numSols,run_time

def run_weightMC(cnf_file,sol_file):
	start_t=time.time()
	# run weightMC on file
	cmd = "./weightmc {} > {}".format(cnf_file, sol_file)
	bash_output=run_bash(cmd,timeout=glbl_vars.timeout_limit)
	print 'weightMC',bash_output
	end_t=time.time()
	run_time=end_t-start_t

	# Check output status
	if bash_output=='timeout':
		print 'Timeout'
		run_bash('./kill_weightMC.sh')
		return 'timeout','timeout'
	# The exit codes returned by weightMC do not follow common convention
	else:
		# Process weightMC output to get #Sols/check for error
		print "reading weightMC's output..."
		numSols = process_weightMC_output(sol_file)
		if numSols=='error':
			run_bash('mkdir segmentation_faults')
			run_bash('cp {} segmentation_faults/{}'.format(cnf_file,cnf_file))
			return 'error','error'
		else:
			return numSols,run_time

def run_sharpSAT(cnf_file,sol_file,return_time=False):
	'''
	Run sharpSAT on cnf_file, save output to sol_file
	:return : 'timeout', exact number of SAT assignments
	'''

	# Run SharpSat on file
	cmd = "./sharpSAT {} > {}".format(cnf_file, sol_file)
	bash_output=run_bash(cmd,timeout=glbl_vars.timeout_limit)
	print 'sharpSAT',bash_output

	# Check output status
	if bash_output=='timeout':
		print 'Timeout'
		run_bash('./kill_sharpsat.sh')
		if return_time:
			return 'timeout','timeout'
		else:
			return 'timeout'
	elif bash_output=='error':
		if return_time:
			return 'error','error'
		else:
			return 'error'
	else:
		assert bash_output=='success'
		# Process sharpSat output to get #Sols
		print "reading SharpSat's output..."
		numSols = process_sharpSat_output(sol_file,return_time=return_time)
		return numSols
