import math
from scipy.special import comb
from decimal import *


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

def prob_not_AMA(e,t,p_crashes=0,k_crashes=0,k_crashes_list=None,precision=None):
	if precision is not None:
		with localcontext() as ctx:
			ctx.prec = precision   # Perform a high precision calculation

			one = Decimal(1)
			e=Decimal(e)
			t=Decimal(t)
			p_crashes=Decimal(p_crashes)
			k_crashes=Decimal(k_crashes)
			a=(one-p_crashes)**((e-k_crashes)*t)*(p_crashes**k_crashes)
			b=Decimal(0)
			for j in k_crashes_list:
				b = b+(one-p_crashes)**(Decimal(j))
			res = a*b
		res = +res
		return res
	else:
		a=pow(1-p_crashes,(e-k_crashes)*t)*pow(p_crashes,k_crashes)
		b=0
		for j in k_crashes_list:
			b += pow(1-p_crashes,j)
		return a*b

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
