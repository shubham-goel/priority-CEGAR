import time
import pickle
import itertools
import subprocess
from optparse import OptionParser

from z3 import *

from Objects import *
from Graph import GenerateSetting
from Utilities import *

#######
# MAJOR
#######

def generalSimulationConstraints(stng,s, M, t, l,
	immediatefailure=False, l_is_upperBound=True):
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

	if l_is_upperBound:
		s.add(Sum([If(stng.vars.config(m, m.t, t), 1, 0) for m in M]) < l)
	else:
		s.add(Sum([If(stng.vars.config(m, m.t, t), 1, 0) for m in M]) >= l)

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

#######
# MINOR
#######

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
