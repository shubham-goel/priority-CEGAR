from z3 import *

import global_vars as glbl_vars

class Vars:
	def __init__(self):
		self.vars = {}


	def def_sched(self, m, e, i, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('m%s is scheduled on e%s at time t%d'%(str(m), str(e), i))
		self.vars[(m,e,i)] = Bool(var_name)

	def sched(self, m, e, i):
		return self.vars[(m,e,i)]

	def def_priority(self, m, v, j, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('m%s at v%s has priority %d'%(str(m), str(v), j))
		self.vars[(m,v,j,'priority')] = Bool(var_name)

	def priority(self, m, v, j):
		return self.vars[(m,v,j,'priority')]

	def def_config(self, m, v, i, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('m%s is on v%s at time %d'%(str(m), str(v), i))
		self.vars[(m,v,i,'config')] = Bool(var_name)

	def config(self, m, v, i):
		return self.vars[(m,v,i,'config')]

	def def_crash(self, e, i, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('e%s crashes at time %d'%(str(e), i))
		self.vars[(e,i,'crash')] = Bool(var_name)

	def crash(self, e, i):
		'''
		Returns False if the variable (e,i,'crash') is not defined
		'''
		try:
			return self.vars[(e,i,'crash')]
		except KeyError:
			return False

	def def_delay(self, e, i, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('e%s delays at time %d'%(str(e), i))
		self.vars[(e,i,'delay')] = Bool(var_name)

	def delay(self, e, i):
		'''
		Returns False if the variable (e,i,'delay') is not defined
		'''
		try:
			return self.vars[(e,i,'delay')]
		except KeyError:
			return False

	def def_omit(self, e, i, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('e%s omits at time %d'%(str(e), i))
		self.vars[(e,i,'omit')] = Bool(var_name)

	def omit(self, e, i):
		'''
		Returns False if the variable (e,i,'omit') is not defined
		'''
		try:
			return self.vars[(e,i,'omit')]
		except KeyError:
			return False

	def def_used(self, m, e, i, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('m%s is using e%s at time %d'%(str(m), str(e), i))
		self.vars[(m,e,i,'used')] = Bool(var_name)

	def used(self, m, e, i):
		return self.vars[(m,e,i,'used')]

	def used_ex(self, m, e, i):
		'''
		Returns False if the variable (m,e,i,'used') is not defined
		'''
		try:
			return self.vars[(m,e,i,'used')]
		except KeyError:
			return False

	def def_msgArrive(self, m, basic_names=False):

		if basic_names:
			var_name = str(glbl_vars.variable_number)
			glbl_vars.variable_number += 1
		else:
			var_name = ('m%s has arrived'%str(m))
		self.vars[m] = Bool(var_name)

	def msg(self, m):
		return self.vars[m]

class Sim_Vars:
	def __init__(self):
		self.queue = {}
		self.config = {}
		self.crash = {}
		self.delay = {}
		self.omit = {}
		self.used = {}

class Vertex:
	def __init__(self, name):
		self.name = name
		self.__nextS = {}
		self.__nextF = {}

	def __str__(self):
		return str(self.name)

	def nextS(self,m):
		if m in self.__nextS:
			return self.__nextS[m]
		#if (m,self) in SC:
		#    return SC[(m,self)]

	def setNextS(self, m, u):
		self.__nextS[m] = u

	def nextF(self,m):
		if m in self.__nextF:
		   return self.__nextF[m]
		# if (m,self) in FC:
		#     return FC[(m,self)]

	def setNextF(self, m, u):
		self.__nextF[m] = u

	def __hash__(self):
		return hash(self.name)

	def __eq__(self, other):
		if not other:
			return False
		return self.name == other.name


class Edge:
	def __init__(self, s, t):
		self.s = s
		self.t = t

	def __str__(self):
		return '(%s-%s)'%(self.s, self.t)

	def __hash__(self):
		return hash((hash(self.s), hash(self.t)))

	def __eq__(self, other):
		return self.s == other.s and self.t == other.t

class Graph:
	def __init__(self, V, E):
		self.V = V
		self.E = E

	def __call__(self, v, u):
		for e in self.E:
			if e.s == v and e.t == u:
				return e


class Message:
	def __init__(self, s, t, name):
		self.s = s
		self.t = t
		self.name = str(name)
		self.id = name

	def __str__(self):
		return self.name

	def __lt__(self, m):
		return self.id < m.id

	def __le__(self, m):
		return self.id <= m.id

	def __hash__(self):
		return hash(self.id)

	def __eq__(self, other):
		if not other:
			return False
		return self.id == other.id

class Glbl:
	def __init__(self, g, vars, FCe, FCv, SCv, SCe, UFSv, edge_priority, messages_across=None):
		self.vars = vars
		self.g = g
		self.FCe = FCe
		self.SCe = SCe
		self.SCv = SCv
		self.FCv = FCv
		self.UFSv = UFSv
		self.edge_priority = edge_priority

class weight_var:
	def __init__(self, name, p=0):
		self.id = name
		self.name = name
		self.var = Bool('WV_'+str(name))
		self.weight = p

	def __str__(self):
		return str(self.var)

	def __lt__(self, m):
		return self.id < m.id

	def __le__(self, m):
		return self.id <= m.id

	def __hash__(self):
		return hash(self.id)

	def __eq__(self, other):
		if not other:
			return False
		return self.id == other.id

class myGoal:
	def __init__(self):
		self.constr_list = []
		self.backtracking = Stack()
	def __str__(self):
		return str(self.constr_list)
	def add(self,expr):
		self.constr_list.append(expr)
	def push(self):
		self.backtracking.push(len(self.constr_list))
	def pop(self):
		self.constr_list = self.constr_list[:self.backtracking.pop()]
	def get_goal(self):
		s = Goal()
		s.add(And(self.constr_list))
		return s
	def get_solver(self):
		s = Solver()
		s.add(And(self.constr_list))
		return s
	def print_constr(self):
		for i in self.constr_list:
			print i

class Stack:
	def __init__(self):
		self.items = []

	def isEmpty(self):
		return self.items == []

	def push(self, item):
		self.items.append(item)

	def pop(self):
		return self.items.pop()

	def peek(self):
		return self.items[len(self.items)-1]

	def size(self):
		return len(self.items)
