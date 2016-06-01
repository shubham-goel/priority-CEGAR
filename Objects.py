from z3 import *

class Vars:
	def __init__(self):
		self.vars = {}


	def def_sched(self, m, e, i):
		self.vars[(m,e,i)] = Bool('%s is scheduled on %s at time %d'%(str(m), str(e), i))

	def sched(self, m, e, i):
		return self.vars[(m,e,i)]

	def def_priority(self, m, v, j):
		self.vars[(m,v,j,'priority')] = Bool('%s at %s has priority %d'%(str(m), str(v), j))

	def priority(self, m, v, j):
		return self.vars[(m,v,j,'priority')]

	def def_config(self, m, v, i):
		self.vars[(m,v,i,'config')] = Bool('%s is on %s at time %d'%(str(m), str(v), i))

	def config(self, m, v, i):
		return self.vars[(m,v,i,'config')]

	def def_crash(self, e, i):
		self.vars[(e,i,'crash')] = Bool('%s crashes at time %d'%(str(e), i))

	def crash(self, e, i):
		'''
		Returns False if the variable (e,i,'crash') is not defined
		'''
		try:
			return self.vars[(e,i,'crash')]
		except KeyError:
			return False

	def def_delay(self, e, i):
		self.vars[(e,i,'delay')] = Bool('%s delays at time %d'%(str(e), i))

	def delay(self, e, i):
		'''
		Returns False if the variable (e,i,'delay') is not defined
		'''
		try:
			return self.vars[(e,i,'delay')]
		except KeyError:
			return False

	def def_omit(self, e, i):
		self.vars[(e,i,'omit')] = Bool('%s omits at time %d'%(str(e), i))

	def omit(self, e, i):
		'''
		Returns False if the variable (e,i,'omit') is not defined
		'''
		try:
			return self.vars[(e,i,'omit')]
		except KeyError:
			return False

	def def_used(self, m, e, i):
		self.vars[(m,e,i,'used')] = Bool('%s is using %s at time %d'%(str(m), str(e), i))

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

	def def_msgArrive(self, m):
		self.vars[m] = Bool('%s has arrived'%str(m))

	def msg(self, m):
		return self.vars[m]


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
		return '(%s, %s)'%(self.s, self.t)

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
