import networkx
from networkx import NetworkXNoPath
import random
import itertools
import pickle
import matplotlib.pyplot as plt
import os

from Objects import *
import matplotlib.pyplot as plt

def GenerateSetting(n, m, e, weight=False, save=False, load=False, filename=None, custom=False):
	'''
	:param n: the number of vertices
	:param m: the number of messages
	:param e: the number of edges in the graph.
	'''

	if load:
		if custom:
			custom_file = 'custom.setting'
			with open(custom_file, 'r') as file:
				status=0
				num_vertices = 0
				edges = []
				messages = []
				for l in file:
					l = l.strip(' \n\t')
					if l== '' : continue
					if status  == 0:
						assert l == 'Edges'
						status += 1
					elif status == 1:
						if l == 'Messages':
							status += 1
						else:
							ends=l.split(' ')
							assert len(ends)==2
							end1 = int(ends[0])
							end2 = int(ends[1])
							edges.append((end1,end2))
							if max(end1,end2) > num_vertices-1:
								num_vertices = max(end1,end2) + 1
					elif status == 2:
						ends=l.split(' ')
						assert len(ends)==2
						end1 = int(ends[0])
						end2 = int(ends[1])
						messages.append((end1,end2,len(messages)))
				assert status==2

			vertices = range(num_vertices)
			G = networkx.DiGraph()
			G.add_nodes_from(vertices)
			G.add_edges_from(edges)
			M = messages

		else:
			with open(filename, 'r') as file:
				(G, M) =  pickle.load(file)

		assert len(M) == m
		assert networkx.number_of_nodes(G) == n
		assert networkx.number_of_edges(G) == e

	else:
		G = networkx.gnm_random_graph(n, e, directed=True)
		M = []

	# Printing Graph
	print("Nodes of graph: ")
	print(G.nodes())
	print("Edges of graph: ")
	print(G.edges())

	V = dict([(i,Vertex(i)) for i in range(n)])
	E = []
	for e in G.edges_iter():
		E.append(Edge(V[e[0]], V[e[1]]))
		# E.append(Edge(V[e[1]], V[e[0]]))
		if weight:
			G[e[0]][e[1]]['weight'] = 0


	g = Graph(V.values(), E)
	if load:
		M = [Message(V[s], V[t], name) for (s,t,name) in M]

	# Printing Graph
	pos=networkx.spring_layout(G)
	networkx.draw_networkx_nodes(G,pos,
								nodelist=range(n),
								node_color='r',
								node_size=500,
								alpha=0.8)
	networkx.draw_networkx_edges(G,pos,width=1.0,alpha=0.5)
	labels = {}
	for temp in range(n):
		labels[temp] = temp
	networkx.draw_networkx_labels(G,pos,labels,font_size=16)
	plt.savefig("graph.png") # save as png
	# plt.show() # display

	FCv = {} # m -> the vertices in FC[m]
	FCe = {} # m --> the edges in FV
	SCv = {} # m -> the vertices in SC[m]
	SCe = {} # m --> the edges in SC
	UFSv = {} # the union of vertices in FCv and SCv



	for i in range(m):
		if load:
			s = M[i].s.name
			t = M[i].t.name
			m = M[i]
		else:
			s = random.randint(0, n-1)
			t = s
			while t == s:
				t = random.randint(0,n-1)

			# # selecting graph diameter for all messages
			# longest_path=[]
			# for start_tmp in range(n):
			# 	for end_tmp in range(n):
			# 		try:
			# 			p = networkx.shortest_path(G, source=start_tmp, target=end_tmp)
			# 		except NetworkXNoPath:
			# 			p=[]
			# 			pass
			# 		if len(p) > len(longest_path):
			# 			longest_path = p
			# s = longest_path[0]
			# t = longest_path[-1]

			m = Message(V[s], V[t], i)
			M.append(m)

		#first path is the shortest path from s to t
		prev = V[s]
		FCv[m] = [prev]
		FCe[m] = []
		try:
			if not weight:
				p = networkx.shortest_path(G, source=s, target=t)
			else:
				p = networkx.shortest_path(G, source=s, target=t, weight='weight')
		except NetworkXNoPath:
			print "NO PATH"
			os._exit(1)

		for v in p[1:]:
			nextV = V[v]
			FCv[m].append(nextV)
			e = g(prev, nextV)
			assert e != None
			FCe[m].append(e)
			prev.setNextF(m, nextV)
			if weight:
				G[prev.name][nextV.name]['weight'] += 1
			prev = nextV


		#second path:
		#the second path does not use first-path edges

		#remember the edge weights
		if weight:
			weightDict = {}
			for e in FCe[m]:
				weightDict[e] = G[e.s.name][e.t.name]['weight']

		G.remove_edges_from([(e.s.name, e.t.name) for e in FCe[m]])



		#Algorithm for second-path:
		#iterate the first path in reversed order. For each vertex, find the shortest path to t that does not use the first-choice edges.
		#Add these vertices one after the other until you hit a vertex that is already in the second choice path.
		SCv[m] = []
		SCe[m] = []
		for v in reversed(FCv[m][:-1]):
			prev = v

			#if there is no second path, leave this field empty
			try:
				if not weight:
					p = networkx.shortest_path(G, source=v.name, target=t)
				else:
					p = networkx.shortest_path(G, source=v.name, target=t, weight='weight')
			except NetworkXNoPath:
				continue

			for u in p[1:]:
				nextV = V[u]
				assert g(prev,nextV) != None
				prev.setNextS(m, nextV)

				if nextV in SCv[m]:
					break

				SCv[m].append(nextV)
				SCe[m].append(g(prev, nextV))
				prev = nextV

			if weight:
				for i in range(len(p)-1):
					G[p[i]][p[i+1]]['weight'] += 1

		G.add_edges_from([(e.s.name, e.t.name) for e in FCe[m]])

		if weight:
			for e in FCe[m]:
				G[e.s.name][e.t.name]['weight'] = weightDict[e]


	for m in M:
		UFSv[m] = set([v for v in itertools.chain(FCv[m], SCv[m])])

	if save:
		file = open(filename, 'w')
		pickle.dump((G, [(m.s.name, m.t.name, m.id) for m in M]), file)
		file.close()


	return (g, M, FCv, FCe, SCv, SCe, UFSv)

if __name__=='__main__':
	print GenerateSetting(10, 5, 20)
