import sage.matroids.matroid
import sage.graphs.bipartite_graph
import sage.graphs.digraph
import sage.matroids.dual_matroid
import sage.graphs.graph
import itertools
from sage.all import vector

# Straightforward implementation of a transversal matroid, using sage's facilities to find a maximal matching
# in a bipartite graph

class TransversalMatroid(sage.matroids.matroid.Matroid):
    def __init__(self, faceMap):
        """ creates a transversal matroid that uses bipartite graphs as a backend
        faceMap __ a map that maps each matroid element to a set of (abstract) vertices 
                   defining the face it is on (in general position) 
                   
        ex: n = TransversalMatroid({'d': frozenset({1}), 'a': frozenset({0}), 'c': frozenset({0})})           
        """
        faceMap = dict(faceMap)
        
        E = set(faceMap)
        
        fm = {}
        Vs = set()
        
        from collections.abc import Iterable
        for e in E:
            f = faceMap[e]
            if isinstance(f,Iterable):
                fm[e] = frozenset(f)
            else:
                fm[e] = frozenset({f})
            Vs = Vs.union(fm[e])
            
        V = tuple(sorted(Vs))
        for e in E:
            fm[e] = frozenset(map(V.index, fm[e]))
            
        partition = [[('v',i) for i in range(len(V))],[('e',e) for e in E]]
        data = dict(map(lambda y: (('e',y[0]),[('v',z) for z in y[1]]),fm.items()))
        
        G = sage.graphs.bipartite_graph.BipartiteGraph(data,partition)
        self.GE = partition[1]
        self.GV = partition[0]
        self.G = G
        self.facemap = fm
        self.E = frozenset(E)
        self.V = V
        
    def groundset(self):
        return self.E
    
    def _rank(self, X):
        Xs = set([('e',x) for x in X])
        GX = self.G.subgraph(Xs.union(self.GV))
        return len(GX.matching())
        
    def _repr_(self):
        return f"TransversalMatroid({self.facemap})"
    
# Implementation helpers for gammoids that deal with augmentations of routings
       
def outboundNeighbors(D, paths, visited=None, V=None):
    """ computes the outbound neighbors that are accessible from each vertex wrt. to a given (partial) routing
        D       __ sage.graphs.digraph.DiGraph object
        paths   __ set/list consisting of the paths of the routing (as vertex-sequence)
        visited __ (optional) set of vertices visited by the paths
        V       __ (optional) set of vertices in D
        
        returns a dictionary that maps each vertex to a set of triples
            (v,X,(u,v))
        where X consists of edges of a visited path that need to be removed from the routing
           and (u,v) is the edge that needs to be added to the routing 
           in order to use the connection
    """
    if visited is None:
        visited = frozenset().union(*paths)
    if V is None:
        V = frozenset(D.vertex_iterator())
    D = sage.graphs.digraph.DiGraph(D)
        
    out = dict()
    
    for nonvisited in V.difference(visited):
        out[nonvisited] = frozenset([(v,frozenset(),(u,v)) for u,v,lbl in D.outgoing_edges(nonvisited) if v in V])
        
    for p in paths:
        Vp = frozenset(p) # vertices reached by the path
        neighbors = {}
        # initialize neighbors
        for u,v,_ in D.outgoing_edges(p[0]):
            if v in Vp:
                continue # do not jump back on the path
            neighbors[v] = (frozenset(),(u,v))
        
        for u,v in zip(p[:-1],p[1:]):
            #augment the list of dropped edges
            neighbors = dict((
                (t,(X.union({(u,v)}),e))            
                for (t,(X,e)) in neighbors.items()
            ))
            
            # by altering the path that visits v (and permuting targets in the routing),
            # we may go from v to any of the previous outbound neighbors on the path that
            # are not visited by this path when searching for an augmentation of the routing
            out[v] = frozenset((t,X,e) for t,(X,e) in neighbors.items())
            
            #update the neighbors: add new possible targets for subsequent vertices in the path
            for _,w,_ in D.outgoing_edges(v):
                if w in Vp:
                    continue # no back-jumps!
                if w in neighbors:
                    continue # we already have a way to get to w, which frees more vertices
                neighbors[w] = (frozenset(),(v,w))
    for v in visited:
        if not v in out:
            out[v] = frozenset()
    return out

def traverseArcs(start, arcs):
    """ traverse the arcs from the starting point
    
    start __ start vertex
    arcs  __ dictionary with successors
    
    returns the path starting in the start vector, or None if there is a cycle
    """
    
    v = start
    path = [v]
    
    while v in arcs:
        v = arcs[v]
        if v in path:
            return None
        path.append(v)
    
    return tuple(path)

class DigraphRouting(object):
    def _updateAugStructs(self):
        self.visited = set().union(*self.paths) # vertices that have been visited by a path
        augOut = outboundNeighbors(
            D=self.D,
            paths=self.paths,
            visited=self.visited,
            V=self.V)
        
        self.T1 = frozenset((p[-1] for p in self.paths))
        
        # disregard any outbound connectivity of any unused terminal
        for t in self.T.difference(self.T1):
            augOut[t] = frozenset()
            
        
        
        augA = dict((
            (u,frozenset((v for v,_,_ in d))) for u,d in augOut.items()
        ))
        
        
        self.aug = augOut
        self.augD = sage.graphs.digraph.DiGraph(augA)
        self.augA = augA
        
        self.traversed = frozenset((
            (u,v) 
                  for p in self.paths
                  for u,v in zip(p[:-1],p[1:]) 
        ))
        
        
    def __init__(self, D, T, validatePaths=False):
        """ Create an empty digraph routing 
            D _ digraph (some representation)
            T _ set of target vertices to be considered for routings
            validatePaths _ set to true to check whether the paths obtained from the iterator are okay,
                            (should not be needed for BFS path enumeration)
        """
        D0 = sage.graphs.digraph.DiGraph(D)
        V0 = frozenset(D0.vertex_iterator())
        T0 = V0.intersection(T)
        
        self.D = D0
        self.V = V0
        self.T = T0
        self.validatePaths = validatePaths
        
        self.paths = set() # paths in the routing (as tuples of vertices)
        
        self._updateAugStructs()
        
        
    def augment(self, source):
        """ Try to augment the routing such that another source routes to the target set
            source __ vertex that should be added to the routing
            
            returns True, if the augmentation was possible, False otherwise
        """
        usedT = frozenset((p[-1] for p in self.paths))
        freeT = self.T.difference(usedT)
    
        for p0 in self.augD.all_paths_iterator([source],freeT,simple=True,trivial=True):
            # notice: the candidate path p0 may have several backjumps using the same original 
            #         routing path which is something that is not necessary, i.e., if you have 
            #         a path with more than one backjump on the same original routing path
            #         *and the backjumps cross*, then you can fix the path by shortening it
            #         If BFS is used to obtain the paths, then the 'weird' paths come after
            #         their non-weird counterparts, because the 'weird' paths have more vertices.
            #         DiGraph.all_paths_iterator guarantees that the paths are enumerated in 
            #         increasing length order, making p0 a non-weird path (if a path exists).
            #         But this guarantee may break at some point, so to be safe, we implement
            #         a validity check.

            S = frozenset((p[0] for p in self.paths)).union({p0[0]})
            P = frozenset((
                x
                for u,v in zip(p0[:-1],p0[1:])
                for x in self.aug[u] 
                    if x[0] == v  
                ))
            X = frozenset().union(*(X for _,X,_ in P)) # deleted arcs
            Y = frozenset((y for _,_,y in P)) # new arcs
            traversed = dict(self.traversed.difference(X).union(Y))
            
            paths = frozenset((traverseArcs(s,traversed) for s in S))

            if (not self.validatePaths) or self.isValid(paths):
                self.paths = paths
                self._updateAugStructs()
                return True
            else:
                print(f"Warning: got weird path {p0} first!")
                
        
        # source cannot reach any unused target
        
        return False
    
    def drop(self, *vertices):
        """ Drops all paths from the routing that use one of the given vertices
            *vertices __ list of vertices whose paths should be dropped
            
            returns the number of dropped paths
        """
        drop = frozenset(vertices)
        l = len(self.paths)
        paths = frozenset((
            p for p in self.paths
              if not drop.intersection(p)
        ))
        
        self.paths = paths
        self._updateAugStructs()
        
        return l-len(self.paths)
    
    def isValid(self,paths=None):
        """ checks whether the routing is indeed a routing in the underlying digraph 
            paths __ set of paths (optional)
        """
        if paths is None:
            paths = self.paths
        else:
            paths = frozenset(paths)
        # no vertex may be on two paths
        totalCount = len(frozenset().union(*paths))
        sumCounts = sum((len(p) for p in paths))
        if totalCount != sumCounts:
            return False
        # each path must end in a target vertex
        if not frozenset((p[-1] for p in paths)).issubset(self.T):
            return False
        # update the traversed arcs struct
        traversed = frozenset((
            (u,v) 
                  for p in paths
                  for u,v in zip(p[:-1],p[1:]) 
        ))
        # paths must traverse arcs of D
        for u,v in traversed:
            if not self.D.has_edge(u,v):
                return False
        return True

    def pivot(self):
        """ returns the digraph that results from pivoting in the routing
        """
        arcs = frozenset((u,v) for u,v,_ in self.D.edges())
        for p in self.paths:
            for r,s in zip(p[::-1][1:],p[::-1][:-1]):
                uNotTail = frozenset(((u,v) for u,v in arcs if u != r))
                rOuterExtension = frozenset((v for u,v in arcs if u == r)).union({r})
                sOut = frozenset(((s,x) for x in rOuterExtension)).difference({(s,s)})
                arcs = uNotTail.union(sOut)
        out = dict(( (v,frozenset((w for u,w in arcs if u == v))) for v in self.V))
        return sage.graphs.digraph.DiGraph(out)

    def targets(self):
        """ returns the targets used by paths in the routing
        """
        return frozenset((p[-1] for p in self.paths))

    def sources(self):
        """ returns the first vertices of paths in the routing
        """
        return frozenset((p[0] for p in self.paths))

# Helper for the gammoid implementation
    
def flattenDigraph(D):
    """
        Takes a digraph and turns vertices that have both inbound and outbound 
        arcs into gadgets that don't.
        
        D __ digraph
        

        returns a pair (D0, T0, X0) where 
            D0 is a digraph that consists solely of sources and sinks;
            T0 is the set of newly created sinks (have been in D before);
            X0 is the set of vertices that need to be contracted
    """
    V = D.vertices()
    degrees = zip(V,D.in_degree(V),D.out_degree(V))
    gadgetify = [v for v,i,o in degrees if i > 0 and o > 0]
    if not gadgetify:
        return D, [], []
    D0 = sage.graphs.digraph.DiGraph(D)
    X0 = []
    for v in gadgetify:
        t = D0.add_vertex(name=None)
        X0.append(t)
        edges = list(D.outgoing_edges(v))
        D0.delete_edges(edges)
        D0.add_edge(t,v)
        for q,r,label in edges: # q == v
            D0.add_edge(t,r,label)
            
    return D0, gadgetify, X0

def makeTargetsSinks(D,T):
    """
        D __ digraph
        T __ set of vertices that should be turned into sinks

        returns a copy of D minus all arcs (edges) that start in any element from T
    """
    D2 = sage.graphs.digraph.DiGraph(D)
    D2.delete_edges(((u,v,l) for (u,v,l) in D.edges() if u in T ))
    return D2
    
# Straightforward implementation of a gammoid
class Gammoid(sage.matroids.matroid.Matroid):
    def __init__(self, D, T, E=None):
        """ Create a strict gammoid.
            D __ digraph (some representation)
            T __ set of target vertices of D 
            E __ set of vertices that are edges in the matroid (optional)
            
            
            ex: m = Gammoid({'a':"efg",'b':"cdf",'f':"xyz",'d':"z","x":"z"},"xyz","abcdefg")
            
            """
        
        D0 = sage.graphs.digraph.DiGraph(D)
        V0 = set(D0.vertex_iterator())
        T0 = V0.intersection(T)
        if E is None:
            E0 = V0
        else:
            E0 = frozenset(V0).intersection(E)
            
        self.E = E0
        self.T = frozenset(T0)
        self.D = D0

    def targetsAreEdges(self):
        """ checks whether every target is also an edge
        """
        return self.T.issubset(self.E)

    def normalizeTargets(self,key=None):
        """ modifies the digraph representation, such that
            - every target is also an edge of the matroid
            - the miminal base wrt. to the sorting is the target set

            key __ (optional) passed over to sorted(..)
        """
        E = list(sorted(self.E,key=key))
        R = DigraphRouting(self.D,self.T)
        for e in E:
            R.augment(e)
        D = R.pivot()
        T = R.sources()
        return Gammoid(D,T,self.E)


    def groundset(self):
        return self.E

    def isCanonicalDRR(self):
        """ checks whether the underyling representation of this gammoid is a canonical duality respecting representation
        """
        if not self.targetsAreEdges():
            return False
        sources = self.E.difference(self.T)
        sinks = self.T
        fixSources = frozenset((s for s in sources if self.D.neighbors_in(s)))
        fixSinks = frozenset((s for s in sinks if self.D.neighbors_out(s)))
        return not fixSources.union(fixSinks)

    def _canonicalDRRDigraph(self):
        if not self.targetsAreEdges():
            raise "ERROR: Targets must be chosen from E"

        sources = self.E.difference(self.T)
        sinks = self.T
        fixSources = frozenset((s for s in sources if self.D.neighbors_in(s)))
        fixSinks = frozenset((s for s in sinks if self.D.neighbors_out(s)))
        V = set(self.D.vertex_iterator())
        usedVertices = set((str(v) for v in V))
        edges = list(self.D.edges())
        vidx = 1
        for s in fixSources:
            while f"v{vidx}" in usedVertices:
                vidx += 1

            v = f"v{vidx}"
            usedVertices.add(v)
            V.add(v)

            # rename s to v
            edges = list(map(lambda x: 
                            (x[0] if x[0] != s else v, 
                             x[1] if x[1] != s else v, 
                             x[2]), 
                        edges))
            # add arc from s -> v
            edges.append((s,v,None))
        for s in fixSinks:
            while f"v{vidx}" in usedVertices:
                vidx += 1

            v = f"v{vidx}"
            usedVertices.add(v)
            V.add(v)

            # rename s to v
            edges = list(map(lambda x: 
                            (x[0] if x[0] != s else v, 
                             x[1] if x[1] != s else v, 
                             x[2]), 
                        edges))
            # add arc from v -> s
            edges.append((v,s,None))
        outArcs = dict(([v,[]] for v in V))
        for u,v,_ in edges:
            outArcs[u].append(v)
        D = sage.graphs.digraph.DiGraph(outArcs)
        return D

    def canonicalDRR(self):
        """ returns a canonical duality respecting representation of this gammoid
        """
        if self.isCanonicalDRR():
            return self

        if self.targetsAreEdges():
            M = self
        else:
            M = self.normalizeTargets()

        return Gammoid(M._canonicalDRRDigraph(), M.T, M.E)

    def dual(self):
        if self.isCanonicalDRR():
            return Gammoid(self.D.reverse(),self.E.difference(self.T),self.E)
        return sage.matroids.dual_matroid.DualMatroid(self)

    
    def routing(self,X):
        """ finds a maximal routing from (a subset of) X to the set T
        """
        R = DigraphRouting(self.D, self.T)
        for x in X:
            R.augment(x)
        return R
    
    def _rank(self, X):
        return len(self.routing(X).paths)
        
    def _repr_(self):
        return f"Gammoid({self.D},{self.T},{self.E})"
    
    def isObviouslyTransversal(self):
        """ tests whether the digraph of this representation allows to quickly see that the gammoid is a transversal matroid
        """
        # If there are no paths from E to T in D which traverse more than a single arc, then we can just read off the transversal system
        # corresponding to the represented gammoid
        for p in self.D.all_paths_iterator(starting_vertices=self.E, ending_vertices=self.T, simple=True, trivial=True):
            if len(p) > 2:
                return False
        return True
    
    def flattenRepresentation(self):
        """ Modifies the digraph of the representation such that it becomes obviously transversal.
            Returns (M,C) where M is the constructed Gammoid and C is a set of vertices that needs 
            to be contracted in order to get this Gammoid back.
        """
        D0,T0,X0 = flattenDigraph(makeTargetsSinks(self.D,self.T))
        M0 = Gammoid(D0,self.T.union(T0),self.E.union(X0))
        return (M0,X0)

    def superTransversal(self):
        """ Returns a transversal matroid that contracts to this matroid; represented as TransversalMatroid
        """
        if not self.isObviouslyTransversal():
            M0,X0 = self.flattenRepresentation()
            return M0.superTransversal()
        faceMap = {e:[v for u,v,l in self.D.outgoing_edges(e) if v in self.T]+([e] if e in self.T else []) for e in self.E}
        return TransversalMatroid(faceMap)
        

## Test for strict gammoid

def isStrictGammoid(M):
    """ tests a matroid whether it is a strict gammoid using Mason's alpha criterion
        M __ matroid

        return False if M is not a strict gammoid,
           and True if it is.
    """
    alpha = {}
    
    allFlats = itertools.chain.from_iterable((M.flats(r) for r in range(0,M.rank()+1)))
    allDependentFlats = filter(M.is_dependent, allFlats)
    # compute Mason's alpha for all dependent flats
    for x in allDependentFlats:
        nlt = len(x) - M.rank(x)
        for y in alpha:
            if y.issubset(x):
                nlt -= alpha[y]
        if nlt < 0:
            return False # not a strict gammoid
        alpha[x] = nlt
        
    nonZero = frozenset([x for x in alpha.keys() if alpha[x] > 0])
    testSets = set()
    for i in range(2,len(nonZero)):
        for Q in itertools.combinations(nonZero,i):
            testSets.add(frozenset().union(*Q))
    # compute Mason's alpha for unions of dependent flats with positive alpha
    for x in testSets.difference(alpha.keys()):
        nlt = len(x) - M.rank(x)
        for y in alpha:
            if y.issubset(x):
                nlt -= alpha[y]
        if nlt < 0:
            return False # not a strict gammoid
    # all alpha values are non-negative => M is a strict gammoid
    return True

## implementation of a bicircular matroid using the sage Graph class

class BicircularMatroid(sage.matroids.matroid.Matroid):
    def __init__(self, edgeVertexMap):
        """ creates a bicircular matroid 
        edgeVertexMap __ a map that maps each matroid element an edge of a graph 
        
        ex: m = BicircularMatroid({"a":[0,1],"b":[1,2],"c":[2,0],"x":[2,8],"d":[8,9],"e":[9,8],"f":[9,9]})
        """
        edgeVertexMap = dict(edgeVertexMap)
        edgeVertexMap = dict(((k,list(v)) for k,v in edgeVertexMap.items()))
        
        E = set(edgeVertexMap)
        
        self.edgeVertexMap = edgeVertexMap
        self.E = frozenset(E)
        # not needed, but still handy
        self.G = sage.graphs.graph.Graph(loops=True,multiedges=True)
        for edge,uv in self.edgeVertexMap.items():
            self.G.add_edge(uv[0],uv[-1],edge)
        
    def groundset(self):
        return self.E
    
    def _rank(self, X):
        # create the appropriate subgraph from the edgeVertexMap
        G = sage.graphs.graph.Graph(loops=True,multiedges=True)
        for edge in set(X):
            uv = self.edgeVertexMap[edge]
            G.add_edge(uv[0],uv[-1],edge)
        # determine the size of a base of X
        rank = 0
        for component in G.connected_components():
            G0 = G.subgraph(component)
            T = next(G0.spanning_trees(True))
            # we may augment T with up to one edge in order to get a bicircular basis for the component
            rank += min(len(G0.edges()),len(T.edges())+1)
        
        return rank
        
    def _repr_(self):
        return f"BicircularMatroid({self.edgeVertexMap})"

## check a matroid for how many 'positive' colines there are

def categorizeColines(M,onlySummary=False):
    """
        M __ matroid

        onlySummary __ if set, then only the summary (positive and fat colines) will be returned

        returns a dictionary with information of the number of copoints with a given cardinality per coline,
                and an entry how many positive colines there are
    """
    rk = M.rank()
    result = {'positive':0,'fat':0}
    copoints = list(M.flats(rk-1))
    colines = list(M.flats(rk-2))
    for l in colines:
        cmap = {}
        cardL = len(l)
        countP = 0
        for p in copoints:
            if l.issubset(p):
                countP += 1
                cardP = len(p)
                delta = cardP-cardL
                cmap[delta] = 1 + cmap.get(delta,0)
        if not onlySummary:
            result[l] = cmap
        kind = 'positive' if cmap.get(1,0)*2 > countP else 'fat'
        result[kind] = 1 + result.get(kind,0)
    return result

## This can be used to get counter-examples to the theory that gammoids always have a positive coline

def petalBicircular(count,length):
    """
        count __ number of petals
        length __ length of the circle of the petal (or lollipop -<>)
    
        Bicircular Matroid on a graph that looks like lollipops that grow out of a single vertex
        
        <>--<> (would be count = 2, length = 4) 
        
        These kind of bicircular matroids can be used to find strict gammoids without a positive coline,
        for instance
        
            petalBicircular(3,4).dual()
        
        has one fat (3 copoints with cardinality 5) and no positive coline.
    
        returns a BicircularMatroid
    """
    d = {}
    vertex = 1
    for p in range(count):
        v0 = vertex
        d[f"stem{p}.0"] = [0,v0]
        for l in range(length):
            u = v0+l
            v = v0+(l+1)%length
            d[f"x{p}.{l}"] = [u,v]
        vertex += length
    return BicircularMatroid(d)
            
## petalBicircular matroid represented as gammoid through a duality respecting representation

def petalBicircularDRR(count,length):
    """
        count __ number of petals
        length __ length of the circle of the petal (or lollipop -<>)
    
        Bicircular Matroid on a graph that looks like lollipops that grow out of a single vertex
        
        <>--<> (would be count = 2, length = 4) 
        
        These kind of bicircular matroids can be used to find strict gammoids without a positive coline,
        for instance
        
            petalBicircularDRR(3,4).dual()
        
        has one fat (3 copoints with cardinality 5) and no positive coline.
    
        returns a Gammoid with a duality respecting representation
    """
    if count <= 1:
        return Gammoid({},[],[])
    d = {'stem0.0':[]}
    targets = ['stem0.0']
    
    for c in range(count):
        for p in range(length):
            d[f'x{c}.{p}'] = []
            targets.append(f'x{c}.{p}')
        
    for c in range(1,count):
        d[f'stem{c}.0'] = ['v'] + [f'x{c}.{p}' for p in range(length)]
        
    if count > 1:
        d['v'] = ['stem0.0'] + [f'x0.{p}' for p in range(length)]

    groundset = frozenset(d.keys()).difference(['v'])

    return Gammoid(d,targets,groundset)

## Tools needed to orient a given matroid (gammoids can always be oriented)

import itertools
import sage.logic.propcalc as propcalc
from sage.sat.solvers.picosat import PicoSAT

def prepareOrientationStructure(M,getSolver=PicoSAT):
    """
        M         __ matroid
        getSolver __ (optional) function that returns a sat solver
        
        returns (s,m, FC, FCd) where
             s   __ an instance of the SAT problem of assigning an orientation to M
             m   __ maps variable indexes to triples
                           (t, X, x) where t is either 'circuit' or 'cocircuit'
                                           X is the corresponding circuit or cocircuit
                                           x is the corresponding element of X
             FC __ family of circuits
             FCd __ family of cocircuits
              
    """
    
    FC = [sorted(x) for x in M.circuits()]
    FCd = [sorted(x) for x in M.cocircuits()]
    FC_idx = []
    FCd_idx = []
    
    idx = 0
    m = {}

    for c in FC:
        c_ = frozenset(c)
        idxs = []
        for x in c:
            idx += 1
            m[idx] = ('circuit',c_,x)
            idxs.append(idx)
        FC_idx.append(idxs)
        
    for d in FCd:
        d_ = frozenset(d)
        idxs = []
        for y in d:
            idx += 1
            m[idx] = ('cocircuit',d_,y)
            idxs.append(idx)
        FCd_idx.append(idxs)
        
    x = [propcalc.formula(f"x{i}") for i in range(idx+1)]
    
    s = getSolver()
    
    conditions = []
    goodCombinations = [(a,b,c,d) for a in [-1,1] for b in [-1,1] for c in [-1,1] for d in [-1,1] if a*b == -c*d]
    def applyToVar(x,sign):
        if sign < 0:
            return ~x
        return x
    
    for i,c in enumerate(FC):
        supC = frozenset(c)
        for j,d in enumerate(FCd):
            sup = supC.intersection(d)
            if sup:
                if len(sup) == 1:
                    raise f"Matroid {M} has a problem: circuit and cocircuit intersect in exactly one element, {c}, {d}!"
                for e,f in itertools.combinations(sup,2):
                    ce_idx = FC[i].index(e)
                    cf_idx = FC[i].index(f)
                    de_idx = FCd[j].index(e)
                    df_idx = FCd[j].index(f)
                    xce = x[FC_idx[i][ce_idx]]
                    xcf = x[FC_idx[i][cf_idx]]
                    xde = x[FCd_idx[j][de_idx]]
                    xdf = x[FCd_idx[j][df_idx]]
                    existsOne = [applyToVar(xce,a)&applyToVar(xde,b)&applyToVar(xcf,c)&applyToVar(xdf,d) 
                                 for a,b,c,d in goodCombinations]
                    existence = existsOne[0]
                    for f in existsOne[1:]:
                        existence = existence | f
                    existence.convert_cnf()
                    conditions.append(existence)
    
    def extractParts(t):
        if type(t) != list:
            t = [t]
        op = t[0]
        if op == '&':
            return extractParts(t[1]) + extractParts(t[2])
        else:
            return [t]
        
    def getSatPart(t):
        if type(t) != list:
            t = [t]
        op = t[0]
        if op == '|':
            return getSatPart(t[1]) + getSatPart(t[2])
        elif op == '~':
            return [-x for x in getSatPart(t[1])]
        elif op.startswith('x'):
            return [int(op[1:])]
    
    for f in conditions:
        for df in extractParts(f.full_tree()):
            pt = getSatPart(df)
            s.add_clause(pt)
                
    return (s, m, FC,FCd)

def solveOrientation(M,getSolver=PicoSAT):
    """
        M __ matroid
        getSolver __ (optional) function that returns a sat solver
        
        returns an orientation of M, or None if M cannot be oriented
        
            The orientation is a tuple
            
            (C,Cd)
            
                where C  contains the circuits
                and   Cd contains the cocircuits;
                
            and both C and Cd are dictionaries that map each (co-)circuit
            to a dictionary that gives the orientation of the element wrt to the
            (co-)circuit. The (-1)-companion is omitted from these dictionaries.

        ex:

            m = petalBicircular(3,4).dual()
            C,Cd = solveOrientation(m)
        
    """
    s,m,FC,FCd = prepareOrientationStructure(M,getSolver)
    sltn = s()
    
    C = {}
    Cd = {}
    
    if sltn == False:
        return None
    
    for idx, val in enumerate(sltn):
        if idx == 0:
            continue
        t, X, x = m[idx]
        if t == 'circuit':
            Xd = C.get(X,{})
            C[X] = Xd
        elif t == 'cocircuit':
            Xd = Cd.get(X,{})
            Cd[X] = Xd
        Xd[x] = +1 if not val else -1
    return (C,Cd)
    
def testOrientation(C,Cd):
    """
        C __ circuit orientation
        Cd __ cocircuit orientation

        return True, if the property (O1) holds
    """
    for c in C:
        cc = C[c]
        for d in Cd:
            sup = c.intersection(d)
            if sup:
                dd = Cd[d]
                foundPair = False
                for e,f in itertools.combinations(sup,2):
                    if cc[e] * dd[e] == - cc[f] * dd[f]:
                        foundPair = True
                        break
                if not foundPair:
                    return False
                
    return True

##  converts dictionary orientations to vector orientations

def orientationToLattice(C):
    """
        C __ dictionary of oriented circuit or co-circuit family in dictionary format

        returns dictionary as integer lattice vectors
    """
    groundset = sorted(frozenset().union(*C.keys()))
    idx = dict([(e,i) for i,e in enumerate(groundset)])
    d = {}
    for c in C:
        v = [0 for e in groundset]
        cc = C[c]
        for e in cc:
            v[idx[e]] = cc[e]
        d[c] = vector(v)
    return d
