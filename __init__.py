import sage.matroids.matroid
import sage.graphs.bipartite_graph
import sage.graphs.digraph
import sage.matroids.dual_matroid
import itertools

# Straightforward implementation of a transversal matroid, using sage's facilities to find a maximal matching
# in a bipartite graph

class TransversalMatroid(sage.matroids.matroid.Matroid):
    def __init__(self, faceMap):
        """ creates a transversal matroid that uses bipartite graphs as a backend
        faceMap __ a map that maps each matroid element to a set of (abstract) vertices 
                   defining the face it is on (in general position) """
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

    
# Straightforward implementation of a gammoid
class Gammoid(sage.matroids.matroid.Matroid):
    def __init__(self, D, T, E=None):
        """ Create a strict gammoid.
            D __ digraph (some representation)
            T __ set of target vertices of D 
            E __ set of vertices that are edges in the matroid (optional)"""
        
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