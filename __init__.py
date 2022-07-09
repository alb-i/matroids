import sage.matroids.matroid
import sage.graphs.bipartite_graph
class TransversalMatroid(sage.matroids.matroid.Matroid):
    def __init__(self, faceMap):
        """ faceMap __ a map that maps each matroid element to a set of (abstract) vertices defining the face it is on (in general position)"""
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
        print(data)
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
