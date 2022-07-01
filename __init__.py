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
        
        
    def __repr__(self):
        return f"TransversalMatroid({self.facemap})"
        
