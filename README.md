# Usage

This package is meant to be used from within sage-math notebooks.

Clone this repo as the 'matroids' subdirectory from the place where you want to use it, then add
`from matroids import *` to a cell and run it.

# Contents

* `TransversalMatroid` - matroid class implementation that gives you transversal matroids. Uses the sage built-in bipartite graphs and matching capabilities.
* `DigraphRouting` - class that represents a routing in a digraph.
* `Gammoid` - matroid class implementation that gives you gammoids through their representation using a digraph.
* `AGammoid` - gives you a gammoid as the (deletion of the) dual of the transversal matroid that corresponds to the linkage system of D onto T.
* `BicircularMatroid` - matroid class implementation for bicircular matroids
* `isStrictGammoid` - test whether a matroid is a strict gammoid

## Helpers
* `flattenDigraph` - helper for recovering a transversal 'major' (co-minor) of a gammoid
* `makeTargetsSinks` - removes outbound arcs for given set of vertices of a digraph
* `outboundNeighbors` - computes outbound accessible neighbors relative to a routing (needed for augmenting path analog for digraph routings)
* `petalBicircular` - generates elements of a special bicircular matroid class
* `petalBicircularDRR` - gives a duality respecting representation of the above class element
* `traverseArcs` - turns dictionary of successor vertices and a start vertex into a path

untrustworthy code:

* `prepareOrientationStructure` - prepares a SAT problem that tries to solve the problem of assigning each circuit in a given matroid a set of signs such that the result is an oriented matroid
* `solveOrientation` - tries to find an orientation of a given matroid
* `orientationToLattice`
* `testOrientation`