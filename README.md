# Usage

This package is meant to be used from within sage-math notebooks.

Clone this repo as the 'matroids' subdirectory from the place where you want to use it, then add
`from matroids import *` to a cell and run it.

# Contents

* `TransversalMatroid` - matroid class implementation that gives you transversal matroids. Uses the sage built-in bipartite graphs and matching capabilities.
* `DigraphRouting` - class that represents a routing in a digraph.
* `Gammoid` - matroid class implementation that gives you gammoids through their representation using a digraph.
* `BicircularMatroid` - matroid class implementation for bicircular matroids
* `isStrictGammoid` - test whether a matroid is a strict gammoid

## Helpers
* `flattedDigraph` - helper for recovering a transversal 'major' (co-minor) of a gammoid
* `makeTargetsSinks` - removes outbound arcs for given set of vertices of a digraph

not trustworthy code:

* `prepareOrientationStructure` - prepares a SAT problem that tries to solve the problem of assigning each circuit in a given matroid a set of signs such that the result is an oriented matroid
* `solveOrientation` - tries to find an orientation of a given matroid
* `orientationToLattice`