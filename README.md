# Usage

This package is meant to be used from within sage-math notebooks.

Clone this repo as the 'matroids' subdirectory from the place where you want to use it, then add
`from matroids import *` to a cell and run it.

# Contents

* `TransversalMatroid` - matroid class implementation that gives you transversal matroids. Uses the sage built-in bipartite graphs and matching capabilities.
* `DigraphRouting` - class that represents a routing in a digraph.
* `Gammoid` - matroid class implementation that gives you gammoids through their representation using a digraph.
