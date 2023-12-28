import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

@[simp]
def addEdges (G : SimpleGraph V) (s : Set (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet $ G.edgeSet ∪ s
