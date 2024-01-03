import Mathlib.Combinatorics.SimpleGraph.Basic

import FlowEquivalentForest.Util

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

@[simp]
def addEdges (G : SimpleGraph V) (s : Set (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet $ G.edgeSet ∪ s

noncomputable def dartNonDiagFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (NonDiag V) :=
  Finset.filter (λ e => G.Adj e.fst e.snd) (Finset.univ (α := NonDiag V))
