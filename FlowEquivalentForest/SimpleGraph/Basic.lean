import Mathlib.Combinatorics.SimpleGraph.Basic

import FlowEquivalentForest.Util

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

@[simp]
def addEdges (G : SimpleGraph V) (s : Set (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet $ G.edgeSet ∪ s

noncomputable def dartNonDiagFinset (G : SimpleGraph V) : Finset (NonDiag V) :=
  have : DecidableRel G.Adj := Classical.decRel _
  Finset.filter (λ e => G.Adj e.fst e.snd) (Finset.univ (α := NonDiag V))

lemma addEdges_singleton_dartNonDiagFinset
    (G : SimpleGraph V)
    {u v : V}
    (huv : u ≠ v) :
    (G.addEdges {⟦(u, v)⟧}).dartNonDiagFinset = G.dartNonDiagFinset ∪ {NonDiag.mk' huv, NonDiag.mk' huv.symm} := sorry

lemma dartNonDiagFinset_disjoint_of_not_adj
    (G : SimpleGraph V)
    {u v : V}
    (huv : u ≠ v)
    (h : ¬G.Adj u v) :
    Disjoint G.dartNonDiagFinset {NonDiag.mk' huv, NonDiag.mk' huv.symm} := sorry

lemma deleteEdges_singleton_dartNonDiagFinset
    (G : SimpleGraph V)
    {u v : V}
    (huv : u ≠ v) :
    (G.deleteEdges {⟦(u, v)⟧}).dartNonDiagFinset = G.dartNonDiagFinset \ {NonDiag.mk' huv, NonDiag.mk' huv.symm} := sorry

lemma subset_dartNonDiagFinset_of_adj
    (G : SimpleGraph V)
    (h : G.Adj u v) :
    {NonDiag.mk' h.ne, NonDiag.mk' h.ne.symm} ⊆ G.dartNonDiagFinset := sorry
