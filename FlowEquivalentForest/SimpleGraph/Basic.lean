import Mathlib.Combinatorics.SimpleGraph.Basic

import FlowEquivalentForest.Util

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

@[simp]
def addEdges (G : SimpleGraph V) (s : Set (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet $ G.edgeSet ∪ s

noncomputable instance {G : SimpleGraph V} : DecidableRel G.Adj := Classical.decRel _

def dartNonDiagFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (NonDiag V) :=
  Finset.filter (λ e => G.Adj e.fst e.snd) (Finset.univ (α := NonDiag V))

theorem mem_dartNonDiagFinset_iff (G : SimpleGraph V) (e : NonDiag V) : e ∈ G.dartNonDiagFinset ↔ G.Adj e.fst e.snd := by
  rw[dartNonDiagFinset, Finset.mem_filter, and_iff_right (Finset.mem_univ e)]

lemma addEdges_singleton_dartNonDiagFinset
    (G : SimpleGraph V)
    {u v : V}
    (huv : u ≠ v) :
    (G.addEdges {s(u, v)}).dartNonDiagFinset = G.dartNonDiagFinset ∪ {NonDiag.mk' huv, NonDiag.mk' huv.symm} := by
  ext e
  simp only [mem_dartNonDiagFinset_iff, Finset.mem_union, addEdges, fromEdgeSet_adj, Set.mem_union, mem_edgeSet]
  rw[and_iff_left e.ne]
  apply or_congr
  · rfl
  · aesop

lemma dartNonDiagFinset_disjoint_of_not_adj
    (G : SimpleGraph V)
    {u v : V}
    (huv : u ≠ v)
    (h : ¬G.Adj u v) :
    Disjoint G.dartNonDiagFinset {NonDiag.mk' huv, NonDiag.mk' huv.symm} := by
  simp
  exact ⟨
    h ∘ (G.mem_dartNonDiagFinset_iff _).mp,
    h ∘ SimpleGraph.Adj.symm ∘ (G.mem_dartNonDiagFinset_iff _).mp
  ⟩

lemma deleteEdges_singleton_dartNonDiagFinset
    (G : SimpleGraph V)
    {u v : V}
    (huv : u ≠ v) :
    (G.deleteEdges {s(u, v)}).dartNonDiagFinset = G.dartNonDiagFinset \ {NonDiag.mk' huv, NonDiag.mk' huv.symm} := by
  ext e
  simp only [mem_dartNonDiagFinset_iff, deleteEdges_adj, Finset.mem_sdiff]
  apply and_congr
  · rfl
  · simp only [Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    aesop

lemma subset_dartNonDiagFinset_of_adj
    (G : SimpleGraph V)
    (h : G.Adj u v) :
    {NonDiag.mk' h.ne, NonDiag.mk' h.ne.symm} ⊆ G.dartNonDiagFinset := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_dartNonDiagFinset_iff, h, h.symm, and_self]
