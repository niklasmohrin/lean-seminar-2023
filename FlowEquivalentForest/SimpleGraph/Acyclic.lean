import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

import FlowEquivalentForest.SimpleGraph.Basic

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem deleteEdges_isAcyclic (G : SimpleGraph V) (hG : G.IsAcyclic) (s : Set (Sym2 V)) : (G.deleteEdges s).IsAcyclic := by
  by_contra h
  suffices ¬G.IsAcyclic by contradiction
  simp[isAcyclic_iff_path_unique] at h ⊢
  obtain ⟨a, b, p₁, hp₁, p₂, hp₂, hne⟩ := h
  have hle := SimpleGraph.deleteEdges_le G s
  use a
  use b
  use p₁.mapLe hle
  use (SimpleGraph.Walk.mapLe_isPath hle).mpr hp₁
  use p₂.mapLe hle
  use (SimpleGraph.Walk.mapLe_isPath hle).mpr hp₂
  by_contra heq
  refine hne $ Walk.map_injective_of_injective ?_ a b $ heq
  exact (Setoid.injective_iff_ker_bot ⇑(Hom.mapSpanningSubgraphs hle)).mpr rfl

theorem deleteEdges_not_reachable_of_mem_edges
    (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (p : G.Path s t)
    (huv : ⟦(u, v)⟧ ∈ p.val.edges) :
    ¬Reachable (G.deleteEdges {⟦(u, v)⟧}) s t := sorry

lemma foo (G H : SimpleGraph V) (h : G.edgeSet = H.edgeSet) : G = H := by exact edgeSet_inj.mp h

theorem addEdges_isAcyclic_of_not_reachable
    (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (huv : ¬G.Reachable u v) :
    (G.addEdges {⟦(u, v)⟧}).IsAcyclic := by
  wlog hne : u ≠ v
  · have heq : u = v := by by_contra h; contradiction
    subst heq
    suffices G = G.addEdges {⟦(u, u)⟧} by rwa[←this]
    simp only [←edgeSet_inj, addEdges, edgeSet_fromEdgeSet, Set.union_singleton, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, Set.insert_diff_of_mem]
    ext e
    constructor
    · intro he
      rw[Set.mem_diff]
      exact ⟨he, G.not_isDiag_of_mem_edgeSet he⟩
    · intro he
      rw[Set.mem_diff] at he
      exact he.left

  have h_eq_add_sub : G = fromEdgeSet (G.edgeSet ∪ {⟦(u, v)⟧}) \ fromEdgeSet {⟦(u, v)⟧} := by
    simp
    ext a b
    if hab : ⟦(a, b)⟧ = ⟦(u, v)⟧ then
      simp[hab]
      by_contra h
      rw[←mem_edgeSet, hab, mem_edgeSet] at h
      exact huv h.reachable
    else
      aesop

  rw[SimpleGraph.isAcyclic_iff_forall_edge_isBridge, Sym2.forall]
  intro a b hab
  if h_ab_uv : ⟦(a, b)⟧ = ⟦(u, v)⟧ then
    rw[h_ab_uv, SimpleGraph.isBridge_iff]
    constructor
    · exact (fromEdgeSet_adj _).mpr ⟨by simp only [Set.union_singleton, mem_edgeSet, Set.mem_insert_iff, true_or], hne⟩
    · rwa[addEdges, ←h_eq_add_sub]
  else
    rw[isBridge_iff_mem_and_forall_cycle_not_mem]
    constructor
    · exact hab
    · intro x c hc
      exfalso
      if hcuv : ⟦(u, v)⟧ ∈ c.edges then
        have : v ∈ c.support := Walk.snd_mem_support_of_mem_edges c hcuv
        let c' := c.rotate this
        have hc' := hc.rotate this
        -- TODO: The tail of c' is a walk from v to u, without using the
        -- inserted edge (u, v) edge. This contradicts that u and v are
        -- disconnected in g.
        sorry
      else
        -- TODO: c is a cycle in g, because the added edge is not part of
        -- it. I can maybe be transferred back to g, where it would then
        -- be a contradiction to g being a forest.
        sorry

