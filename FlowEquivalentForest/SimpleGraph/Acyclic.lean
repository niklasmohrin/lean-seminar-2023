import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Duplicate

import FlowEquivalentForest.SimpleGraph.Basic
import FlowEquivalentForest.SimpleGraph.Path

namespace SimpleGraph

open ContainsEdge

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
    ¬Reachable (G.deleteEdges {⟦(u, v)⟧}) s t := by
  by_contra h
  have p' := (Classical.choice h).toPath
  let p'' := p'.transfer G (by
    intro e he
    have := p'.val.edges_subset_edgeSet he
    rw[edgeSet_deleteEdges] at this
    simp_all only [mem_edgeSet, Set.mem_diff]
  )

  suffices p ≠ p'' from this (hG.path_unique p p'')
  suffices ⟦(u, v)⟧ ∉ p''.val.edges by
    by_contra heq
    subst heq
    contradiction
  simp only [Path.transfer, Walk.edges_transfer]
  by_contra hmem
  have := p'.val.edges_subset_edgeSet hmem
  rw[edgeSet_deleteEdges] at this
  simp_all only [Set.mem_diff, Set.mem_singleton_iff, not_true_eq_false]

theorem addEdges_isAcyclic_of_not_reachable
    (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (huv : ¬G.Reachable u v) :
    (G.addEdges {⟦(u, v)⟧}).IsAcyclic := by
  wlog hne : u ≠ v
  · exact False.elim $ not_ne_iff.mp hne ▸ huv $ Reachable.refl v

  intro v₀ cp hcp
  let c : SimpleGraph.Cycle _ := {
    val := cp,
    property := hcp,
  }

  if hc' : contains_edge c u v ∨ contains_edge c v u then
    wlog huv' : contains_edge c u v generalizing c u v
    · exact (Sym2.eq_swap ▸ this) (huv ∘ Reachable.symm) hne.symm c c.prop hc'.symm (hc'.resolve_left huv')

    have ⟨hadj, hd⟩ := huv'

    have hu := c.val.dart_fst_mem_support_of_mem_darts hd
    have huv' := c.contains_edge_rotate hu huv'
    let c := c.rotate hu

    let p := c.val.tail c.prop.not_nil
    have hvc := c.snd_eq_succ_start huv'
    have p : G.Walk v u := hvc ▸ p.transfer G (by
      intro e he
      have := p.edges_subset_edgeSet he
      simp at this
      exact this.left.resolve_left (by
        intro heq
        subst heq
        have : c.val.edges = ⟦(u, v)⟧ :: p.edges := by
          rw[c.edges_eq_firstEdge_cons, List.cons_eq_cons]
          exact ⟨by aesop, by aesop⟩
        have : List.Duplicate ⟦(u, v)⟧ c.val.edges := this ▸ List.Mem.duplicate_cons_self he
        exact this.not_nodup c.prop.edges_nodup
      )
    )
    exact huv p.reachable.symm
  else
    have : ∀ e ∈ c.val.edges, e ∈ G.edgeSet := by
      intro e he
      have := c.val.edges_subset_edgeSet he
      simp at this
      exact this.left.resolve_left (by
        intro heq
        subst heq
        cases c.val.mem_darts_of_mem_edges he with
        | inl hd =>
          have : contains_edge c u v := ⟨_, hd⟩
          exact hc' $ Or.inl this
        | inr hd =>
          have : contains_edge c v u := ⟨_, hd⟩
          exact hc' $ Or.inr this
      )
    exact hG (c.val.transfer G this) (c.prop.transfer this)
