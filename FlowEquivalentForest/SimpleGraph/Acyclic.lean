import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Duplicate

import FlowEquivalentForest.SimpleGraph.Basic
import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Cycle

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

lemma deleteEdges_not_mem_edgeSet_of_mem (G : SimpleGraph V) (s : Set (Sym2 V)) (h : s(u, v) ∈ s) :
    s(u, v) ∉ (G.deleteEdges s).edgeSet := by aesop

theorem deleteEdges_not_reachable_of_mem_edges
    (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (p : G.Path s t)
    (huv : s(u, v) ∈ p.val.edges) :
    ¬(G.deleteEdges {s(u, v)}).Reachable s t := by
  intro h
  have p' := (Classical.choice h).toPath

  have hp' : s(u, v) ∉ p'.val.edges :=
    G.deleteEdges_not_mem_edgeSet_of_mem _ rfl ∘ p'.val.edges_subset_edgeSet (e := s(u, v))

  let p'' := p'.transfer G (by
    intro e he
    have := p'.val.edges_subset_edgeSet he
    simp_all only [edgeSet_deleteEdges, mem_edgeSet, Set.mem_diff]
  )

  have hp'' : s(u, v) ∉ p''.val.edges := (Walk.edges_transfer ..).symm ▸ hp'
  rw[hG.path_unique p'' p] at hp''
  contradiction

theorem addEdges_isAcyclic_of_not_reachable
    (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (huv : ¬G.Reachable u v) :
    (G.addEdges {s(u, v)}).IsAcyclic := by
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
        have : c.val.edges = s(u, v) :: p.edges := by
          rw[c.edges_eq_firstEdge_cons, List.cons_eq_cons]
          exact ⟨by aesop, by aesop⟩
        have : List.Duplicate s(u, v) c.val.edges := this ▸ List.Mem.duplicate_cons_self he
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
