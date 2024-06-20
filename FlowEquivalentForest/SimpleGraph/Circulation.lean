import Mathlib.Tactic.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

import FlowEquivalentForest.SimpleGraph.Path

open ContainsEdge

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : SimpleGraph V}

-- A directed cycle
structure Walk.IsCirculation (p : G.Walk v v) : Prop where
  ne_nil : p ≠ nil
  support_nodup : p.support.tail.Nodup

abbrev Circulation (v : V) := {p : G.Walk v v // p.IsCirculation}

@[simp]
instance : ContainsEdge V (G.Circulation v₀) where
  contains_edge c := contains_edge c.val

instance {c : G.Circulation v₀} : DecidableRel (contains_edge c) := by
  simp only [instContainsEdgeCirculation]
  infer_instance

theorem Path.cons_isCirculation (p : G.Path v u) (h : G.Adj u v) :
    (Walk.cons h p.val).IsCirculation where
  ne_nil := by simp only [ne_eq, not_false_eq_true]
  support_nodup := by
    rw[Walk.support_cons, List.tail_cons]
    exact p.prop.support_nodup

lemma Walk.IsCirculation.not_nil {p : G.Walk v v} (hc : p.IsCirculation) : ¬p.Nil := p.not_nil_of_ne_nil hc.ne_nil

theorem Walk.IsCirculation_iff (p : G.Walk u u) : p.IsCirculation ↔ ∃ (v : V) (h : G.Adj u v) (p' : G.Path v u), p = Walk.cons h p'.val := by
  constructor
  · intro hp
    let d := p.firstDart hp.not_nil
    use d.snd
    use d.is_adj
    have hp' := (p.cons_tail_eq hp.not_nil).symm
    use {
      val := p.tail hp.not_nil,
      property := IsPath.mk' (by
        have := hp' ▸ hp.support_nodup
        rwa[support_cons, List.tail_cons] at this
      )
    }
  · intro h
    obtain ⟨_, huv, p', hp'⟩ := h
    exact hp' ▸ p'.cons_isCirculation huv


theorem Walk.IsCirculation.reverse {G : SimpleGraph V} {p : G.Walk v v} (h : p.IsCirculation) : p.reverse.IsCirculation where
  ne_nil := SimpleGraph.Walk.reverse_ne_nil h.ne_nil
  support_nodup := by
    suffices List.Perm p.support.tail p.reverse.support.tail from
      (List.Perm.nodup_iff this).mp h.support_nodup

    suffices List.Perm p.support p.reverse.support by
      rwa[support_eq_cons p, support_eq_cons p.reverse, List.perm_cons] at this

    exact Walk.support_reverse _ ▸ (List.reverse_perm p.support).symm

lemma Walk.IsCirculation.darts_nodup {p : G.Walk u u} (h : p.IsCirculation) : p.darts.Nodup := by
  obtain ⟨v, huv, p', hp'⟩ := (Walk.IsCirculation_iff p).mp h
  subst hp'
  rw[darts_cons]
  apply List.Nodup.cons
  · intro hd; exact p'.val.end_ne_fst_of_mem_darts_of_support_nodup hd p'.nodup_support rfl
  · exact darts_nodup_of_support_nodup p'.nodup_support

lemma Walk.IsCirculation.dart_counts_nodup {p : G.Walk v v} (h : p.IsCirculation) : p.dart_counts.Nodup := by
  apply Multiset.coe_nodup.mpr
  exact h.darts_nodup

namespace Circulation

def reverse (c : G.Circulation v₀) : G.Circulation v₀ where
  val := c.val.reverse
  property := c.prop.reverse

lemma succ_exists {c : G.Circulation s} (hu: u ∈ c.val.support) :
    ∃! v, contains_edge c u v := by
  obtain ⟨u', hadj, p', hp'⟩ := Walk.not_nil_iff.mp c.prop.not_nil
  simp only [instContainsEdgeCirculation, hp', Walk.contains_edge_cons_iff]
  if hus : u = s then
    subst hus
    use u'
    simp
    intro v' hv' hd
    have := c.prop.support_nodup
    rw[hp', Walk.support_cons, List.tail_cons] at this
    have := p'.end_ne_fst_of_mem_darts_of_support_nodup hd this
    simp at this
  else
    have : p'.support.Nodup := by
      have := c.prop.support_nodup
      rwa[hp', Walk.support_cons, List.tail_cons] at this
    let p'' : G.Path _ _ := {
      val := p'
      property := Walk.IsPath.mk' this
    }
    rw[hp', Walk.support_cons, List.mem_cons] at hu
    have hu := hu.resolve_left hus
    obtain ⟨v, hv⟩ := p''.succ_exists hu hus
    use v
    use Or.inr hv.left
    intro v' hv'
    simp[hus] at hv'
    exact hv.right v' hv'

lemma pred_exists {c : G.Circulation s} (hc: v ∈ c.val.support) :
    ∃! u, contains_edge c u v := by
  have : v ∈ c.val.reverse.support := by simp_all only [Walk.support_reverse, List.mem_reverse]
  obtain ⟨u, hu⟩ := c.reverse.succ_exists this
  simp only [instContainsEdgeCirculation, reverse, Walk.reverse_contains_edge_iff] at hu ⊢
  use u

end Circulation
end SimpleGraph
