import Mathlib.Tactic.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

import FlowEquivalentForest.SimpleGraph.Circulation

open ContainsEdge

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : SimpleGraph V}

abbrev Cycle (v : V) := { p : G.Walk v v // p.IsCycle }

@[simp]
instance : ContainsEdge V (G.Cycle v) where
  contains_edge P := ContainsEdge.contains_edge P.val

theorem Walk.IsCycle.reverse {G : SimpleGraph V} {p : G.Walk v v} (h : p.IsCycle) : p.reverse.IsCycle where
  edges_nodup := by rw[edges_reverse, List.nodup_reverse]; exact h.edges_nodup
  ne_nil := SimpleGraph.Walk.reverse_ne_nil h.ne_nil
  support_nodup := by
    suffices List.Perm p.support.tail p.reverse.support.tail from
      (List.Perm.nodup_iff this).mp h.support_nodup

    suffices List.Perm p.support p.reverse.support by
      rwa[support_eq_cons p, support_eq_cons p.reverse, List.perm_cons] at this

    exact Walk.support_reverse _ ▸ (List.reverse_perm p.support).symm

lemma Walk.IsCycle.IsCirculation {p : G.Walk v v} (hp : p.IsCycle) : p.IsCirculation where
  ne_nil := hp.ne_nil
  support_nodup := hp.support_nodup

lemma Walk.IsCycle.not_nil {p : G.Walk v v} (hc : p.IsCycle) : ¬p.Nil := hc.IsCirculation.not_nil

namespace Cycle

def toCirculation (c : G.Cycle v₀) : G.Circulation v₀ where
  val := c.val
  property := c.prop.IsCirculation

def reverse {G : SimpleGraph V} (c : G.Cycle v) : G.Cycle v where
  val := c.val.reverse
  property := c.prop.reverse

def rotate [DecidableEq V] {G : SimpleGraph V} (c : G.Cycle v) {u : V} (hu : u ∈ c.val.support) : G.Cycle u where
  val := c.val.rotate hu
  property := c.prop.rotate hu

@[simp]
lemma reverse_contains_edge {G : SimpleGraph V} {P : G.Cycle s} (h : contains_edge P u v) : contains_edge P.reverse v u := by
  obtain ⟨h', h''⟩ := h
  use h'.symm
  sorry

theorem succ_exists (c : G.Cycle v₀) {u : V} (hu : u ∈ c.val.support) :
    ∃!v, contains_edge c u v := c.toCirculation.succ_exists hu

abbrev snd (c : G.Cycle v₀) := c.val.sndOfNotNil c.prop.not_nil

lemma snd_is_succ_start (c : G.Cycle v₀) : contains_edge c v₀ c.snd := sorry

theorem snd_eq_succ_start (c : G.Cycle u) (h : contains_edge c u v) : c.snd = v :=
  (c.succ_exists c.val.start_mem_support).unique c.snd_is_succ_start h

theorem edges_eq_firstEdge_cons {G : SimpleGraph V} (c : G.Cycle v₀) :
    c.val.edges = ⟦(v₀, c.val.sndOfNotNil c.prop.not_nil)⟧ :: (c.val.tail c.prop.not_nil).edges := sorry

theorem contains_edge_rotate (c : G.Cycle v₀) {v₀' : V} (hv₀' : v₀' ∈ c.val.support) (h : contains_edge c u v) :
    contains_edge (c.rotate hv₀') u v := sorry

end Cycle
end SimpleGraph
