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

lemma Walk.IsCycle.IsCirculation {p : G.Walk v v} (hp : p.IsCycle) : p.IsCirculation where
  ne_nil := hp.ne_nil
  support_nodup := hp.support_nodup

lemma Walk.IsCycle.not_nil {p : G.Walk v v} (hc : p.IsCycle) : ¬p.Nil := hc.IsCirculation.not_nil

theorem Walk.IsCycle.reverse {G : SimpleGraph V} {p : G.Walk v v} (h : p.IsCycle) : p.reverse.IsCycle where
  edges_nodup := by rw[edges_reverse, List.nodup_reverse]; exact h.edges_nodup
  ne_nil := h.IsCirculation.reverse.ne_nil
  support_nodup := h.IsCirculation.reverse.support_nodup


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

theorem succ_exists (c : G.Cycle v₀) {u : V} (hu : u ∈ c.val.support) :
    ∃!v, contains_edge c u v := c.toCirculation.succ_exists hu

abbrev snd (c : G.Cycle v₀) := c.val.sndOfNotNil c.prop.not_nil

lemma snd_is_succ_start (c : G.Cycle v₀) : contains_edge c v₀ c.snd := by
  use c.val.adj_sndOfNotNil c.prop.not_nil
  use c.val.firstDart_mem_darts c.prop.not_nil

theorem snd_eq_succ_start (c : G.Cycle u) (h : contains_edge c u v) : c.snd = v :=
  (c.succ_exists c.val.start_mem_support).unique c.snd_is_succ_start h

theorem edges_eq_firstEdge_cons {G : SimpleGraph V} (c : G.Cycle v₀) :
    c.val.edges = s(v₀, c.val.sndOfNotNil c.prop.not_nil) :: (c.val.tail c.prop.not_nil).edges := by
  obtain ⟨u', hadj, p', hp'⟩ := Walk.not_nil_iff.mp c.prop.not_nil
  simp only [hp', Walk.edges_cons, List.cons_eq_cons]
  constructor
  · rw[Sym2.eq_iff]
    exact Or.inl ⟨rfl, rfl⟩
  · aesop

theorem contains_edge_rotate (c : G.Cycle v₀) {v₀' : V} (hv₀' : v₀' ∈ c.val.support) (h : contains_edge c u v) :
    contains_edge (c.rotate hv₀') u v := by
  obtain ⟨hadj, hd⟩ := h
  use hadj
  have := c.val.rotate_darts hv₀'
  simp only [rotate, instContainsEdgeCycle, this.mem_iff]
  use hd

end Cycle
end SimpleGraph
