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

instance : ContainsEdge V (G.Circulation v₀) where
  contains_edge c := contains_edge c.val

theorem Path.cons_isCirculation (p : G.Path v u) (h : G.Adj u v) :
    (Walk.cons h p.val).IsCirculation where
  ne_nil := by simp only [ne_eq, not_false_eq_true]
  support_nodup := by
    rw[Walk.support_cons, List.tail_cons]
    exact p.prop.support_nodup

lemma Walk.IsCirculation.not_nil {p : G.Walk v v} (hc : p.IsCirculation) : ¬p.Nil := p.not_nil_of_ne_nil hc.ne_nil

namespace Circulation

lemma pred_exists {c : G.Circulation s} (hc: v ∈ c.val.support) :
    ∃! u, contains_edge c u v := by
  sorry

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

end Circulation
end SimpleGraph
