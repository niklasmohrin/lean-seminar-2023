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

namespace Circulation

lemma pred_exists {c : G.Circulation s} (hc: v ∈ c.val.support) :
    ∃! u, contains_edge c u v := by
  sorry

lemma succ_exists {c : G.Circulation s} (hc: u ∈ c.val.support) :
    ∃! v, contains_edge c u v := by
  sorry

end Circulation
end SimpleGraph
