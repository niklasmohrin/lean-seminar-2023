import Mathlib.Tactic.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : SimpleGraph V}

def contains_edge {G : SimpleGraph V} (P : G.Path s t) (u v : V) :=
  ∃ h : G.Adj u v, P.val.darts.contains $ SimpleGraph.Dart.mk (u, v) h

lemma pred_exists {P : G.Path s t} (hp : P.val.support.contains v) (hs : v ≠ s) :
    ∃! u, contains_edge P u v := sorry
lemma succ_exists {P : G.Path s t} (hp : P.val.support.contains v) (ht : v ≠ t) :
    ∃! w, contains_edge P v w := sorry
