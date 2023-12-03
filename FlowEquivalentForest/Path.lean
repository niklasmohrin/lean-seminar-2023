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

-- Adds an edge to the front of a path.
@[simp]
def SimpleGraph.Adj.cons {G : SimpleGraph V} (h_Adj : G.Adj u v) (P : G.Path v w) (hu : u ∉ P.val.support) : G.Path u w where
  val := SimpleGraph.Walk.cons h_Adj P.val
  property := SimpleGraph.Walk.IsPath.cons P.property hu

/-
Induction on paths.

This theoerem can be used with the induction tactic. The advantage over using
this over just induction on walks is that you never to leave path-land and the
induction step is set up so that it is clear that you are in the cons-case.

The proof works by using the `cases` tactic which gives the additional
hypothesis about which pattern matched so that we can assemble the walk back
back into a path. We then recursively call this theorem to keep the induction
going. We need to prove to Lean again that this recursion terminates, this time
we even need to specify what function is decreasing in the recursion (see the
`termination_by` after the proof).
-/
theorem SimpleGraph.Path.ind.{u₁}
    {G : SimpleGraph V}
    {motive : (u : V) → (v : V) → G.Path u v → Sort u₁}
    {u v : V}
    (P : G.Path u v)
    (base : ∀ u P, motive u u P)
    (ind : ∀ u v w P, (h_Adj : G.Adj u v) → (hu : u ∉ P.val.support) → motive v w P → motive u w (h_Adj.cons P hu)) :
    motive u v P := by
  cases h_cons : P.val with
  | nil => exact base u P
  | @cons a b c h p' =>
    let P' : G.Path _ _ := { val := p', property := (by have := P.property; rw[h_cons] at this; exact Walk.IsPath.of_cons this) }
    have : P = { val := SimpleGraph.Walk.cons h P'.val, property := (by rw[←h_cons]; exact P.property) } := by ext; assumption
    rw[this]
    have : p'.length < P.val.length := by rw[h_cons]; exact Nat.lt.base (Walk.length p')
    have := SimpleGraph.Path.ind P' base ind
    exact ind u b v P' h (by
      by_contra hu
      have : List.Duplicate u P.val.support := by
        simp_all only [h_cons, Walk.support_cons, List.duplicate_cons_self_iff, Walk.length_cons, lt_add_iff_pos_right]
      exact this.not_nodup P.property.support_nodup
    ) this
termination_by SimpleGraph.Path.ind P _ _ => P.val.length

-- A path containing just a single edge.
@[simp]
def SimpleGraph.Adj.toPath {G : SimpleGraph V} (h : G.Adj u v) : G.Path u v where
  val := h.toWalk
  property := by aesop

open SimpleGraph

example
    {G : SimpleGraph V}
    (P : G.Path u v) :
    P.val.support.length = P.val.darts.length + 1 := by
  induction' P using SimpleGraph.Path.ind with u P u v w P h_Adj hu ih
  · rw[SimpleGraph.Path.loop_eq P]
    simp only [Path.nil_coe, Walk.support_nil, List.length_singleton, Walk.darts_nil, List.length_nil, zero_add]
  · rw[SimpleGraph.Adj.cons, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.darts_cons, List.length_cons, List.length_cons, ih]
