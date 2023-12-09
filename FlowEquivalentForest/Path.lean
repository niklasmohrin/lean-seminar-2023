import Mathlib.Tactic.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Logic.Basic

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : SimpleGraph V}

def contains_edge {G : SimpleGraph V} (P : G.Path s t) (u v : V) :=
  ∃ h : G.Adj u v, P.val.darts.contains $ SimpleGraph.Dart.mk (u, v) h

lemma pred_exists {P : G.Path s t} (hp : P.val.support.contains v) (hs : v ≠ s) :
    ∃! u, contains_edge P u v := sorry
lemma succ_exists {P : G.Path s t} (hp : P.val.support.contains v) (ht : v ≠ t) :
    ∃! w, contains_edge P v w := by
  by_contra
  let Pr : G.Path t s := P.reverse
  have hpr : Pr.val.support.contains v := by
    simp_all only [List.elem_iff, ne_eq, SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  let w' : V := Classical.choose (pred_exists hpr ht)
  have h' : contains_edge Pr w' v := by
    sorry
  have h'' : contains_edge P v w' := by
    sorry
  -- ...?
  sorry

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

@[ext]
structure SimpleGraph.NonemptyPath {V : Type*} (G : SimpleGraph V) (u v : V) where
  path : G.Path u v
  ne : u ≠ v

-- A path containing just a single edge.
@[simp]
def SimpleGraph.Adj.toPath {G : SimpleGraph V} (h : G.Adj u v) : G.Path u v where
  val := h.toWalk
  property := by aesop

@[simp]
def SimpleGraph.Adj.toNonemptyPath {G : SimpleGraph V} (h : G.Adj u v) : G.NonemptyPath u v where
  path := h.toPath
  ne := h.ne

def SimpleGraph.NonemptyPath.cons {G : SimpleGraph V} (h_Adj : G.Adj u v) (P : G.NonemptyPath v w) (hu : u ∉ P.path.val.support) : G.NonemptyPath u w where
  path := {
    val := SimpleGraph.Walk.cons h_Adj P.path.val,
    property := SimpleGraph.Walk.IsPath.cons P.path.property hu
  }
  ne := by aesop

-- Same as SimpleGraph.Path.ind, but for non-trivial paths (paths with at least one edge).
theorem SimpleGraph.NonemptyPath.ind.{u₁}
    {G : SimpleGraph V}
    {motive : (u : V) → (v : V) → G.NonemptyPath u v → Sort u₁}
    {u v : V}
    (P : G.NonemptyPath u v)
    (base : ∀ u v, (h_Adj : G.Adj u v) → motive u v h_Adj.toNonemptyPath)
    (ind : ∀ u v w P, (h_Adj : G.Adj u v) → (hu : u ∉ P.path.val.support) → v ≠ w → motive v w P → motive u w (SimpleGraph.NonemptyPath.cons h_Adj P hu)) :
    motive u v P := by
  cases h_cons : P.path.val with
  | nil => have := P.ne; contradiction
  | @cons _ b c h_Adj tail =>
    let tail_path : G.Path b v := {
      val := tail,
      property := by
        have := P.path.property
        rw[h_cons] at this
        exact SimpleGraph.Walk.IsPath.of_cons this
    }

    if hbv : b = v then
      subst hbv
      have : h_Adj.toNonemptyPath = P := by
        ext
        simp[h_cons]
        apply Eq.symm
        exact (SimpleGraph.Walk.isPath_iff_eq_nil tail).mp tail_path.property
      subst this
      apply base
    else
      let tail_nonemptypath : G.NonemptyPath b v := { path := tail_path, ne := hbv }
      have hu : u ∉ tail.support := by
        by_contra hu
        have : List.Duplicate u P.path.val.support := by aesop
        exact this.not_nodup P.path.property.support_nodup

      have : tail.length < P.path.val.length := by simp_all only [Walk.length_cons, lt_add_iff_pos_right]
      have ih := SimpleGraph.NonemptyPath.ind tail_nonemptypath base ind

      have : P = cons h_Adj tail_nonemptypath hu := by ext; simp[h_cons]; rfl
      rw[this]

      exact ind u b v tail_nonemptypath h_Adj hu hbv ih
termination_by SimpleGraph.NonemptyPath.ind P _ _ => P.path.val.length

open SimpleGraph

example
    {G : SimpleGraph V}
    (P : G.Path u v) :
    P.val.support.length = P.val.darts.length + 1 := by
  induction P using SimpleGraph.Path.ind with
  | base u P =>
    rw[SimpleGraph.Path.loop_eq P]
    simp only [Path.nil_coe, Walk.support_nil, List.length_singleton, Walk.darts_nil, List.length_nil, zero_add]
  | ind u v w P h_Adj hu ih =>
    rw[SimpleGraph.Adj.cons, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.darts_cons, List.length_cons, List.length_cons, ih]

example
    {G : SimpleGraph V}
    (P : G.NonemptyPath u v) :
    P.path.val.support.length = P.path.val.darts.length + 1 := by
  induction P using SimpleGraph.NonemptyPath.ind with
  | base u v h_Adj => simp
  | ind u v w P h_Adj hu hvw ih => simp
