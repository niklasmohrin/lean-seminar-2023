import Mathlib.Tactic.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Logic.Basic

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : SimpleGraph V}

@[simp]
def contains_edge {G : SimpleGraph V} (P : G.Path s t) (u v : V) :=
  ∃ h : G.Adj u v, P.val.darts.contains $ SimpleGraph.Dart.mk (u, v) h

@[simp]
lemma SimpleGraph.Path.reverse_reverse {G : SimpleGraph V} (P : G.Path s t) : P.reverse.reverse = P := by
  ext
  simp_all only [SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.reverse_reverse]


@[simp]
lemma contains_edge.mem_reverse {G : SimpleGraph V} {P : G.Path s t} (h : contains_edge P u v) : contains_edge P.reverse v u := by
  obtain ⟨h', h''⟩ := h
  use h'.symm
  simp_all only [List.elem_iff, SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.darts_reverse, List.mem_reverse,
    List.mem_map, SimpleGraph.Dart.symm_involutive, Function.Involutive.exists_mem_and_apply_eq_iff,
    SimpleGraph.Dart.symm_mk, Prod.swap_prod_mk]

lemma SimpleGraph.Walk.mem_edges_of_mem_darts {p : G.Walk s t} {d : G.Dart} (hd : d ∈ p.darts) : d.edge ∈ p.edges := by
  simp only [SimpleGraph.Walk.edges, List.mem_map]
  use d

-- Adds an edge to the front of a path.
@[simp]
def SimpleGraph.Adj.cons {G : SimpleGraph V} (h_Adj : G.Adj u v) (P : G.Path v w) (hu : u ∉ P.val.support) : G.Path u w where
  val := SimpleGraph.Walk.cons h_Adj P.val
  property := SimpleGraph.Walk.IsPath.cons P.property hu

lemma SimpleGraph.Path.cons.darts {G : SimpleGraph V} (h_Adj : G.Adj u v) (P : G.Path v w) (hu : u ∉ P.val.support) : (h_Adj.cons P hu).val.darts = Dart.mk (u,v) h_Adj :: P.val.darts := rfl 

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

lemma SimpleGraph.NonemptyPath.cons.darts {G : SimpleGraph V} (h_Adj : G.Adj u v) (P : G.NonemptyPath v w) (hu : u ∉ P.path.val.support) : (SimpleGraph.NonemptyPath.cons h_Adj P hu).path.val.darts = Dart.mk (u,v) h_Adj :: P.path.val.darts := rfl

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

      have : tail.length < P.path.val.length := by simp_all only [Walk.length_cons, lt_add_iff_pos_right, zero_lt_one]
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



lemma SimpleGraph.Path.no_two_incoming {G : SimpleGraph V} (P : G.Path s t) (a1 : contains_edge P a c) (a2 : contains_edge P b c) : a = b := by
  induction P using SimpleGraph.Path.ind with
  | base u P => aesop -- Path u u contradicts hs and hp
  | ind u v' w P h_Adj hu ih =>
    simp_all
    by_cases hv : v' = c
    · simp_all [hv]
      sorry
    · aesop

lemma pred_exists {P : G.Path s t} (hp : P.val.support.contains v) (hs : v ≠ s) :
    ∃! u, contains_edge P u v := by
  induction P using SimpleGraph.Path.ind with
  | base u P => aesop -- Path u u contradicts hs and hp
  | ind u v' w P h_Adj hu ih =>
    by_cases hv : v = v'
    · use u
      constructor
      · aesop
      · intro y hy
        have h : contains_edge (Adj.cons h_Adj P hu) u v := by aesop
        exact SimpleGraph.Path.no_two_incoming (Adj.cons h_Adj P hu) hy h
    · aesop



lemma succ_exists {P : G.Path s t} (hp : P.val.support.contains v) (ht : v ≠ t) :
    ∃! w, contains_edge P v w := by
  let Pr : G.Path t s := P.reverse
  have hpr : Pr.val.support.contains v := by
    simp_all only [List.elem_iff, ne_eq, SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  obtain ⟨w, hw⟩ := pred_exists hpr ht
  use w
  constructor
  · exact P.reverse_reverse ▸ contains_edge.mem_reverse hw.left
  · intro y hy
    exact hw.right y (contains_edge.mem_reverse hy)

lemma no_pred_first (P : G.Path s t) : ¬contains_edge P u s := by
  have h0 : P.val.support.indexOf s = 0 := by
    unfold Walk.support
    aesop

  by_contra h
  obtain ⟨_, h_dart⟩ := h
  suffices P.val.support.indexOf u < P.val.support.indexOf s by simp_all only [not_lt_zero']

  sorry
