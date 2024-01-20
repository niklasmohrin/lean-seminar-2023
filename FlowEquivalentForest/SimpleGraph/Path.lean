import Mathlib.Tactic.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Logic.Basic

abbrev SimpleGraph.Cycle {G : SimpleGraph V} (v : V) := { p : G.Walk v v // p.IsCycle }

lemma SimpleGraph.Walk.reverse_ne_nil {G : SimpleGraph V} {p : G.Walk v v} (h : p ≠ nil) : p.reverse ≠ nil :=
  λ h_nil => h $ reverse_nil ▸ SimpleGraph.Walk.reverse_reverse p ▸ congrArg SimpleGraph.Walk.reverse h_nil

theorem SimpleGraph.Walk.IsCycle.reverse {G : SimpleGraph V} {p : G.Walk v v} (h : p.IsCycle) : p.reverse.IsCycle where
  edges_nodup := by rw[edges_reverse, List.nodup_reverse]; exact h.edges_nodup
  ne_nil := SimpleGraph.Walk.reverse_ne_nil h.ne_nil
  support_nodup := by
    suffices List.Perm p.support.tail p.reverse.support.tail from
      (List.Perm.nodup_iff this).mp h.support_nodup

    suffices List.Perm p.support p.reverse.support by
      rwa[support_eq_cons p, support_eq_cons p.reverse, List.perm_cons] at this

    exact Walk.support_reverse _ ▸ (List.reverse_perm p.support).symm

def SimpleGraph.Cycle.reverse {G : SimpleGraph V} (c : G.Cycle v) : G.Cycle v where
  val := c.val.reverse
  property := c.prop.reverse

def SimpleGraph.Cycle.rotate [DecidableEq V] {G : SimpleGraph V} (c : G.Cycle v) {u : V} (hu : u ∈ c.val.support) : G.Cycle u where
  val := c.val.rotate hu
  property := c.prop.rotate hu

class ContainsEdge (V : outParam Type*) (α : Type*) where
  contains_edge : α → V → V → Prop

@[simp]
instance {V : Type*} [DecidableEq V] {s t : V} {G : SimpleGraph V} : ContainsEdge V (G.Walk s t) where
  contains_edge P u v := ∃ h : G.Adj u v, (SimpleGraph.Dart.mk (u, v) h) ∈ P.darts

@[simp]
instance instPathContainsEdge {V : Type*} [DecidableEq V] {s t : V} {G : SimpleGraph V} : ContainsEdge V (G.Path s t) where
  contains_edge P := ContainsEdge.contains_edge P.val

@[simp]
instance {V : Type*} [DecidableEq V] {v : V} {G : SimpleGraph V} : ContainsEdge V (G.Cycle v) where
  contains_edge P := ContainsEdge.contains_edge P.val

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {G : SimpleGraph V}

open ContainsEdge

lemma SimpleGraph.Walk.mem_support_of_contains_edge_fst
    (p : G.Walk s t)
    (h : contains_edge p u v) :
    u ∈ p.support := by
  obtain ⟨hadj, hd⟩ := h
  exact p.dart_fst_mem_support_of_mem_darts hd

lemma Walk_length_nonzero_from_ne
    {G : SimpleGraph V}
    (h : u ≠ v)
    (P : G.Walk u v) :
    0 < P.length :=
  match P with
  | SimpleGraph.Walk.nil => by contradiction
  | SimpleGraph.Walk.cons _ _ => by simp_all only [ne_eq, SimpleGraph.Walk.length_cons, add_pos_iff, zero_lt_one, or_true]

lemma Walk_darts_Nonempty_from_ne
    {G : SimpleGraph V}
    (h : u ≠ v)
    (P : G.Walk u v) :
    P.darts.toFinset.Nonempty := by
  simp only [List.toFinset_nonempty_iff, ne_eq]
  apply List.ne_nil_of_length_pos
  simp_all only [ne_eq, SimpleGraph.Walk.length_darts, not_false_eq_true, Walk_length_nonzero_from_ne]

lemma SimpleGraph.Walk.firstDart_mem_darts (p : G.Walk s t) (hp : ¬p.Nil) : p.firstDart hp ∈ p.darts := sorry

@[simp]
lemma SimpleGraph.Path.reverse_reverse {G : SimpleGraph V} (P : G.Path s t) : P.reverse.reverse = P := by
  ext
  simp_all only [SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.reverse_reverse]


@[simp]
lemma Walk.reverse.contains_edge {G : SimpleGraph V} {P : G.Walk s t} (h : contains_edge P u v) : contains_edge P.reverse v u := by
  obtain ⟨h', h''⟩ := h
  use h'.symm
  simp_all only [List.elem_iff, SimpleGraph.Walk.darts_reverse, List.mem_reverse,
    List.mem_map, SimpleGraph.Dart.symm_involutive, Function.Involutive.exists_mem_and_apply_eq_iff,
    SimpleGraph.Dart.symm_mk, Prod.swap_prod_mk]

@[simp]
lemma Path.reverse.contains_edge {G : SimpleGraph V} {P : G.Path s t} (h : contains_edge P u v) : contains_edge P.reverse v u := by
  obtain ⟨h', h''⟩ := h
  use h'.symm

  -- should be trivial with Walk.reverse.contains_edge
  simp_all only [List.elem_iff, SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.darts_reverse, List.mem_reverse,
    List.mem_map, SimpleGraph.Dart.symm_involutive, Function.Involutive.exists_mem_and_apply_eq_iff,
    SimpleGraph.Dart.symm_mk, Prod.swap_prod_mk]

@[simp]
lemma Cycle.reverse.contains_edge {G : SimpleGraph V} {P : G.Cycle s} (h : contains_edge P u v) : contains_edge P.reverse v u := by
  obtain ⟨h', h''⟩ := h
  use h'.symm
  sorry


lemma SimpleGraph.Walk.mem_edges_of_mem_darts {p : G.Walk s t} {d : G.Dart} (hd : d ∈ p.darts) : d.edge ∈ p.edges := by
  simp only [SimpleGraph.Walk.edges, List.mem_map]
  use d

-- Like `Walk.transfer`, but for `Path`s.
@[simp]
def SimpleGraph.Path.transfer {G : SimpleGraph V} (p : G.Path u v) (H : SimpleGraph V) (h : ∀ e ∈ p.val.edges, e ∈ H.edgeSet) : H.Path u v where
  val := p.val.transfer H h
  property := p.prop.transfer h

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

lemma SimpleGraph.Walk.start_ne_snd_of_mem_darts_of_support_nodup :
    ∀ (p : G.Walk s t) {d : G.Dart}, d ∈ p.darts → p.support.Nodup → s ≠ d.snd
  | Walk.cons (v := v') h p', d, hd, hp, heq => by
    rw[darts_cons, List.mem_cons] at hd
    rw[support_cons, List.nodup_cons] at hp
    have := hd.resolve_right (by
      subst heq
      intro hmem
      exact hp.left $ p'.dart_snd_mem_support_of_mem_darts hmem
    )
    rw[this] at heq
    simp at heq
    rw[heq] at h
    exact G.loopless _ h

lemma SimpleGraph.Walk.pred_eq_of_support_nodup
    (p : G.Walk s t)
    (hp : p.support.Nodup)
    (hu : contains_edge p u v)
    (hu' : contains_edge p u' v) :
    u = u' := by
  match p with
  | Walk.nil => exact False.elim $ List.not_mem_nil _ $ darts_nil ▸ hu.2
  | Walk.cons' _ v' _ h_adj p' =>
    have ⟨hadj, hd⟩ := hu
    have ⟨hadj', hd'⟩ := hu'
    rw[darts_cons, List.mem_cons] at hd hd'
    rw[support_cons, List.nodup_cons] at hp

    if hs : s = u ∨ s = u' then
      wlog hs' : s = u generalizing u u'
      · exact Eq.symm $ this (u := u') (u' := u) hu' hu hadj' hd' hadj hd hs.symm (hs.resolve_left hs')
      clear hs hu hu'
      subst hs'
      have hd := hd.resolve_right (hp.left ∘ p'.dart_fst_mem_support_of_mem_darts)
      injection hd with foo
      injection foo with _ hvv'
      subst hvv'
      clear hd

      by_contra hsu'
      have hd' := hd'.resolve_left (by
        intro h
        injection h with foo
        injection foo with hu's
        exact hsu' hu's.symm
      )

      exact p'.start_ne_snd_of_mem_darts_of_support_nodup hd' hp.right rfl
    else
      rw[not_or] at hs
      obtain ⟨hsu, hsu'⟩ := hs
      have h1 := hd.resolve_left (by
        intro h
        injection h with foo
        injection foo with bar
        exact hsu bar.symm
      )
      have h2 := hd'.resolve_left (by
        intro h
        injection h with foo
        injection foo with bar
        exact hsu' bar.symm
      )
      exact p'.pred_eq_of_support_nodup hp.right ⟨hadj, h1⟩ ⟨hadj', h2⟩



lemma SimpleGraph.Path.pred_exists {P : G.Path s t} (hp : v ∈ P.val.support) (hs : v ≠ s) :
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
        exact Walk.pred_eq_of_support_nodup _ (Adj.cons h_Adj P hu).prop.support_nodup hy h
    · aesop

lemma SimpleGraph.Path.succ_exists {P : G.Path s t} (hp : v ∈ P.val.support) (ht : v ≠ t) :
    ∃! w, contains_edge P v w := by
  let Pr : G.Path t s := P.reverse
  have hpr : v ∈ Pr.val.support := by
    simp_all only [List.elem_iff, ne_eq, SimpleGraph.Path.reverse_coe, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  obtain ⟨w, hw⟩ := SimpleGraph.Path.pred_exists hpr ht
  use w
  constructor
  · exact P.reverse_reverse ▸ Path.reverse.contains_edge hw.left
  · intro y hy
    exact hw.right y (Path.reverse.contains_edge hy)

lemma SimpleGraph.Walk.not_nil_of_ne_nil (p : G.Walk v v) (hp : p ≠ nil) : ¬p.Nil :=
  match p with
  | Walk.nil => False.elim $ hp rfl
  | Walk.cons .. => Walk.not_nil_cons

lemma SimpleGraph.Walk.IsCycle.not_nil {p : G.Walk v v} (hc : p.IsCycle) : ¬p.Nil := p.not_nil_of_ne_nil hc.ne_nil

lemma SimpleGraph.Path.no_pred_first (p : G.Path s t) : ¬contains_edge p u s := by
  intro ⟨hadj, hd⟩
  exact p.val.start_ne_snd_of_mem_darts_of_support_nodup hd p.prop.support_nodup rfl

theorem SimpleGraph.Path.not_contains_edge_end_start (p : G.Path u v) :
    ¬contains_edge p.val v u := sorry

theorem SimpleGraph.Walk.mem_darts_of_mem_edges (p : G.Walk s t) (h : ⟦(u, v)⟧ ∈ p.edges) :
    let hadj := p.adj_of_mem_edges h
    Dart.mk (u, v) hadj ∈ p.darts ∨ Dart.mk (v, u) hadj.symm ∈ p.darts := by
  rw[edges, List.mem_map] at h
  unfold Dart.edge at h
  obtain ⟨d, hd₁, hd₂⟩ := h
  rw[Sym2.eq_iff] at hd₂
  cases hd₂ with
  | inl heq =>
    left
    obtain ⟨hu, hv⟩ := heq
    subst_vars
    use hd₁
  | inr heq =>
    right
    obtain ⟨hv, hu⟩ := heq
    subst_vars
    use hd₁

theorem SimpleGraph.Cycle.succ_exists (c : G.Cycle v₀) {u : V} (hu : u ∈ c.val.support) :
    ∃!v, contains_edge c u v := sorry

abbrev SimpleGraph.Cycle.snd (c : G.Cycle v₀) := c.val.sndOfNotNil c.prop.not_nil

lemma SimpleGraph.Cycle.snd_is_succ_start (c : G.Cycle v₀) : contains_edge c v₀ c.snd := sorry

theorem SimpleGraph.Cycle.snd_eq_succ_start (c : G.Cycle u) (h : contains_edge c u v) : c.snd = v :=
  (c.succ_exists c.val.start_mem_support).unique c.snd_is_succ_start h

theorem SimpleGraph.Cycle.edges_eq_firstEdge_cons {G : SimpleGraph V} (c : G.Cycle v₀) :
    c.val.edges = ⟦(v₀, c.val.sndOfNotNil c.prop.not_nil)⟧ :: (c.val.tail c.prop.not_nil).edges := sorry

theorem SimpleGraph.Cycle.contains_edge_rotate (c : G.Cycle v₀) {v₀' : V} (hv₀' : v₀' ∈ c.val.support) (h : contains_edge c u v) :
    contains_edge (c.rotate hv₀') u v := sorry
