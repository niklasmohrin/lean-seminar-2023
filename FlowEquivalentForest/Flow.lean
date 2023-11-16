import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

import FlowEquivalentForest.Network

open BigOperators

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

structure FlowProblem { V : Type* } (G : Network V) where
  s : V
  t : V

variable { G : Network V }

def flowIn (f : V → V → ℕ) (v : V) := ∑ u, f u v
def flowOut (f : V → V → ℕ) (v : V) := ∑ u, f v u

@[ext]
structure Flow (P : FlowProblem G) where
  f : V → V → ℕ
  conservation : ∀ v, v ≠ P.s ∧ v ≠ P.t → flowOut f v = flowIn f v
  capacity : ∀ u v, f u v ≤ G.cap u v

def FlowProblem.nullFlow (P : FlowProblem G) : Flow P where
  f _ _ := 0
  conservation := by aesop
  capacity := by simp

instance { P : FlowProblem G } : Inhabited (Flow P) where
  default := P.nullFlow

def Flow.value { P : FlowProblem G } (flow : Flow P) := flowOut flow.f P.s

def Flow.isMaximal { P : FlowProblem G } (F : Flow P) := ∀ F' : Flow P, F'.value ≤ F.value

@[simp]
lemma Flow.le_capMax {P : FlowProblem G} (F : Flow P) (u v : V) : F.f u v ≤ G.capMax := by
  apply le_trans
  exact F.capacity u v
  exact G.capMax_max

noncomputable section

instance { P : FlowProblem G } : Fintype (Flow P) := by
  let c := G.capMax + 1
  let β := V → V → Fin c
  let inj : Flow P → β := fun F u v => ⟨F.f u v, Nat.lt_add_one_iff.mpr (F.le_capMax u v)⟩
  apply Fintype.ofInjective inj

  intro F₁ F₂ h
  ext u v
  suffices F₁.f u v = F₂.f u v by simp_all only [add_left_inj]

  have h_F : ∀ F : Flow P, Flow.f F u v = ((inj F) u v).val := by
    intro F
    simp only
  rw [h_F F₁, h_F F₂, h]


def FlowProblem.maxFlow (P : FlowProblem G) : ℕ :=
  let values := Finset.image Flow.value $ @Finset.univ (Flow P) inferInstance
  let values_Nonempty : Finset.Nonempty values := Finset.Nonempty.image Finset.univ_nonempty Flow.value
  values.max' values_Nonempty

lemma FlowProblem.maxFlow_exists { P : FlowProblem G } : ∃ F : Flow P, F.value = P.maxFlow := by
  let values := Finset.image Flow.value $ @Finset.univ (Flow P) inferInstance

  have : P.maxFlow ∈ values := by
    apply Finset.max'_mem

  rename_i inst inst_1 inst_2
  simp_all only [Finset.mem_image, Finset.mem_univ, true_and]

def Network.maxFlowValue (G : Network V) (u v : V) := { s := u, t := v : FlowProblem G}.maxFlow

instance {G : UndirectedNetwork V} {P : FlowProblem G.toNetwork} : Neg (Flow P) :=
  ⟨fun F => ⟨fun u v => F.f v u, by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    exact (F.conservation v h_v_ne_st).symm
  , by
    intro u v
    simp
    rw [G.symm]
    exact F.capacity v u
  ⟩⟩

instance {P : FlowProblem G} : HasSubset (Flow P) := ⟨fun F₁ F₂ => ∀ {u v : V}, F₁.f u v ≤ F₂.f u v⟩

instance {P : FlowProblem G} : LE (Flow P) := ⟨fun f g => f.value ≤ g.value⟩

@[simp]
lemma flow_pos_of_le_pos {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, 0 < F₁.f u v → 0 < F₂.f u v := by
  intro u v h
  exact lt_of_lt_of_le h h_le

def Flow.sub {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : Flow P where
  f := F₂.f - F₁.f
  conservation := by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    have : ∑ x : V, (f F₂ v x - f F₁ v x) = ∑ x : V, f F₂ v x - ∑ x : V, f F₁ v x := by
      sorry
    rw [this]
    have : ∑ x : V, (f F₂ x v - f F₁ x v) = ∑ x : V, f F₂ x v - ∑ x : V, f F₁ x v := by
      -- use flow_le_nonneg_iff
      sorry
    rw [this]
    have h₁ := F₁.conservation v h_v_ne_st
    have h₂ := F₂.conservation v h_v_ne_st
    simp [flowOut, flowIn] at h₁ h₂
    rw [h₁, h₂]
  capacity := by
    intro u v
    simp only [Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    have : F₂.f u v = F₂.f u v + 0 := by simp only [add_zero]
    rw [this]
    apply add_le_add
    simp [F₂.capacity]
    simp only [zero_le]

lemma disconnected_zero
    (G : UndirectedNetwork V)
    (s t : V)
    (h : ¬G.asSimpleGraph.Reachable s t) :
    G.maxFlowValue s t = 0 := sorry

lemma Walk_length_nonzero_from_ne
    {G : SimpleGraph V}
    (h : u ≠ v)
    (P : G.Walk u v) :
    0 < P.length :=
  match P with
  | SimpleGraph.Walk.nil => by contradiction
  | SimpleGraph.Walk.cons _ _ => by simp only [SimpleGraph.Walk.length_cons, add_pos_iff, or_true]

lemma Walk_darts_Nonempty_from_ne
    {G : SimpleGraph V}
    (h : u ≠ v)
    (P : G.Walk u v) :
    P.darts.toFinset.Nonempty := by
  simp only [List.toFinset_nonempty_iff, ne_eq]
  apply List.ne_nil_of_length_pos
  simp_all only [ne_eq, SimpleGraph.Walk.length_darts, not_false_eq_true, Walk_length_nonzero_from_ne]

def UndirectedNetwork.bottleneck
    {G : UndirectedNetwork V}
    (h : s ≠ t)
    (P : G.asSimpleGraph.Path s t) : ℕ
  := (P.val.darts.toFinset.image (λ e => G.cap e.fst e.snd)).min' (by
    apply (Finset.Nonempty.image_iff _).mpr
    exact Walk_darts_Nonempty_from_ne h P.val
  )

lemma UndirectedNetwork.bottleneck.le_dart
    {G : UndirectedNetwork V}
    (h : s ≠ t)
    (P : G.asSimpleGraph.Path s t)
    (d : SimpleGraph.Dart _)
    (hd : P.val.darts.contains d) :
    G.bottleneck h P ≤ G.cap s t := by sorry


def Flow.fromPath
    {G : UndirectedNetwork V}
    {Pr : FlowProblem G.toNetwork}
    (h : Pr.s ≠ Pr.t)
    (P : G.asSimpleGraph.Path Pr.s Pr.t) :
    Flow Pr :=
  let b := G.bottleneck h P

  let sup := P.val.support
  let contains_edge u v := ∃ i : Fin (sup.length - 1),
    sup.get (i.castLE (Nat.sub_le _ _)) = u
    ∧ sup.get (i.succ.cast (by simp only [SimpleGraph.Walk.length_support, ge_iff_le, add_le_iff_nonpos_left,
      nonpos_iff_eq_zero, add_tsub_cancel_right])) = v

  have no_loop_edge : ∀ v, ¬contains_edge v v := by
    intro v hv
    obtain ⟨i, hi⟩ := hv
    have dup : List.Duplicate v sup := by
      apply List.duplicate_iff_exists_distinct_get.mpr
      let n : Fin (sup.length) := i.castLE (Nat.sub_le _ _)
      let m : Fin (sup.length) := i.succ.cast (by simp only [SimpleGraph.Walk.length_support, ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right])
      use n
      use m
      have : n < m := by
        apply Fin.mk_lt_mk.mpr
        simp only [Fin.val_succ, lt_add_iff_pos_right]
      use this
      simp only [and_self, hi]

    exact List.Duplicate.not_nodup dup $ SimpleGraph.Path.nodup_support P

  have edge_only_one_way : ∀ u v, contains_edge u v → ¬contains_edge v u := by
    intro u v h

    if huv : u = v then
      rw[huv]
      exact no_loop_edge v
    else
      intro h'
      obtain ⟨i, hi⟩ := h
      obtain ⟨i', hi'⟩ := h'
      have hne : i ≠ i' := by
        by_contra heq
        rw[heq] at hi
        simp_all only [not_exists, not_and, and_false]
      wlog hlt : i < i' generalizing i i' u v with hgt
      · have : i' ≤ i := Fin.not_lt.mp (hgt u v huv i hi i' hi' hne)
        have : i' < i := Ne.lt_of_le (Ne.symm hne) this
        exact hgt v u (Iff.mp ne_comm huv) i' hi' i hi (Ne.symm hne) this

      have dup : List.Duplicate u sup := by
        apply List.duplicate_iff_exists_distinct_get.mpr
        let n : Fin (sup.length) := i.castLE (Nat.sub_le _ _)
        let m : Fin (sup.length) := i'.succ.cast (by simp only [SimpleGraph.Walk.length_support, ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right])
        use n
        use m
        have : n < m := by
          apply Fin.mk_lt_mk.mpr
          exact Nat.lt.step hlt
        use this
        simp only [and_self, hi, hi']
      exact List.Duplicate.not_nodup dup $ SimpleGraph.Path.nodup_support P

  let f u v : ℕ := if contains_edge u v then b else 0

  have conservation : ∀ v, v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v := sorry
  have capacity : ∀ u v, f u v ≤ G.cap u v := by
    intro u v
    if he : contains_edge u v then
      have hfb : f u v = b := by simp only [he, ite_true]
      rw [hfb]
      simp
      sorry
      -- apply UndirectedNetwork.bottleneck.le_dart
    else
      have : f u v = 0 := by simp only [he, ite_false]
      linarith

  { f, conservation, capacity }

lemma Flow.fromPath.value_eq_bottleneck
    {G : UndirectedNetwork V}
    {Pr : FlowProblem G.toNetwork}
    (h : Pr.s ≠ Pr.t)
    (P : G.asSimpleGraph.Path Pr.s Pr.t) :
    (Flow.fromPath h P).value = G.bottleneck h P := sorry

lemma flow_to_self_zero {P : FlowProblem G} (F : Flow P) (v : V) : F.f v v = 0 := by
  linarith [F.capacity v v, G.loopless v]

lemma null_flow_smallest {P : FlowProblem G} (F : Flow P) : P.nullFlow ⊆ F := by
  intro u v
  simp only [FlowProblem.nullFlow, zero_le]
