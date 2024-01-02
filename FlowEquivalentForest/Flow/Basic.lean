import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

import FlowEquivalentForest.Network
import FlowEquivalentForest.Util
import FlowEquivalentForest.SimpleGraph.Path

open BigOperators

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

structure FlowProblem { V : Type* } (G : Network V) where
  s : V
  t : V

variable { G : Network V }

@[simp]
def flowIn (f : V → V → ℕ) (v : V) := ∑ u, f u v

@[simp]
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

@[simp]
def Flow.value { P : FlowProblem G } (flow : Flow P) := flowOut flow.f P.s - flowIn flow.f P.s

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
      apply fintype_sum_sub_distrib_of_sub_nonneg
      intro x
      exact h_le
    rw [this]
    have : ∑ x : V, (f F₂ x v - f F₁ x v) = ∑ x : V, f F₂ x v - ∑ x : V, f F₁ x v := by
      apply fintype_sum_sub_distrib_of_sub_nonneg
      intro x
      exact h_le
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

def Flow.edge (P : FlowProblem G) {u v : V} (h_cap : 0 < min (G.cap u v) (G.cap v u)) : Flow P where
  f a b := if a = u ∧ b = v ∨ a = v ∧ b = u then 1 else 0
  conservation := by
    intro w _
    simp [flowOut, flowIn]
    have : Finset.filter (fun x ↦ w = u ∧ x = v ∨ w = v ∧ x = u) Finset.univ = Finset.filter (fun x ↦ x = u ∧ w = v ∨ x = v ∧ w = u) Finset.univ := by
      simp [Finset.filter_or, Finset.filter_and]
      ext
      apply Iff.intro
      split
      split
      intro h
      simp at h ⊢
      exact h.symm
      intro h
      simp at h ⊢
      exact h
      split
      intro h
      simp at h ⊢
      exact h
      intro h
      simp at h ⊢
      split
      split
      intro h
      simp at h ⊢
      exact h.symm
      intro h
      simp at h ⊢
      exact h
      split
      intro h
      simp at h ⊢
      exact h
      intro h
      simp at h ⊢
    rw [this]
  capacity := by
    intro a b
    simp
    split
    have h : a = u ∧ b = v ∨ a = v ∧ b = u := by assumption
    rcases h with h' | h'
    rw [h'.1, h'.2]
    simp at h_cap
    exact h_cap.1
    rw [h'.1, h'.2]
    simp at h_cap
    exact h_cap.2
    simp_all only [ge_iff_le, lt_min_iff, zero_le]

lemma edge_flow_value_zero
    (P : FlowProblem G)
    {u v : V}
    (h_cap : 0 < min (G.cap u v) (G.cap v u)) :
    (Flow.edge P h_cap).value = 0 := by
  sorry

lemma maxFlow_eq_zero_from_not_Reachable
    (G : UndirectedNetwork V)
    {u v : V}
    (h : ¬G.asSimpleGraph.Reachable u v) :
  G.maxFlowValue u v = 0 := sorry

lemma flow_to_self_zero {P : FlowProblem G} (F : Flow P) (v : V) : F.f v v = 0 := by
  linarith [F.capacity v v, G.loopless v]

lemma null_flow_smallest {P : FlowProblem G} (F : Flow P) : P.nullFlow ⊆ F := by
  intro u v
  simp only [FlowProblem.nullFlow, zero_le]
