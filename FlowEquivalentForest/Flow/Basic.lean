import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

import FlowEquivalentForest.Network
import FlowEquivalentForest.Util
import FlowEquivalentForest.SimpleGraph.Path

open BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

structure FlowProblem (N : Network V) where
  s : V
  t : V

variable {N : Network V}

@[simp]
def flowIn (f : V → V → ℕ) (v : V) := ∑ u, f u v

@[simp]
def flowOut (f : V → V → ℕ) (v : V) := ∑ w, f v w

@[ext]
structure Flow (Pr : FlowProblem N) where
  f : V → V → ℕ
  conservation : ∀ v, v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v
  capacity : ∀ u v, f u v ≤ N.cap u v

def FlowProblem.nullFlow (Pr : FlowProblem N) : Flow Pr where
  f _ _ := 0
  conservation := by aesop
  capacity := by simp

variable {Pr : FlowProblem N}

instance : Zero (Flow Pr) where
  zero := Pr.nullFlow

def Flow.Backward (F : Flow Pr) := flowOut F.f Pr.s < flowIn F.f Pr.s

@[simp]
def Flow.value (flow : Flow Pr) := flowOut flow.f Pr.s - flowIn flow.f Pr.s

def Flow.isMaximal (F : Flow Pr) := ∀ F' : Flow Pr, F'.value ≤ F.value

@[simp]
lemma Flow.le_capMax (F : Flow Pr) (u v : V) : F.f u v ≤ N.capMax := by
  apply le_trans
  exact F.capacity u v
  exact N.capMax_max

noncomputable section

instance : Fintype (Flow Pr) := by
  let c := N.capMax + 1
  let β := V → V → Fin c
  let inj : Flow Pr → β := fun F u v => ⟨F.f u v, Nat.lt_add_one_iff.mpr (F.le_capMax u v)⟩
  apply Fintype.ofInjective inj

  intro F₁ F₂ h
  ext u v
  suffices F₁.f u v = F₂.f u v by simp_all only [add_left_inj]

  have h_F : ∀ F : Flow Pr, Flow.f F u v = ((inj F) u v).val := by
    intro F
    simp only
  rw [h_F F₁, h_F F₂, h]


def FlowProblem.maxFlow (Pr : FlowProblem N) : ℕ :=
  let values := Finset.image Flow.value $ @Finset.univ (Flow Pr) inferInstance
  let values_Nonempty : Finset.Nonempty values := Finset.Nonempty.image Finset.univ_nonempty Flow.value
  values.max' values_Nonempty

lemma FlowProblem.maxFlow_exists : ∃ F : Flow Pr, F.value = Pr.maxFlow := by
  let values := Finset.image Flow.value $ @Finset.univ (Flow Pr) inferInstance

  have : Pr.maxFlow ∈ values := by
    apply Finset.max'_mem

  rename_i inst inst_1 inst_2
  simp_all only [Finset.mem_image, Finset.mem_univ, true_and]

def Network.maxFlowValue (N : Network V) (u v : V) := { s := u, t := v : FlowProblem N}.maxFlow

instance {N : UndirectedNetwork V} {Pr : FlowProblem N.toNetwork} : Neg (Flow Pr) :=
  ⟨fun F => ⟨fun u v => F.f v u, by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    exact (F.conservation v h_v_ne_st).symm
  , by
    intro u v
    simp
    rw [N.symm]
    exact F.capacity v u
  ⟩⟩

@[simp]
instance : HasSubset (Flow Pr) where
  Subset F₁ F₂ := F₁.f ≤ F₂.f

instance : IsPartialOrder (Flow Pr) (· ⊆ ·) where
  refl F := by simp only [instHasSubsetFlow, le_refl]
  trans F₁ F₂ F₃ h₁₂ h₂₃ := by simp_all only [instHasSubsetFlow, le_trans h₁₂ h₂₃]
  antisymm F₁ F₂ h₁₂ h₂₁ := by ext u v; exact le_antisymm (h₁₂ u v) (h₂₁ u v)

@[simp]
instance : HasSSubset (Flow Pr) where
  SSubset F₁ F₂ := F₁.f < F₂.f

instance : IsStrictOrder (Flow Pr) (· ⊂ ·) where
  irrefl F := by simp only [instHasSSubsetFlow, lt_self_iff_false, not_false_eq_true, forall_const]
  trans F₁ F₂ F₃ h₁₂ h₂₃ := by simp_all only [instHasSSubsetFlow, lt_trans h₁₂ h₂₃]

instance : IsNonstrictStrictOrder (Flow Pr) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left F₁ F₂ := by constructor <;> (intro h; simp_all only [instHasSSubsetFlow, instHasSubsetFlow]; exact h)

@[simp]
instance : LE (Flow Pr) where
  le F₁ F₂ := F₁.value ≤ F₂.value

@[simp]
lemma flow_pos_of_le_pos {F₁ F₂ : Flow Pr} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, 0 < F₁.f u v → 0 < F₂.f u v := by
  intro u v h
  exact lt_of_lt_of_le h (h_le ..)

def Flow.sub {F₁ F₂ : Flow Pr} (h_le : F₁ ⊆ F₂) : Flow Pr where
  f := F₂.f - F₁.f
  conservation := by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    have : ∑ x : V, (f F₂ v x - f F₁ v x) = ∑ x : V, f F₂ v x - ∑ x : V, f F₁ v x := by
      apply fintype_sum_sub_distrib_of_sub_nonneg
      intro x
      exact h_le ..
    rw [this]
    have : ∑ x : V, (f F₂ x v - f F₁ x v) = ∑ x : V, f F₂ x v - ∑ x : V, f F₁ x v := by
      apply fintype_sum_sub_distrib_of_sub_nonneg
      intro x
      exact h_le ..
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

-- This is the first time that we have a problem with flows possibly being backwards:
-- If
-- a) F₂ has value 2 along a path from s to t and value 1 along a path from t to s, and
-- b) F₁                                      has value 1 along a path from t to s,
-- then subtracting F₁ from F₂ yields a flow with value 3, but the formula here would suggest 2,
-- because in natural numbers, the value of F₁ is 0 (while it would be -1 in the integers).
theorem Flow.sub_value
    {F₁ F₂ : Flow Pr}
    (hle : F₁ ⊆ F₂)
    (hF₁ : ¬F₁.Backward) :
    (Flow.sub hle).value = F₂.value - F₁.value := by
  simp[value, sub]
  rw[fintype_sum_sub_distrib_of_sub_nonneg (hle Pr.s ·)]
  rw[fintype_sum_sub_distrib_of_sub_nonneg (hle · Pr.s)]
  rw[Nat.sub_sub, Nat.sub_sub]
  have hle_flowIn: ∑ u : V, f F₁ u Pr.s ≤ ∑ u : V, f F₂ u Pr.s := Finset.sum_le_sum (λ u _ => hle ..)
  rw[←Nat.add_sub_assoc hle_flowIn]
  rw[Nat.add_comm]
  unfold Backward flowIn flowOut at hF₁
  rw[←Nat.add_sub_assoc (le_of_not_lt hF₁)]

theorem Flow.sub_subset
    {F₁ F₂ : Flow Pr}
    (hle : F₁ ⊆ F₂):
    (Flow.sub hle) ⊆ F₂ := by
  intro u v
  simp only [sub, Pi.sub_apply, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]

lemma Flow.zero_of_sub_neutral
    {F₁ F₂ : Flow Pr}
    (hle : F₁ ⊆ F₂)
    (hsub : Flow.sub hle = F₂):
    F₁ = 0 := by
  simp only [sub, Flow.ext_iff] at hsub
  ext u v
  exact Nat.eq_zero_of_sub_eq_self_of_le (congrFun (congrFun hsub u) v) (hle u v)

theorem Flow.sub_ssubset_of_nonzero
    {F₁ F₂ : Flow Pr}
    (h : F₁ ⊆ F₂)
    (hF₁ : F₁ ≠ 0) :
    Flow.sub h ⊂ F₂ :=
  ssubset_of_subset_of_ne (Flow.sub_subset h) (hF₁ ∘ (Flow.zero_of_sub_neutral h ·))

lemma flow_to_self_zero (F : Flow Pr) (v : V) : F.f v v = 0 := by
  linarith [F.capacity v v, N.loopless v]

lemma null_flow_smallest (F : Flow Pr) : Pr.nullFlow ⊆ F := by
  intro u v
  simp only [FlowProblem.nullFlow, zero_le]

theorem Flow.sum_flowOut_eq_sum_flowIn (F : Flow Pr) :
    ∑ u, flowOut F.f u = ∑ v, flowIn F.f v := by
  unfold flowOut flowIn
  rw[←Finset.sum_product', ←Finset.sum_product']
  simp only [Finset.univ_product_univ]
  apply Fintype.sum_bijective Prod.swap Prod.swap_bijective
  intro t
  simp only [Prod.snd_swap, Prod.fst_swap]

theorem Flow.flowOut_st_eq_flowIn_st (F : Flow Pr) :
    flowOut F.f Pr.s + flowOut F.f Pr.t = flowIn F.f Pr.s + flowIn F.f Pr.t := by
  let st : Finset V := {Pr.s, Pr.t}
  have h : Disjoint st stᶜ := disjoint_compl_right
  have hsum := F.sum_flowOut_eq_sum_flowIn
  simp only [←st.union_compl, Finset.sum_union h] at hsum

  suffices ∑ u in stᶜ, flowOut F.f u = ∑ v in stᶜ, flowIn F.f v by
    rw[this] at hsum
    have := add_right_cancel hsum
    if hst : Pr.s = Pr.t then
      rw[hst] at this
      simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton] at this
      simp only [hst, this]
    else
      simp only [Finset.sum_pair hst] at this
      exact this
  apply Finset.sum_congr rfl
  intro v hv
  simp at hv
  exact F.conservation v hv

theorem Flow.excess_s_eq_neg_excess_t (F : Flow Pr) :
    flowOut F.f Pr.s - flowIn F.f Pr.s = flowIn F.f Pr.t - flowOut F.f Pr.t := by
  apply Nat.sub_eq_sub_of_add_eq_add
  have := F.flowOut_st_eq_flowIn_st
  conv at this => right; rw[Nat.add_comm]
  exact this

lemma Flow.value_eq_zero_of_s_eq_t (F : Flow Pr) (hPr : Pr.s = Pr.t) : F.value = 0 := by
  suffices flowOut F.f Pr.s = flowIn F.f Pr.s by rw[value, this, Nat.sub_self]

  exact Finset.eq_of_sum_eq_of_forall_other_eq
    F.sum_flowOut_eq_sum_flowIn
    (Finset.mem_univ _)
    (λ v _ hv => F.conservation v ⟨hv, (hPr ▸ hv)⟩)

def Flow.range_sum (F : Flow Pr) : ℕ := ∑ u, ∑ v, F.f u v

theorem Flow.range_sum_lt_of_ssubset {F₁ F₂ : Flow Pr} (h : F₁ ⊂ F₂) : F₁.range_sum < F₂.range_sum := by
  simp only [range_sum, ←Fintype.sum_prod_type']
  apply Fintype.sum_lt_sum
  simp only [instHasSSubsetFlow, Pi.lt_def] at *
  obtain ⟨h1, u, _, v, h₃⟩ := h
  constructor
  · intro ⟨a, b⟩
    exact h1 a b
  · use ⟨u, v⟩
