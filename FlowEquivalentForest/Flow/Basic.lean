import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Order.Zorn
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

def flowIn (f : V → V → ℤ) (v : V) := ∑ u, f u v
def flowOut (f : V → V → ℤ) (v : V) := ∑ w, f v w

@[ext]
structure Flow (Pr : FlowProblem N) where
  f : V → V → ℤ
  nonneg : ∀ u v, 0 ≤ f u v
  conservation : ∀ v, v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v
  capacity : ∀ u v, f u v ≤ N.cap u v

def FlowProblem.nullFlow (Pr : FlowProblem N) : Flow Pr where
  f _ _ := 0
  nonneg := by simp
  conservation := by aesop
  capacity := by simp[N.nonneg]

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

lemma Flow.flowIn_nonneg (F : Flow Pr) (v : V) : 0 ≤ flowIn F.f v := Fintype.sum_nonneg (F.nonneg · v)
lemma Flow.flowOut_le_capMax (F : Flow Pr) (u : V) : flowOut F.f u ≤ Fintype.card V * N.capMax := by
  calc
    flowOut F.f u = ∑ v, F.f u v  := rfl
    _ ≤ ∑ _v : V, N.capMax        := by apply Finset.sum_le_sum; intro v _; exact F.le_capMax u v
    _ = Fintype.card V * N.capMax := Finset.sum_const ..

lemma Flow.value_le_capMax (F : Flow Pr) : F.value ≤ Fintype.card V * N.capMax := by
  calc
    F.value = flowOut F.f Pr.s - flowIn F.f Pr.s := rfl
    _       ≤ flowOut F.f Pr.s                   := by linarith[F.flowIn_nonneg Pr.s]
    _       ≤ Fintype.card V * N.capMax          := F.flowOut_le_capMax Pr.s

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
instance : Preorder (Flow Pr) := Preorder.lift Flow.value

instance : IsTotalPreorder (Flow Pr) (LE.le) where
  total F F' := by simp only [instPreorderFlow, Preorder.lift]; exact le_total ..

lemma increasing_seq_unbounded_wrt (w : α → ℤ) (succ : α → α) (h : ∀ a, w a < w (succ a)) (n : ℤ) (a : α) : ∃a', n ≤ w a' := by
  if ha : n ≤ w a then
    use a
  else
    have : (n - w (succ a)).toNat < (n - w a) := by
      apply Int.lt_toNat.mp
      refine (Int.toNat_lt_toNat ?_).mpr ?_
      · linarith[ha]
      · linarith[h a]
    exact increasing_seq_unbounded_wrt w succ h n (succ a)
termination_by (n - w a).toNat

theorem FlowProblem.exists_top (Pr : FlowProblem N) : ∃ F : Flow Pr, IsTop F := by
  by_contra h
  have h' (F : Flow Pr) : ∃ F' : Flow Pr, F < F' := by
    simp[IsTop] at h
    obtain ⟨F', hF'⟩ := h F
    use F'
    simp only [instPreorderFlow, Preorder.lift] at hF' ⊢
    linarith[hF']
  let succ F := Classical.choose (h' F)
  have hsucc F := Classical.choose_spec (h' F)
  obtain ⟨F, hF⟩ := increasing_seq_unbounded_wrt Flow.value succ hsucc (Fintype.card V * N.capMax + 1) 0
  linarith[hF, F.value_le_capMax]

noncomputable instance : OrderTop (Flow Pr) where
  top := Classical.choose Pr.exists_top
  le_top := Classical.choose_spec Pr.exists_top

noncomputable def FlowProblem.maxFlow (Pr : FlowProblem N) : ℤ := (⊤ : Flow Pr).value

noncomputable def Network.maxFlowValue (N : Network V) (u v : V) := { s := u, t := v : FlowProblem N}.maxFlow

@[simp]
lemma flow_pos_of_le_pos {F₁ F₂ : Flow Pr} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, 0 < F₁.f u v → 0 < F₂.f u v := by
  intro u v h
  exact lt_of_lt_of_le h (h_le ..)

def Flow.sub {F₁ F₂ : Flow Pr} (h_le : F₁ ⊆ F₂) : Flow Pr where
  f := F₂.f - F₁.f
  nonneg u v := by simp only [Pi.sub_apply, sub_nonneg, h_le u v]
  conservation v hv := by
    simp[flowOut, flowIn]
    rw[←flowOut, ←flowIn, ←flowOut, ←flowIn, F₁.conservation v hv, F₂.conservation v hv]
  capacity u v := by
    simp only [Pi.sub_apply, ge_iff_le, tsub_le_iff_right]
    have : F₂.f u v = F₂.f u v + 0 := by simp only [add_zero]
    rw [this]
    apply add_le_add
    simp [F₂.capacity]
    exact F₁.nonneg u v

-- This is the first time that we have a problem with flows possibly being backwards:
-- If
-- a) F₂ has value 2 along a path from s to t and value 1 along a path from t to s, and
-- b) F₁                                      has value 1 along a path from t to s,
-- then subtracting F₁ from F₂ yields a flow with value 3, but the formula here would suggest 2,
-- because in natural numbers, the value of F₁ is 0 (while it would be -1 in the integers).
theorem Flow.sub_value
    {F₁ F₂ : Flow Pr}
    (hle : F₁ ⊆ F₂) :
    (Flow.sub hle).value = F₂.value - F₁.value := by
  simp [value, sub, flowOut, flowIn]
  ring

theorem Flow.sub_subset
    {F₁ F₂ : Flow Pr}
    (hle : F₁ ⊆ F₂):
    (Flow.sub hle) ⊆ F₂ := by
  intro u v
  simp only [sub, Pi.sub_apply, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, nonneg]

lemma Flow.zero_of_sub_neutral
    {F₁ F₂ : Flow Pr}
    (hle : F₁ ⊆ F₂)
    (hsub : Flow.sub hle = F₂):
    F₁ = 0 := by
  simp only [sub, Flow.ext_iff] at hsub
  ext u v
  simp_all only [instHasSubsetFlow, sub_eq_self, Pi.zero_apply]
  apply Eq.refl

theorem Flow.sub_ssubset_of_nonzero
    {F₁ F₂ : Flow Pr}
    (h : F₁ ⊆ F₂)
    (hF₁ : F₁ ≠ 0) :
    Flow.sub h ⊂ F₂ :=
  ssubset_of_subset_of_ne (Flow.sub_subset h) (hF₁ ∘ (Flow.zero_of_sub_neutral h ·))

lemma null_flow_smallest (F : Flow Pr) : Pr.nullFlow ⊆ F := by
  intro u v
  simp only [FlowProblem.nullFlow, zero_le, F.nonneg]

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
      simp_all only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.disjoint_singleton_left, Finset.mem_compl, not_true_eq_false, not_false_eq_true, flowOut, Finset.sum_singleton, flowIn, add_left_inj, st]
    else
      simp only [Finset.sum_pair hst] at this
      exact this
  apply Finset.sum_congr rfl
  intro v hv
  rw[Finset.mem_compl, Finset.mem_insert, not_or, Finset.mem_singleton] at hv
  exact F.conservation v hv

theorem Flow.excess_s_eq_neg_excess_t (F : Flow Pr) :
    flowOut F.f Pr.s - flowIn F.f Pr.s = flowIn F.f Pr.t - flowOut F.f Pr.t := by linarith[F.flowOut_st_eq_flowIn_st]

lemma Flow.value_eq_zero_of_s_eq_t (F : Flow Pr) (hPr : Pr.s = Pr.t) : F.value = 0 := by
  suffices flowOut F.f Pr.s = flowIn F.f Pr.s by rw[value, this, sub_self]

  exact Finset.eq_of_sum_eq_of_forall_other_eq
    F.sum_flowOut_eq_sum_flowIn
    (Finset.mem_univ _)
    (λ v _ hv => F.conservation v ⟨hv, (hPr ▸ hv)⟩)

def Flow.range_sum (F : Flow Pr) : ℤ := ∑ u, ∑ v, F.f u v

theorem Flow.range_sum_lt_of_ssubset {F₁ F₂ : Flow Pr} (h : F₁ ⊂ F₂) : F₁.range_sum < F₂.range_sum := by
  simp only [range_sum, ←Fintype.sum_prod_type']
  apply Fintype.sum_lt_sum
  simp only [instHasSSubsetFlow, Pi.lt_def] at *
  obtain ⟨h1, u, _, v, h₃⟩ := h
  constructor
  · intro ⟨a, b⟩
    exact h1 a b
  · use ⟨u, v⟩
