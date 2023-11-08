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

def flowIn (f : V → V → ℤ) (v : V) := ∑ u, (f u v).toNat
def flowOut (f : V → V → ℤ) (v : V) := ∑ u, (f v u).toNat

@[ext]
structure Flow (P : FlowProblem G) where
  f : V → V → ℤ
  skewSymmetry : ∀ {u v}, f u v = -f v u
  conservation : ∀ v, v ≠ P.s ∧ v ≠ P.t → flowOut f v = flowIn f v
  capacity : ∀ {u v}, f u v ≤ G.cap u v

def FlowProblem.nullFlow (P : FlowProblem G) : Flow P where
  f _ _ := 0
  skewSymmetry := by simp
  conservation := by aesop
  capacity := by simp

instance { P : FlowProblem G } : Inhabited (Flow P) where
  default := P.nullFlow

def Flow.value { P : FlowProblem G } (flow : Flow P) := flowOut flow.f P.s

def Flow.isMaximal { P : FlowProblem G } (F : Flow P) := ∀ F' : Flow P, F'.value ≤ F.value

lemma FlowProblem.maxFlowBound (P: FlowProblem G): ∀f: Flow P, f.value ≤ G.capMax := sorry

@[simp]
lemma Flow.le_capMax {P : FlowProblem G} (F : Flow P) (u v : V) : F.f u v ≤ ↑G.capMax := by
  apply le_trans
  exact F.capacity
  rw [Nat.cast_le]
  exact G.capMax_max

noncomputable section

instance { P : FlowProblem G } : Fintype (Flow P) := by
  let c := G.capMax
  let β := V → V → Fin (2 * c + 1)
  let inj : Flow P → β := fun F u v => (F.f u v + c).toNat
  apply Fintype.ofInjective inj

  intro F₁ F₂ h
  ext u v
  suffices F₁.f u v + c = F₂.f u v + c by simp_all only [add_left_inj]

  have : ∀ F : Flow P, ∀ u v, 0 ≤ F.f u v + c := by
    intro F u v
    apply le_trans
    simp only [Int.le_def, sub_zero]
    have : Int.NonNeg (Flow.f F u v + G.cap v u) := by
      rw [F.skewSymmetry]
      rw [add_comm, ←Int.sub_neg, ←Int.le_def, neg_neg]
      exact F.capacity
    exact this
    simp only [add_le_add_iff_left, Nat.cast_le]
    apply G.capMax_max

  have toNat_eq : ∀ F : Flow P, ∀ u v, F.f u v + c = (F.f u v + c).toNat := fun F u v ↦ Eq.symm (Int.toNat_of_nonneg (this F u v))

  rw [toNat_eq F₁ u v, toNat_eq F₂ u v]
  have h_F : ∀ F : Flow P, ↑(Int.toNat (Flow.f F u v + ↑c)) = Int.ofNat ((inj F) u v).val := by
    intro F
    simp only [Fin.coe_ofNat_eq_mod, Int.ofNat_eq_coe, Int.ofNat_emod, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one]
    rw [eq_comm, ←Int.mod_eq_emod]
    apply Int.mod_eq_of_lt
    simp
    apply @lt_of_le_of_lt _ _ _ (Flow.f F u v + ↑(Network.capMax G)) _

    have : ↑(Int.toNat (Flow.f F u v + ↑(Network.capMax G))) = Flow.f F u v + ↑(Network.capMax G) := by
      exact Int.toNat_of_nonneg (this F u v)
    rw [this]

    apply Int.lt_add_one_of_le
    have h_two_times : @Nat.cast ℤ NonAssocSemiring.toNatCast 2 * ↑(Network.capMax G) = ↑(Network.capMax G) + ↑(Network.capMax G) := by
      simp
      exact two_mul (↑(Network.capMax G) : ℤ)
    rw [h_two_times]
    simp only [add_le_add_iff_right, Flow.le_capMax]
    simp only [Nat.cast_nonneg]
    nlinarith
  rw [h_F F₁, h_F F₂, h]

def FlowProblem.maxFlow (P : FlowProblem G) : ℕ :=
  let values := Finset.image Flow.value $ @Finset.univ (Flow P) inferInstance
  let values_Nonempty : Finset.Nonempty values := Finset.Nonempty.image Finset.univ_nonempty Flow.value
  values.max' values_Nonempty

lemma FlowProblem.maxFlow_exists { P : FlowProblem G } : ∃ F : Flow P, F.value = P.maxFlow := sorry

def Network.maxFlowValue (G : Network V) (u v : V) := { s := u, t := v : FlowProblem G}.maxFlow

instance {G : UndirectedNetwork V} {P : FlowProblem G.toNetwork} : Neg (Flow P) :=
  ⟨fun f => ⟨-f.f, by
    intro u v
    simp only [Pi.neg_apply, neg_neg]
    rw [f.skewSymmetry]
    simp only [neg_neg]
  , by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    have : ∀ x, Int.toNat (-Flow.f f v x) = Int.toNat (Flow.f f x v) := by
      intro x
      rw [f.skewSymmetry]
      simp only [neg_neg]
    simp only [this]
    have : ∀ x, Int.toNat (-Flow.f f x v) = Int.toNat (Flow.f f v x) := by
      intro x
      rw [f.skewSymmetry]
      simp only [neg_neg]
    simp only [this]
    have := f.conservation v h_v_ne_st
    simp [flowOut, flowIn] at this
    simp_all only [ne_eq]
  , by
    intro u v
    simp
    rw [f.skewSymmetry]
    simp
    rw [G.symm]
    exact f.capacity
  ⟩⟩

instance {P : FlowProblem G} : HasSubset (Flow P) := ⟨fun f g => ∀ {u v : V}, 0 < f.f u v → f.f u v ≤ g.f u v⟩

instance {P : FlowProblem G} : LE (Flow P) := ⟨fun f g => f.value ≤ g.value⟩

@[simp]
lemma flow_le_neg {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, F₁.f u v < 0 → F₁.f u v ≥ F₂.f u v := by
  intro u v h_uv
  have h_vu : F₁.f v u > 0 := by
    rw [F₁.skewSymmetry] at h_uv
    simp at h_uv
    simp_all only [gt_iff_lt]
  have := h_le h_vu
  rw [F₁.skewSymmetry, F₂.skewSymmetry] at this
  exact Int.le_of_neg_le_neg this

@[simp]
lemma flow_pos_of_le_pos {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, 0 < F₁.f u v →  0 < F₂.f u v := by
  intro u v h
  have := h_le h
  exact lt_of_lt_of_le h this

@[simp]
lemma flow_nonneg {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, 0 ≤ F₂.f u v  → 0 ≤ F₁.f u v  := by
  intro u v h
  by_contra h'
  simp at h'
  have := flow_le_neg h_le h'
  simp at this
  have := le_trans h this
  have := lt_of_le_of_lt this h'
  simp only at this

def Flow.sub {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : Flow P where
  f := F₂.f - F₁.f
  skewSymmetry := by
    intro u v
    simp
    rw [F₁.skewSymmetry, F₂.skewSymmetry]
    rw [sub_neg_eq_add, add_comm]
    exact rfl
  conservation := by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    have : ∑ x : V, Int.toNat (f F₂ v x - f F₁ v x) = ∑ x : V, Int.toNat (f F₂ v x) - ∑ x : V, Int.toNat (f F₁ v x) := by
      have : ∀ x : V, Int.toNat (F₂.f v x - F₁.f v x) = Int.toNat (F₂.f v x) - Int.toNat (F₁.f v x) := by
        sorry
      -- use flow_le_nonneg_iff
      simp only [this]
      simp [Finset.sum]

      -- rw [Multiset.sum_map_add]
      sorry
    rw [this]
    have : ∑ x : V, Int.toNat (f F₂ x v - f F₁ x v) = ∑ x : V, Int.toNat (f F₂ x v) - ∑ x : V, Int.toNat (f F₁ x v) := by
      -- use flow_le_nonneg_iff
      sorry
    rw [this]
    have h₁ := F₁.conservation v h_v_ne_st
    have h₂ := F₂.conservation v h_v_ne_st
    simp [flowOut, flowIn] at h₁ h₂
    rw [h₁, h₂]
  capacity := by
    intro u v
    by_cases F₁.f u v ≥ 0
    simp
    have : F₂.f u v = F₂.f u v + 0 := by simp only [add_zero]
    rw [this]
    apply add_le_add
    simp only [F₂.capacity]
    assumption
    simp at h
    have h_le := flow_le_neg h_le h
    simp only [Pi.sub_apply, ge_iff_le]
    simp at h_le
    calc
      f F₂ u v - f F₁ u v ≤ f F₁ u v - f F₁ u v := by simp_all only [ge_iff_le, gt_iff_lt, flow_le_neg, sub_self, tsub_le_iff_right, zero_add]
      _ = 0 := by simp only [sub_self, le_refl]
      _ ≤ ↑(Network.cap G u v) := by simp only [Nat.cast_nonneg]

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
  | SimpleGraph.Walk.nil => by simp_all only [ne_eq, not_true]
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

  let f u v : ℤ := if contains_edge u v then b else if contains_edge v u then -b else 0
  have skewSymmetry : ∀ {u v}, f u v = -f v u := by
    intro u v
    if huv : contains_edge u v then
      have : ¬contains_edge v u := edge_only_one_way u v huv
      have : f v u = -b := by simp_all only [not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ite_true, ite_eq_right_iff, IsEmpty.forall_iff, implies_true]
      simp only [*, ite_false, ite_true, neg_neg, edge_only_one_way]
    else if hvu : contains_edge v u then
      simp_all only [not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ite_true, ite_eq_right_iff, IsEmpty.forall_iff, implies_true]
    else
      have h1 : f u v = 0 := by simp only [ite_false, huv, hvu]
      have h2 : f v u = 0 := by simp only [ite_false, hvu, huv]
      simp only [*]
  have conservation : ∀ v, v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v := sorry
  have capacity : ∀ {u v}, f u v ≤ G.cap u v := sorry

  { f, skewSymmetry, conservation, capacity }

lemma Flow.fromPath.value_eq_bottleneck
    {G : UndirectedNetwork V}
    {Pr : FlowProblem G.toNetwork}
    (h : Pr.s ≠ Pr.t)
    (P : G.asSimpleGraph.Path Pr.s Pr.t) :
    (Flow.fromPath h P).value = G.bottleneck h P := sorry

lemma flow_to_self_zero {P : FlowProblem G} (F : Flow P) (v : V) : F.f v v = 0 := by
    have h : F.f v v = -F.f v v := F.skewSymmetry
    linarith

lemma null_flow_smallest {P : FlowProblem G} (F : Flow P) : P.nullFlow ⊆ F := by
    intro u v h
    simp [FlowProblem.nullFlow] at h
