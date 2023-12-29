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

@[simp]
def UndirectedNetwork.bottleneck
    {G : UndirectedNetwork V}
    (P : G.asSimpleGraph.NonemptyPath s t) : ℕ
  := (P.path.val.darts.toFinset.image (λ e => G.cap e.fst e.snd)).min' (by
    apply (Finset.Nonempty.image_iff _).mpr
    exact Walk_darts_Nonempty_from_ne P.ne P.path.val
  )

lemma UndirectedNetwork.bottleneck.single_edge
    {G : UndirectedNetwork V}
    (h: G.asSimpleGraph.Adj u v) :
    G.bottleneck h.toNonemptyPath = G.cap u v := by
  simp_all only [bottleneck, SimpleGraph.Adj.toNonemptyPath, SimpleGraph.Adj.toPath, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, Finset.image_singleton, Finset.min'_singleton]

lemma UndirectedNetwork.bottleneck.cons
    {G : UndirectedNetwork V}
    (h_Adj : G.asSimpleGraph.Adj u v)
    (P : G.asSimpleGraph.NonemptyPath v w)
    (hu : u ∉ P.path.val.support) :
    G.bottleneck (SimpleGraph.NonemptyPath.cons h_Adj P hu) = min (G.cap u v) (G.bottleneck P) := by
  simp [SimpleGraph.NonemptyPath.cons.darts]
  rw[min_comm]
  apply Finset.min'_insert

@[simp]
lemma UndirectedNetwork.bottleneck.le_dart
    {G : UndirectedNetwork V}
    (P : G.asSimpleGraph.NonemptyPath s t)
    {d : G.asSimpleGraph.Dart}
    (hd : P.path.val.darts.contains d) :
    G.bottleneck  P ≤ G.cap d.toProd.fst d.toProd.snd := by sorry

def Flow.fromPath
    {G : UndirectedNetwork V}
    {Pr : FlowProblem G.toNetwork}
    (P : G.asSimpleGraph.NonemptyPath Pr.s Pr.t) :
    Flow Pr :=
  let contains_edge := contains_edge P.path
  have {u v} : Decidable (contains_edge u v) := Classical.dec _

  let b := G.bottleneck P
  let f u v : ℕ := if contains_edge u v then b else 0

  have contains_edge_from_nonzero {u v} (h : f u v ≠ 0) : contains_edge u v := by by_contra; simp_all only [contains_edge, List.elem_iff, UndirectedNetwork.bottleneck, ne_eq, not_exists, exists_false, ite_false, not_true_eq_false]

  have conservation v : v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v := by
    intro hv
    if hp : P.path.val.support.contains v then
      obtain ⟨u, hu_pred, hu_uniq⟩ := pred_exists hp hv.left
      obtain ⟨w, hw_succ, hw_uniq⟩ := succ_exists hp hv.right

      let us := Finset.filter (contains_edge · v) Finset.univ
      have us_singleton : us = {u} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu_pred⟩, fun x hx => hu_uniq x (Finset.mem_filter.mp hx).right⟩
      have sum_usc_zero : (∑ u' in usᶜ, f u' v) = 0 := by
        apply Finset.sum_eq_zero
        intro u' hu'
        by_contra hnonzero
        have : u' ∈ us := Finset.mem_filter.mpr ⟨Finset.mem_univ u', contains_edge_from_nonzero hnonzero⟩
        exact Finset.mem_compl.mp hu' this

      -- The same again, but the other way around
      let ws := Finset.filter (contains_edge v ·) Finset.univ
      have ws_singleton : ws = {w} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw_succ⟩, fun x hx => hw_uniq x (Finset.mem_filter.mp hx).right⟩
      have sum_wsc_zero : (∑ w' in wsᶜ, f v w') = 0 := by
        apply Finset.sum_eq_zero
        intro w' hw'
        by_contra hnonzero
        have : w' ∈ ws := Finset.mem_filter.mpr ⟨Finset.mem_univ w', contains_edge_from_nonzero hnonzero⟩
        exact Finset.mem_compl.mp hw' this

      calc
        flowOut f v = ∑ w', f v w'                                 := rfl
        _           = (∑ w' in ws, f v w') + (∑ w' in wsᶜ, f v w') := (Finset.sum_add_sum_compl ws _).symm
        _           = ∑ w' in ws, f v w'                           := add_right_eq_self.mpr sum_wsc_zero
        _           = f v w                                        := by rw[ws_singleton, Finset.sum_singleton]
        _           = b                                            := if_pos hw_succ
        _           = f u v                                        := (if_pos hu_pred).symm
        _           = ∑ u' in us, f u' v                           := by rw[us_singleton, Finset.sum_singleton]
        _           = (∑ u' in us, f u' v) + (∑ u' in usᶜ, f u' v) := (add_right_eq_self.mpr sum_usc_zero).symm
        _           = ∑ u', f u' v                                 := Finset.sum_add_sum_compl us _
        _           = flowIn f v                                   := rfl
    else
      have h_out u : f v u = 0 := by
        by_contra h_nonzero
        have ⟨h_Adj, h_dart⟩  := contains_edge_from_nonzero h_nonzero
        have : SimpleGraph.Dart.mk (v,u) h_Adj ∈ P.path.val.darts := List.mem_of_elem_eq_true h_dart
        have : v ∈ P.path.val.support := SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ this
        simp_all only [contains_edge, List.elem_iff, UndirectedNetwork.bottleneck, ne_eq, ite_eq_right_iff, forall_exists_index, not_forall, exists_prop, exists_and_right, and_imp, implies_true, forall_const,not_true_eq_false]
      have h_in u : f u v = 0 := by
        by_contra h_nonzero
        have ⟨h_Adj, h_dart⟩  := contains_edge_from_nonzero h_nonzero
        have : SimpleGraph.Dart.mk (u,v) h_Adj ∈ P.path.val.darts := List.mem_of_elem_eq_true h_dart
        have : v ∈ P.path.val.support := SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ this
        simp_all only [contains_edge, List.elem_iff, UndirectedNetwork.bottleneck, ne_eq, ite_eq_right_iff, forall_exists_index, not_forall, exists_prop, exists_and_right, and_imp, implies_true, forall_const,not_true_eq_false]
      calc
        flowOut f v = ∑ u : V, f v u := rfl
        _           = 0              := Finset.sum_eq_zero $ fun u _ => h_out u
        _           = ∑ u, f u v     := (Finset.sum_eq_zero $ fun u _ => h_in u).symm
        _           = flowIn f v     := rfl
  have capacity u v : f u v ≤ G.cap u v := by
    if he : contains_edge u v then
      calc
        f u v = b                := by simp only [he, ite_true]
        _     = G.bottleneck P := rfl
        _     ≤ G.cap u v        := UndirectedNetwork.bottleneck.le_dart P he.snd
    else
      have : f u v = 0 := by simp only [he, ite_false]
      linarith

  { f, conservation, capacity }

@[simp]
lemma Flow.fromPath.value_eq_bottleneck
    {G : UndirectedNetwork V}
    {Pr : FlowProblem G.toNetwork}
    (P : G.asSimpleGraph.NonemptyPath Pr.s Pr.t) :
    (Flow.fromPath P).value = G.bottleneck P := by
  let F := Flow.fromPath P
  let b := G.bottleneck P

  have h_in : flowIn F.f Pr.s = 0 := by
    simp only [flowIn, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
    intro u
    suffices ¬contains_edge P.path u Pr.s by simp_all only [fromPath, contains_edge, ite_false]
    exact no_pred_first P.path


  obtain ⟨v, hv⟩ := succ_exists (List.elem_iff.mpr (SimpleGraph.Walk.start_mem_support P.path.val)) P.ne
  have h_out_succ : F.f Pr.s v = b := by simp only [fromPath, hv.left, ite_true]
  have h_out : flowOut F.f Pr.s = b := by
    rw[←h_out_succ]
    apply Finset.sum_eq_single
    · intro v' _ hne
      suffices ¬contains_edge P.path Pr.s v' by simp only [fromPath, this, ite_false]
      by_contra h
      exact hne $ hv.right v' h
    · have := Finset.mem_univ v; intro; contradiction

  rw[Flow.value, h_in, h_out, Nat.sub_zero]

lemma flow_to_self_zero {P : FlowProblem G} (F : Flow P) (v : V) : F.f v v = 0 := by
  linarith [F.capacity v v, G.loopless v]

lemma null_flow_smallest {P : FlowProblem G} (F : Flow P) : P.nullFlow ⊆ F := by
  intro u v
  simp only [FlowProblem.nullFlow, zero_le]

theorem Acyclic_Path_maxflow_eq_bottleneck
    (G : UndirectedNetwork V)
    (hG : G.asSimpleGraph.IsAcyclic)
    (P : G.asSimpleGraph.NonemptyPath u v) :
    G.maxFlowValue u v = G.bottleneck P := sorry
