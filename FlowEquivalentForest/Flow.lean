import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

import FlowEquivalentForest.Network
import FlowEquivalentForest.Util

import Paperproof

open BigOperators

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

-- A flow problem is defined on a network and has a source and sink vertex
structure FlowProblem { V : Type* } (G : Network V) where
  s : V
  t : V

variable { G : Network V }

-- The flowIn and flowOut of a vertex is the sum of all flow entering or leaving the vertex, respectively
def flowIn (f : V → V → ℕ) (v : V) := ∑ u, f u v
def flowOut (f : V → V → ℕ) (v : V) := ∑ u, f v u

-- A Flow is a function of edges to natural numbers on a flow problem satisfying flow conservation of each vertex and the capacity contraint of all edges
@[ext]
structure Flow (P : FlowProblem G) where
  f : V → V → ℕ
  conservation : ∀ v, v ≠ P.s ∧ v ≠ P.t → flowOut f v = flowIn f v
  capacity : ∀ u v, f u v ≤ G.cap u v

def FlowProblem.nullFlow (P : FlowProblem G) : Flow P where
  f _ _ := 0
  conservation := by aesop
  capacity := by simp

-- Every FlowProblem has at least one valid flow: the null Flow
instance { P : FlowProblem G } : Inhabited (Flow P) where
  default := P.nullFlow

-- The flow value is the sum of all flow leaving s
def Flow.value { P : FlowProblem G } (flow : Flow P) := flowOut flow.f P.s

-- A maximal Flow is a Flow with maximal value
def Flow.isMaximal { P : FlowProblem G } (F : Flow P) := ∀ F' : Flow P, F'.value ≤ F.value

-- The flow value on each edge is bound by the maximal capacity
@[simp]
lemma Flow.le_capMax {P : FlowProblem G} (F : Flow P) (u v : V) : F.f u v ≤ G.capMax := by
  apply le_trans
  exact F.capacity u v
  exact G.capMax_max

noncomputable section

-- On a given flow prblem there exists a finite set of possible flows, but we are not sure what the proof does
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

-- A MaxFlow is the maximal flow value possible
def FlowProblem.maxFlow (P : FlowProblem G) : ℕ :=
  let values := Finset.image Flow.value $ @Finset.univ (Flow P) inferInstance
  let values_Nonempty : Finset.Nonempty values := Finset.Nonempty.image Finset.univ_nonempty Flow.value
  values.max' values_Nonempty

-- There exists a Flow with the maximal flow value
lemma FlowProblem.maxFlow_exists { P : FlowProblem G } : ∃ F : Flow P, F.value = P.maxFlow := by
  let values := Finset.image Flow.value $ @Finset.univ (Flow P) inferInstance

  have : P.maxFlow ∈ values := by
    apply Finset.max'_mem

  rename_i inst inst_1 inst_2
  simp_all only [Finset.mem_image, Finset.mem_univ, true_and]

-- Return the maximal flow value of a network with source u and sink v
def Network.maxFlowValue (G : Network V) (u v : V) := { s := u, t := v : FlowProblem G}.maxFlow

-- To negate a flow we just let everything flow in the opposite direction
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

-- A subset of a Flow sends less or the same amount of flow over all edges
instance {P : FlowProblem G} : HasSubset (Flow P) := ⟨fun F₁ F₂ => ∀ {u v : V}, F₁.f u v ≤ F₂.f u v⟩

-- The ≤-relation between flows is induced by the ≤-realtion over their values
instance {P : FlowProblem G} : LE (Flow P) := ⟨fun f g => f.value ≤ g.value⟩

-- if F₁ ⊆ F₂ then every edge of F₁ with a positive flow value also has a positive flow value in F₂
@[simp]
lemma flow_pos_of_le_pos {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : ∀ {u v : V}, 0 < F₁.f u v → 0 < F₂.f u v := by
  intro u v h
  exact lt_of_lt_of_le h h_le

-- We can substract two flow and obtain a valid flow
def Flow.sub {P : FlowProblem G} {F₁ F₂ : Flow P} (h_le : F₁ ⊆ F₂) : Flow P where
  f := F₂.f - F₁.f
  conservation := by
    intro v h_v_ne_st
    simp [flowOut, flowIn]
    have : ∑ x : V, (f F₂ v x - f F₁ v x) = ∑ x : V, f F₂ v x - ∑ x : V, f F₁ v x := by
      apply finset_sum_sub_distrib_of_sub_nonneg
      intro x
      exact h_le
    rw [this]
    have : ∑ x : V, (f F₂ x v - f F₁ x v) = ∑ x : V, f F₂ x v - ∑ x : V, f F₁ x v := by
      apply finset_sum_sub_distrib_of_sub_nonneg
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

theorem Flow.sub_value_eq_sub {P : FlowProblem G} {F₁ F₂ : Flow P} (h_sub : F₁ ⊆ F₂) : value (Flow.sub h_sub) = F₂.value - F₁.value := by
  simp [value, flowOut, sub]
  apply finset_sum_sub_distrib_of_sub_nonneg
  intro x
  exact h_sub

-- We define a Flow of one flowing between two vertices
def Flow.edge (P : FlowProblem G) {u v : V} (h_cap : 0 < min (G.cap u v) (G.cap v u)) : Flow P where
  f a b := if a = u ∧ b = v ∨ a = v ∧ b = u then 1 else 0
  conservation := by
    intro w _
    simp [flowOut, flowIn]
    have : Finset.filter (fun x ↦ w = u ∧ x = v ∨ w = v ∧ x = u) Finset.univ = Finset.filter (fun x ↦ x = u ∧ w = v ∨ x = v ∧ w = u) Finset.univ := by
      simp [Finset.filter_or, Finset.filter_and]
      ext
      aesop
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

-- The edge flow has a flow value of 0
lemma edge_flow_value_zero (P : FlowProblem G) {u v : V} (h_cap : 0 < min (G.cap u v) (G.cap v u)) : (Flow.edge P h_cap).value = 0 := by
  sorry

-- A flow network where s and t are disconnected has a MaxFlow of 0
lemma disconnected_zero
    (G : UndirectedNetwork V)
    (s t : V)
    (h : ¬G.asSimpleGraph.Reachable s t) :
    G.maxFlowValue s t = 0 := sorry

-- A walk between two different vertices has a length larger than zero
lemma Walk_length_nonzero_from_ne
    {G : SimpleGraph V}
    (h : u ≠ v)
    (P : G.Walk u v) :
    0 < P.length :=
  match P with
  | SimpleGraph.Walk.nil => by contradiction
  | SimpleGraph.Walk.cons _ _ => by simp only [SimpleGraph.Walk.length_cons, add_pos_iff, or_true]

-- A walk between two different vertices uses at least one edge
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

-- The bottleneck of a Network is less than or equal to all edge weights
@[simp]
lemma UndirectedNetwork.bottleneck.le_dart
    {G : UndirectedNetwork V}
    (h : s ≠ t)
    (P : G.asSimpleGraph.Path s t)
    {d : G.asSimpleGraph.Dart}
    (hd : P.val.darts.contains d) :
    G.bottleneck h P ≤ G.cap d.toProd.fst d.toProd.snd := by sorry

def Flow.fromPath
    {G : UndirectedNetwork V}
    {Pr : FlowProblem G.toNetwork}
    (h : Pr.s ≠ Pr.t)
    (P : G.asSimpleGraph.Path Pr.s Pr.t) :
    Flow Pr :=
  let contains_edge u v := ∃ h : G.asSimpleGraph.Adj u v, P.val.darts.contains $ SimpleGraph.Dart.mk (u, v) h
  have {u v} : Decidable (contains_edge u v) := Classical.dec _

  -- (Maybe not needed): Except for the ends of the path, every vertex has a predecessor iff it has a successor
  -- have pred_iff_succ {v : V} (hinner : v ≠ Pr.s ∧ v ≠ Pr.t) : (∃ u, contains_edge u v) ↔ (∃ w, contains_edge v w) := by sorry

  have pred_exists {v : V} (hp : P.val.support.contains v) (hs : v ≠ Pr.s) : ∃! u, contains_edge u v := sorry
  have succ_exists {v : V} (hp : P.val.support.contains v) (ht : v ≠ Pr.t) : ∃! w, contains_edge v w := sorry

  let b := G.bottleneck h P
  let f u v : ℕ := if contains_edge u v then b else 0

  have contains_edge_from_nonzero {u v} (h : f u v ≠ 0) : contains_edge u v := sorry

  have conservation v : v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v := by
    intro hv
    if hp : P.val.support.contains v then
      obtain ⟨u, hu_pred, hu_uniq⟩ := pred_exists hp hv.left
      obtain ⟨w, hw_succ, hw_uniq⟩ := succ_exists hp hv.right

      have other_in {u'} (h : u' ≠ u) : f u' v = 0 := by
        by_contra hne
        exact h (hu_uniq u' (contains_edge_from_nonzero hne))
      let us := Finset.filter (contains_edge · v) Finset.univ
      have us_singleton : us = {u} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu_pred⟩, fun x hx => hu_uniq x (Finset.mem_filter.mp hx).right⟩
      have sum_usc_zero : (∑ u' in usᶜ, f u' v) = 0 := by
        apply Finset.sum_eq_zero
        intro u' hu'
        by_contra hnonzero
        have : u' ∈ us := Finset.mem_filter.mpr ⟨Finset.mem_univ u', contains_edge_from_nonzero hnonzero⟩
        exact Finset.mem_compl.mp hu' this

      -- The same again, but the other way around
      have other_out {w'} (h : w' ≠ w) : f v w' = 0 := by
        by_contra hne
        exact h (hw_uniq w' (contains_edge_from_nonzero hne))
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
      have h_out u : f v u = 0 := sorry
      have h_in u : f u v = 0 := sorry
      calc
        flowOut f v = ∑ u : V, f v u := rfl
        _           = 0              := Finset.sum_eq_zero $ fun u _ => h_out u
        _           = ∑ u, f u v     := (Finset.sum_eq_zero $ fun u _ => h_in u).symm
        _           = flowIn f v     := rfl
  have capacity u v : f u v ≤ G.cap u v := by
    if he : contains_edge u v then
      calc
        f u v = b                := by simp only [he, ite_true]
        _     = G.bottleneck h P := rfl
        _     ≤ G.cap u v        := UndirectedNetwork.bottleneck.le_dart h P he.snd
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

-- The null flow is a subset of every other flow on a FlowProblem
lemma null_flow_smallest {P : FlowProblem G} (F : Flow P) : P.nullFlow ⊆ F := by
  intro u v
  simp only [FlowProblem.nullFlow, zero_le]
