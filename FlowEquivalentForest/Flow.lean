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
  conservation : ∀ v, v ≠ s ∧ v ≠ t → flowOut f v = flowIn f u
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

lemma flowFromPath_exists
    {G : UndirectedNetwork V}
    {P₁ : FlowProblem G.toNetwork }
    (h : s ≠ t)
    (P : G.asSimpleGraph.Path s t) :
  ∃F: Flow P₁, G.bottleneck h P = F.value := by sorry
