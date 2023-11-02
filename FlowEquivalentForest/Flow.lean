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

noncomputable section

instance { P : FlowProblem G } : Fintype (Flow P) := by
  let c := G.capMax
  let β := V → V → Fin (2 * c + 1)
  let inj : Flow P → β := fun F u v => (F.f u v + c).toNat
  apply Fintype.ofInjective inj


  intro F₁ F₂ h
  ext u v
  suffices F₁.f u v + c = F₂.f u v + c by simp_all only [add_left_inj]

  have : ∀ F : Flow P, ∀ u v, 0 ≤ F.f u v + c := sorry
  have toNat_eq : ∀ F : Flow P, ∀ u v, F.f u v + c = (F.f u v + c).toNat := fun F u v ↦ Eq.symm (Int.toNat_of_nonneg (this F u v))

  rw[toNat_eq F₁ u v, toNat_eq F₂ u v]
  sorry

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

def UndirectedNetwork.bottleNeck
    {G : UndirectedNetwork V}
    { s t : V }
    (P : G.asSimpleGraph.Path s t) : ℕ
  := sorry

lemma pathLowerBound
    (G : UndirectedNetwork V)
    (s t : V)
    (P : G.asSimpleGraph.Path s t) :
  G.bottleNeck P ≤ G.maxFlowValue s t := sorry