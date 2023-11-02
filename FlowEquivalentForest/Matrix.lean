import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Linarith

import FlowEquivalentForest.Flow

noncomputable section

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

def Network.matrix (G : Network V) := G.maxFlowValue

def ZeroDiagonal (M : α → α → β) [Zero β] := ∀ a, M a a = 0

open SimpleGraph
open BigOperators

lemma flowMatrix_symm
    {M : V → V → ℕ}
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  ∀ u v, M u v = M v u := sorry

def mkFlowEquivalentForest
    (M : V → V → ℕ)
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  UndirectedNetwork V :=
  let Forest := { g : SimpleGraph V // IsAcyclic g }
  let Forest_Nonempty : Nonempty Forest := by
    simp only [nonempty_subtype]
    use emptyGraph V
    simp only [emptyGraph_eq_bot, isAcyclic_bot]
  let edges (F : Forest) : Finset (V × V) :=
    let pred e := F.val.Adj e.fst e.snd
    have : DecidablePred pred := Classical.decPred pred
    Finset.filter pred Finset.univ

  let edges_symm (F : Forest) : ∀ u v, (u, v) ∈ edges F → (v, u) ∈ edges F := sorry
  let edges_symm (F : Forest) : ∀ u v, (u, v) ∈ edges F ↔ (v, u) ∈ edges F := fun u v ↦
    { mp := edges_symm F u v, mpr := edges_symm F v u }

  let weight (F : Forest) := ∑ e in edges F, M e.fst e.snd
  let MaximalForest := { g : Forest // ∀ g', weight g' ≤ weight g }
  let MaximalForest_Nonempty : Nonempty MaximalForest := sorry
  let g : MaximalForest := Classical.choice MaximalForest_Nonempty

  let cap u v := if (u, v) ∈ edges g then M u v else 0
  let loopless : ∀ v, cap v v = 0 := by
    simp only [ite_eq_right_iff]
    intro v _
    exact hM.left v
  let symm : ∀ {u v}, cap u v = cap v u := by simp only [edges_symm, flowMatrix_symm hM, forall_const]

  { cap, loopless, symm }

theorem mkFlowEquivalentForest_IsAcyclic
    (M : V → V → ℕ)
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  IsAcyclic (mkFlowEquivalentForest M hM).asSimpleGraph := sorry

theorem mkFlowEquivalentForest_hasMatrixM
    (M : V → V → ℕ)
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  M = (mkFlowEquivalentForest M hM).matrix := sorry

theorem flowEquivalentForest
    (M : V → V → ℕ)
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  ∃ T : UndirectedNetwork V, M = T.matrix ∧ IsAcyclic T.asSimpleGraph := by
  use mkFlowEquivalentForest M hM
  exact ⟨mkFlowEquivalentForest_hasMatrixM M hM, mkFlowEquivalentForest_IsAcyclic M hM⟩

theorem flowMatrixCharacterization (M : V → V → ℕ) :
  (∃ G : Network V, M = G.matrix) ↔ (ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) := sorry
