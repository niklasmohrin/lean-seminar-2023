import Mathlib.Combinatorics.SimpleGraph.Acyclic

import FlowEquivalentForest.Flow

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

noncomputable def Network.matrix (G : Network V) := G.maxFlowValue

def ZeroDiagonal (M : α → α → β) [Zero β] := ∀ a, M a a = 0

open SimpleGraph

def mkFlowEquivalentForest
    (M : V → V → ℕ)
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  UndirectedNetwork V := sorry

theorem isAcyclic
    (M : V → V → ℕ)
    (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  IsAcyclic (mkFlowEquivalentForest M hM).asSimpleGraph := sorry

theorem flowEquivalentTree (M : V → V → ℕ) (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  ∃ T : UndirectedNetwork V, M = T.matrix ∧ IsAcyclic T.asSimpleGraph :=
  sorry

theorem flowMatrixCharacterization (M : V → V → ℕ) :
  (∃ G : Network V, M = G.matrix) ↔ (ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) := sorry
