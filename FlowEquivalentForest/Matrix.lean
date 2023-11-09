import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Linarith

import FlowEquivalentForest.Flow

-- A function from all pairs of discinct α values to β.
def PairMatrix (α β : Type*) := {x y : α} → (hxy : x ≠ y) → β

-- Symmetry of a PairMatrix requires that the order of the input pair does not matter.
def PairMatrix.Symmetrical (M : PairMatrix α β) := ∀ x y, (h : x ≠ y) → M h = M h.symm

noncomputable section

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

-- Currently, there is no need to pass in `hst`, but it is needed to match the
-- definition of PairMatrix (and we might want to restrict FlowProblem later on
-- to assume s ≠ t)
def Network.matrix (G : Network V) (s t : V) (hst : s ≠ t) : ℕ := G.maxFlowValue s t

open SimpleGraph
open BigOperators

def PairMatrix.TriangleInequality (M : PairMatrix V ℕ) :=
  ∀ u v w, (huv : u ≠ v) → (hvw : v ≠ w) → (huw : u ≠ w) → min (M huv) (M hvw) ≤ M huw

def mkFlowEquivalentForest
    (M : PairMatrix V ℕ)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
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

  let edges_ne (F : Forest) (e : V × V) : e ∈ edges F → e.fst ≠ e.snd := sorry

  let edges_symm (F : Forest) : ∀ u v, (u, v) ∈ edges F → (v, u) ∈ edges F := sorry
  -- let edges_symm (F : Forest) : ∀ u v, (u, v) ∈ edges F ↔ (v, u) ∈ edges F := fun u v ↦
  --   { mp := edges_symm F u v, mpr := edges_symm F v u }

  let weight (F : Forest) := ∑ e in edges F, M (edges_ne F e sorry)
  let MaximalForest := { g : Forest // ∀ g', weight g' ≤ weight g }
  let MaximalForest_Nonempty : Nonempty MaximalForest := sorry
  let g : MaximalForest := Classical.choice MaximalForest_Nonempty

  let cap u v := if huv : (u, v) ∈ edges g then M (edges_ne g (u, v) huv) else 0
  let loopless : ∀ v, cap v v = 0 := by
    intro v
    have : (v, v) ∉ edges g := by
      by_contra h
      have : v ≠ v := edges_ne g _ h
      contradiction
    simp only [*, ne_eq, dite_false]
  let symm : ∀ {u v}, cap u v = cap v u := sorry

  { cap, loopless, symm }

theorem mkFlowEquivalentForest_IsAcyclic
    (M : PairMatrix V ℕ)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
    IsAcyclic (mkFlowEquivalentForest M hsymm htri).asSimpleGraph := sorry

theorem mkFlowEquivalentForest_hasMatrixM
    (M : PairMatrix V ℕ)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
    @M = (mkFlowEquivalentForest M hsymm htri).matrix := sorry

theorem flowEquivalentForest
    (M : PairMatrix V ℕ)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
    ∃ T : UndirectedNetwork V, @M = T.matrix ∧ IsAcyclic T.asSimpleGraph := by
  use mkFlowEquivalentForest M hsymm htri
  exact ⟨mkFlowEquivalentForest_hasMatrixM M hsymm htri, mkFlowEquivalentForest_IsAcyclic M hsymm htri⟩

theorem flowMatrixCharacterization (M : PairMatrix V ℕ) :
    (∃ G : Network V, @M = G.matrix) ↔ (M.Symmetrical ∧ M.TriangleInequality) := sorry
