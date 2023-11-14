import Mathlib.Algebra.BigOperators.Order
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Linarith

import FlowEquivalentForest.Flow
import FlowEquivalentForest.PairMatrix
import FlowEquivalentForest.Util

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
  -- All the "spanning trees" over the complete graph over V.
  -- We also cancel forest edges that would have 0 capacity in the end, because we can.
  let Forest := { g : SimpleGraph V // IsAcyclic g ∧ ∀ u v, (huv : u ≠ v) → M huv = 0 → ¬g.Adj u v }
  have Forest_Nonempty : Nonempty Forest := by
    simp only [nonempty_subtype]
    use emptyGraph V
    simp_all only [emptyGraph_eq_bot, isAcyclic_bot, bot_adj, not_false_eq_true, implies_true, forall_const, and_self]

  have Forest_Adj_DecidablePred {F : Forest} : DecidablePred (fun e : V × V => F.val.Adj e.fst e.snd) := Classical.decPred _

  let edges (F : Forest) : Finset (V × V) :=
    let pred e := F.val.Adj e.fst e.snd
    Finset.filter pred Finset.univ

  have edges_Adj {F : Forest} {e : V × V} : e ∈ edges F → F.val.Adj e.fst e.snd := fun he =>
    (Finset.mem_filter.mp he).right
  have edges_ne {F : Forest} {e : V × V} : e ∈ edges F → e.fst ≠ e.snd := by
    intro he
    by_contra heq
    apply SimpleGraph.irrefl F.val
    have := edges_Adj he
    rwa[heq] at this

  have edges_symm {F : Forest} : ∀ {u v}, (u, v) ∈ edges F → (v, u) ∈ edges F := by
    intro u v huv
    simp only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and]
    apply F.val.symm
    simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp]

  let weight (F : Forest) := ∑ e : edges F, M (edges_ne e.prop)

  let M_max := Classical.choose M.bounded
  have weight_bounded F : weight F ≤ Fintype.card V * Fintype.card V * M_max := by
    calc
      weight F = ∑ e : edges F, M (edges_ne e.prop)      := by rfl
      _        ≤ ∑ _e : edges F, M_max                   := by simp_all only [Finset.sum_le_sum, Classical.choose_spec M.bounded, ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp]
      _        = (edges F).card * M_max                  := by simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp, Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
      _        ≤ Fintype.card V * Fintype.card V * M_max := by
                                                              have : (edges F).card ≤ (@Finset.univ (V × V)).card := Finset.card_filter_le _ _
                                                              have : (edges F).card ≤ Fintype.card (V × V) := by apply this
                                                              have : (edges F).card ≤ Fintype.card V * Fintype.card V := by simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp, Fintype.card_prod]
                                                              exact Nat.mul_le_mul_right M_max this
  have weight_bounded' F : F ∈ Set.univ → weight F ≤ Fintype.card V * Fintype.card V * M_max := fun _ => weight_bounded F

  let g := Classical.choose $ max_from_Nonempty_bounded_wrt Set.univ (by simp only [ne_eq, Set.univ_nonempty]) weight weight_bounded'

  let cap u v := if huv : (u, v) ∈ edges g then M (edges_ne huv) else 0
  have loopless : ∀ v, cap v v = 0 := by
    intro v
    have : (v, v) ∉ edges g := by
      by_contra h
      have : v ≠ v := edges_ne h
      contradiction
    simp only [*, ne_eq, dite_false]
  have symm : ∀ {u v}, cap u v = cap v u := by
    intro u v
    if huv : (u, v) ∈ edges g then
      have huv_ne := edges_ne huv
      have hvu := edges_symm huv
      calc
        cap u v = M huv_ne      := dif_pos huv
        _       = M huv_ne.symm := by rw[hsymm]
        _       = cap v u       := Eq.symm $ dif_pos hvu
    else
      have hvu : (v, u) ∉ edges g := by
        by_contra h
        exact huv $ edges_symm h
      calc
        cap u v = 0       := dif_neg huv
        _       = cap v u := Eq.symm $ dif_neg hvu

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
