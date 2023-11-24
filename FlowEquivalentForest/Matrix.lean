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

section
namespace mkFlowEquivalentForest

-- All the "spanning trees" over the complete graph over V.
-- We also cancel forest edges that would have 0 capacity in the end, because we can.
abbrev Forest (M : PairMatrix V ℕ) := { g : SimpleGraph V // IsAcyclic g ∧ ∀ u v, (huv : u ≠ v) → M huv = 0 → ¬g.Adj u v }

instance {M : PairMatrix V ℕ} : Nonempty (Forest M) := by
  simp only [nonempty_subtype]
  use emptyGraph V
  simp_all only [emptyGraph_eq_bot, isAcyclic_bot, bot_adj, not_false_eq_true, implies_true, forall_const, and_self]

namespace Forest
  variable {M : PairMatrix V ℕ} 

  instance Forest_Adj_DecidablePred {F : Forest M} : DecidablePred (fun e : V × V => F.val.Adj e.fst e.snd) := Classical.decPred _

  abbrev edges (F : Forest M) : Finset (V × V) :=
    let pred e := F.val.Adj e.fst e.snd
    Finset.filter pred Finset.univ

  lemma edges_Adj {F : Forest M} (he : e ∈ F.edges) : F.val.Adj e.fst e.snd :=
    (Finset.mem_filter.mp he).right

  lemma edges_ne {F : Forest M} (he : e ∈ F.edges) : e.fst ≠ e.snd := by
    by_contra heq
    apply SimpleGraph.irrefl F.val
    have := edges_Adj he
    rwa[heq] at this

  lemma edges_symm {F : Forest M} (huv : (u, v) ∈ F.edges) : (v, u) ∈ F.edges := by
    have := F.val.symm $ edges_Adj huv
    simp_all only [Finset.mem_filter, Finset.mem_univ, ne_eq, true_and, and_self]
end Forest

variable (M : PairMatrix V ℕ)

def mkFrom
    (hsymm : M.Symmetrical) :
    UndirectedNetwork V :=
  let Forest := Forest M

  let weight (F : Forest) := ∑ e : F.edges, M (F.edges_ne e.prop)

  let M_max := Classical.choose M.bounded
  have weight_bounded F : weight F ≤ Fintype.card V * Fintype.card V * M_max := by
    calc
      weight F = ∑ e : F.edges, M (F.edges_ne e.prop)    := by rfl
      _        ≤ ∑ _e : F.edges, M_max                   := by simp_all only [Finset.sum_le_sum, Classical.choose_spec M.bounded, ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp]
      _        = (F.edges).card * M_max                  := by simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp, Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
      _        ≤ Fintype.card V * Fintype.card V * M_max := by
                                                              have : (F.edges).card ≤ (@Finset.univ (V × V)).card := Finset.card_filter_le _ _
                                                              have : (F.edges).card ≤ Fintype.card (V × V) := by apply this
                                                              have : (F.edges).card ≤ Fintype.card V * Fintype.card V := by simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp, Fintype.card_prod]
                                                              exact Nat.mul_le_mul_right M_max this
  have weight_bounded' F : F ∈ Set.univ → weight F ≤ Fintype.card V * Fintype.card V * M_max := fun _ => weight_bounded F

  let g := Classical.choose $ max_from_Nonempty_bounded_wrt Set.univ (by simp only [ne_eq, Set.univ_nonempty]) weight weight_bounded'

  let cap u v := if huv : (u, v) ∈ g.edges then M (g.edges_ne huv) else 0
  have loopless : ∀ v, cap v v = 0 := by
    intro v
    have : (v, v) ∉ g.edges := by
      by_contra h
      have : v ≠ v := g.edges_ne h
      contradiction
    simp only [*, ne_eq, dite_false]
  have symm : ∀ u v, cap u v = cap v u := by
    intro u v
    if huv : (u, v) ∈ g.edges then
      have huv_ne := g.edges_ne huv
      have hvu := g.edges_symm huv
      calc
        cap u v = M huv_ne      := dif_pos huv
        _       = M huv_ne.symm := by rw[hsymm]
        _       = cap v u       := Eq.symm $ dif_pos hvu
    else
      have hvu : (v, u) ∉ g.edges := by
        by_contra h
        exact huv $ g.edges_symm h
      calc
        cap u v = 0       := dif_neg huv
        _       = cap v u := Eq.symm $ dif_neg hvu

  { cap, loopless, symm }

theorem mkFrom_IsAcyclic
    (hsymm : M.Symmetrical) :
    IsAcyclic (mkFrom M hsymm).asSimpleGraph := sorry

theorem mkFrom_hasMatrixM
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
    @M = (mkFrom M hsymm).matrix := sorry

end mkFlowEquivalentForest
end

theorem flowEquivalentForest
    (M : PairMatrix V ℕ)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
    ∃ T : UndirectedNetwork V, @M = T.matrix ∧ IsAcyclic T.asSimpleGraph := ⟨
    mkFlowEquivalentForest.mkFrom M hsymm,
    mkFlowEquivalentForest.mkFrom_hasMatrixM M hsymm htri,
    mkFlowEquivalentForest.mkFrom_IsAcyclic M hsymm
  ⟩

theorem flowMatrixCharacterization (M : PairMatrix V ℕ) :
    (∃ G : UndirectedNetwork V, @M = G.matrix) ↔ (M.Symmetrical ∧ M.TriangleInequality) := sorry
