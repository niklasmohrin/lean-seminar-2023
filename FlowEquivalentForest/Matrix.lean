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
abbrev Forest (M : PairMatrix V ℕ) := { g : SimpleGraph V // IsAcyclic g ∧ ∀ u v, (huv : u ≠ v) → g.Adj u v → 0 < M huv }

instance {M : PairMatrix V ℕ} : Nonempty (Forest M) := by
  simp only [nonempty_subtype]
  use emptyGraph V
  simp_all only [emptyGraph_eq_bot, isAcyclic_bot, bot_adj, IsEmpty.forall_iff, implies_true, forall_const, and_self]

namespace Forest
  variable {V : Type*} [Fintype V] {M : PairMatrix V ℕ} 

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

  def weight (F : Forest M) := ∑ e : F.edges, M (F.edges_ne e.prop)

  lemma weight_bounded (M : PairMatrix V ℕ) : (∃ b, ∀ F : Forest M, F.weight ≤ b) := by
    let M_max := Classical.choose M.bounded
    use Fintype.card V * Fintype.card V * M_max
    intro F
    calc
      F.weight = ∑ e : F.edges, M (F.edges_ne e.prop)    := by rfl
      _        ≤ ∑ _e : F.edges, M_max                   := by simp_all only [Finset.sum_le_sum, Classical.choose_spec M.bounded, ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp]
      _        = (F.edges).card * M_max                  := by simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp, Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
      _        ≤ Fintype.card V * Fintype.card V * M_max := by
                                                              have : (F.edges).card ≤ (@Finset.univ (V × V)).card := Finset.card_filter_le _ _
                                                              have : (F.edges).card ≤ Fintype.card (V × V) := by apply this
                                                              have : (F.edges).card ≤ Fintype.card V * Fintype.card V := by simp_all only [ne_eq, Finset.filter_congr_decidable, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter, true_and, implies_true, forall_const, Subtype.forall, and_imp, Fintype.card_prod]
                                                              exact Nat.mul_le_mul_right M_max this

  def add_edge (g : Forest M) {u v : V} (huv : u ≠ v) (h_non_Adj : ¬g.val.Adj u v) : Forest M := sorry

  lemma add_edge.weight_eq_add
      (g : Forest M)
      {u v : V}
      (huv : u ≠ v)
      (h_non_Adj : ¬g.val.Adj u v) :
      (g.add_edge huv h_non_Adj).weight = g.weight + M huv := sorry
end Forest

abbrev MaximalForest (M : PairMatrix V ℕ) := {F : Forest M // ∀ F' : Forest M, F'.weight ≤ F.weight}

instance {M : PairMatrix V ℕ} : Nonempty (MaximalForest M) := by
  obtain ⟨b, hb⟩ := Forest.weight_bounded M
  obtain ⟨F : Forest M, hF⟩ := max_from_Nonempty_bounded_wrt (@Set.univ (Forest M)) (Set.univ_nonempty) Forest.weight (fun F _ => hb F)
  use F
  intro F'
  simp_all only [Set.mem_univ, forall_true_left, Subtype.forall, ne_eq, true_and]
  apply hF

variable (M : PairMatrix V ℕ)

def mkFrom (hsymm : M.Symmetrical) (g : Forest M) : UndirectedNetwork V :=
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

@[simp]
lemma mkFrom_cap_def
    (hsymm : M.Symmetrical)
    (g : Forest M)
    (huv : (u, v) ∈ g.edges) :
    (mkFrom M hsymm g).cap u v = M (g.edges_ne huv) := by 
  unfold mkFrom
  aesop

@[simp]
lemma mkFrom_asSimpleGraph_eq
    (hsymm : M.Symmetrical)
    (g : Forest M) :
    (mkFrom M hsymm g).asSimpleGraph = g.val := by
  let N := mkFrom M hsymm g
  ext u v
  constructor
  · intro h
    unfold mkFrom at h
    unfold UndirectedNetwork.asSimpleGraph at h
    simp at h
    have : (u, v) ∈ g.edges := by by_contra; aesop
    simp_all only [Finset.mem_filter, Finset.mem_univ, ne_eq, true_and]
  · intro h
    suffices 0 < N.cap u v from this
    have he : (u, v) ∈ g.edges := by simp_all only [ne_eq, Finset.mem_filter, Finset.mem_univ, and_self]
    suffices 0 < M (g.edges_ne he) from by simp_all only [ne_eq, Finset.mem_filter, Finset.mem_univ, and_self, mkFrom_cap_def]
    exact g.prop.right u v (g.edges_ne he) h

theorem mkFrom_IsAcyclic
    (hsymm : M.Symmetrical)
    (g : Forest M) :
    IsAcyclic (mkFrom M hsymm g).asSimpleGraph := by
  rw[mkFrom_asSimpleGraph_eq]
  aesop

lemma mkFrom_maxFlowValue_le_M
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (g : MaximalForest M)
    {u v : V}
    (huv : u ≠ v) :
    M huv ≤ (mkFrom M hsymm g).maxFlowValue u v := by
  let N := (mkFrom M hsymm g)
  if h_Reachable : N.asSimpleGraph.Reachable u v then
    let Pr : FlowProblem N.toNetwork := {s := u, t := v}
    suffices h : ∃ F : Flow Pr, M huv = F.value by
      obtain ⟨F, hF⟩ := h
      simp only [hF, Network.maxFlowValue, FlowProblem.maxFlow, ge_iff_le]
      apply Finset.le_max'
      simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]
    obtain ⟨P, _⟩ := Classical.exists_true_of_nonempty h_Reachable
    sorry
  else
    suffices M huv = 0 by linarith
    by_contra h_nonzero
    have h_not_Adj: ¬g.val.val.Adj u v := by
      by_contra h_Adj
      simp only [mkFrom_asSimpleGraph_eq, ne_eq] at h_Reachable 
      have := SimpleGraph.Adj.reachable h_Adj
      contradiction
    let g' := g.val.add_edge huv h_not_Adj
    sorry


lemma mkFrom_M_le_maxFlowValue
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (g : MaximalForest M)
    {u v : V}
    (huv : u ≠ v) :
    (mkFrom M hsymm g).maxFlowValue u v ≤ M huv := sorry

theorem mkFrom_hasMatrixM
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (g : MaximalForest M) :
    @M = (mkFrom M hsymm g).matrix := by
  funext u v huv
  exact Nat.le_antisymm (mkFrom_maxFlowValue_le_M M hsymm htri g huv) (mkFrom_M_le_maxFlowValue M hsymm htri g huv)

end mkFlowEquivalentForest
end

theorem flowEquivalentForest
    (M : PairMatrix V ℕ)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality) :
    ∃ T : UndirectedNetwork V, @M = T.matrix ∧ IsAcyclic T.asSimpleGraph :=
  let g : mkFlowEquivalentForest.MaximalForest M := Classical.choice inferInstance
  ⟨
    mkFlowEquivalentForest.mkFrom M hsymm g,
    mkFlowEquivalentForest.mkFrom_hasMatrixM M hsymm htri g,
    mkFlowEquivalentForest.mkFrom_IsAcyclic M hsymm g
  ⟩

theorem flowMatrixCharacterization (M : PairMatrix V ℕ) :
    (∃ G : UndirectedNetwork V, @M = G.matrix) ↔ (M.Symmetrical ∧ M.TriangleInequality) := sorry
