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
  lemma mem_edges {F : Forest M} (h_Adj : F.val.Adj e.fst e.snd) : e ∈ F.edges := by
    simp_all only [Finset.mem_filter, Finset.mem_univ]

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

  @[simp]
  lemma le_weight {g : Forest M} (h_Adj : g.val.Adj u v) : M h_Adj.ne ≤ g.weight := sorry

  -- constructs a new forest from g with the additional edge (u, v)
  def add_edge
      (g : Forest M)
      {u v : V}
      (huv : u ≠ v)
      (h_M : 0 < min (M huv) (M huv.symm))
      (h_not_Reach : ¬g.val.Reachable u v) :
    Forest M where
    val := g.val ⊔ SimpleGraph.fromEdgeSet {⟦(u,v)⟧}
    property := by
      apply And.intro
      rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
      intro c d h_Adj
      rw [SimpleGraph.isBridge_iff]
      apply And.intro
      assumption
      simp only [fromEdgeSet_adj]
      simp at h_Adj
      simp


      sorry

      intro a b hab h_Adj
      apply Or.elim h_Adj
      intro h_Adj
      exact g.prop.right a b hab h_Adj
      intro heq
      sorry

  @[simp]
  lemma add_edge.weight_eq_add
      (g : Forest M)
      {u v : V}
      (huv : u ≠ v)
      (h_M : 0 < min (M huv) (M huv.symm))
      (h_not_Reach : ¬g.val.Reachable u v) :
      (g.add_edge huv h_M h_not_Reach).weight = g.weight + M huv := sorry

  def remove_edge (g : Forest M) (h_Adj : g.val.Adj u v) : Forest M := sorry

  lemma remove_edge.disconnect
      {g : Forest M}
      (P : g.val.Path s t)
      {d : g.val.Dart}
      (hd : d ∈ P.val.darts) :
      ¬(g.remove_edge d.is_adj).val.Reachable s t := sorry

  @[simp]
  lemma remove_edge.weight_eq_sub (g : Forest M) (h_Adj : g.val.Adj u v) :
      (g.remove_edge h_Adj).weight = g.weight - M h_Adj.ne := sorry
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
    suffices h : ∃ F : Flow Pr, M huv ≤ F.value by
      obtain ⟨F, hF⟩ := h
      simp only [Network.maxFlowValue, FlowProblem.maxFlow, ge_iff_le]
      apply le_trans hF
      apply Finset.le_max'
      simp_all only [mkFrom_asSimpleGraph_eq, ne_eq, Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]

    obtain ⟨P, _⟩ := Classical.exists_true_of_nonempty h_Reachable
    have P := P.toPath

    have M_huv_le e : (e ∈ P.val.darts) → M huv ≤ M e.is_adj.ne := by
      -- We construct a forest by replacing the edge e with the edge (u, v). If
      -- M (u, v) > M e, this forest would have a bigger weight - a
      -- contradiction to the maximality of g.
      intro he
      -- TODO: The sorries here are because we really want to rewrite the types
      -- of e and P with mkFrom_asSimpleGraph_eq so that they belong to g
      -- again, but then we lose all hypotheses about them, because they still
      -- only hold in N.asSimpleGraph. This seems like something people from
      -- the Zulip could help us with.
      have h_Adj_in_g : g.val.val.Adj e.fst e.snd := sorry -- e.is_adj
      let g' := g.val.remove_edge h_Adj_in_g
      have : ¬g'.val.Reachable u v := sorry -- Forest.remove_edge.disconnect P he
      sorry -- below is the previous proof which does not work anymore with the updated definition of add_edge
      -- let g'' := g'.add_edge huv this

      -- by_contra hlt
      -- rw[not_le] at hlt
      -- have : g.val.weight < g''.weight := by calc
      --   g.val.weight < g.val.weight + (M huv - M e.is_adj.ne) := lt_add_of_pos_right _ (Nat.sub_pos_of_lt hlt)
      --   _            = g.val.weight + M huv - M e.is_adj.ne := by rw[Nat.add_sub_assoc (Nat.le_of_lt hlt)]
      --   _            = g.val.weight - M e.is_adj.ne + M huv := Nat.sub_add_comm (g.val.le_weight h_Adj_in_g)
      --   _            = g''.weight := by simp only [Forest.add_edge.weight_eq_add, Forest.remove_edge.weight_eq_sub]
      -- exact not_le_of_lt this $ g.prop g''

    -- Now that we know that the capacity along the path is big enough, we
    -- construct the flow.
    use Flow.fromPath huv P
    simp[Flow.fromPath.value_eq_bottleneck, UndirectedNetwork.bottleneck]
    intro d hd
    apply le_trans $ M_huv_le d hd
    simp only [mkFrom, ne_eq, Eq.ndrec, id_eq, eq_mpr_eq_cast, Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le]
    have := d.is_adj
    simp_all only [mkFrom_asSimpleGraph_eq, dite_true, le_refl]
  else
    suffices M huv = 0 by linarith
    -- We will show this by contradiction: If the value is nonzero, we can add
    -- this edge to g and get a forest with higher weight - this contradicts
    -- that g is actually a maximal forest.
    sorry -- the code below previously proved this, but the forest lemma changed
    -- let g' := g.val.add_edge huv (by rwa[mkFrom_asSimpleGraph_eq] at h_Reachable)
    -- by_contra h_nonzero
    -- have : g.val.weight < g'.weight := by simp only [Forest.add_edge.weight_eq_add, lt_add_iff_pos_right, Nat.pos_of_ne_zero h_nonzero]
    -- exact not_le_of_lt this $ g.prop g'

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
