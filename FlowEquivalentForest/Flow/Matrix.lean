import Mathlib.Algebra.BigOperators.Order
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Linarith

import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.Flow.MaxFlow
import FlowEquivalentForest.PairMatrix
import FlowEquivalentForest.Util
import FlowEquivalentForest.SimpleGraph.Basic
import FlowEquivalentForest.SimpleGraph.Acyclic

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]

-- Currently, there is no need to pass in `hst`, but it is needed to match the
-- definition of PairMatrix (and we might want to restrict FlowProblem later on
-- to assume s ≠ t)
noncomputable def Network.matrix (N : Network V R) [HasMaxFlow N] (s t : V) (_ : s ≠ t) : R := N.maxFlowValue s t

class HasMatrix (α : Type*) (β : outParam (Type*)) where
  hasMatrix : α → β → Prop

infixl:50 " ~ₘ " => HasMatrix.hasMatrix

@[simp]
instance Network.instHasMatrix : HasMatrix (Network V R) (PairMatrix V R) where
  hasMatrix N M := ∃ (_ : HasMaxFlow N), N.matrix = @M

@[simp]
instance UndirectedNetwork.instHasMatrix : HasMatrix (UndirectedNetwork V R) (PairMatrix V R) where
  hasMatrix := Network.instHasMatrix.hasMatrix ∘ UndirectedNetwork.toNetwork

open SimpleGraph
open BigOperators

def PairMatrix.TriangleInequality (M : PairMatrix V R) :=
  ∀ u v w, (huv : u ≠ v) → (hvw : v ≠ w) → (huw : u ≠ w) → min (M huv) (M hvw) ≤ M huw

section
namespace mkFlowEquivalentForest

-- All the "spanning trees" over the complete graph over V.
-- We also cancel forest edges that would have 0 capacity in the end, because we can.
abbrev Forest (M : PairMatrix V R) := { g : SimpleGraph V // IsAcyclic g ∧ ∀ u v, (huv : u ≠ v) → g.Adj u v → 0 < M huv }

instance {M : PairMatrix V R} : Nonempty (Forest M) := by
  simp only [nonempty_subtype]
  use emptyGraph V
  simp_all only [emptyGraph_eq_bot, isAcyclic_bot, bot_adj, IsEmpty.forall_iff, implies_true, forall_const, and_self]

namespace Forest
  variable {M : PairMatrix V R}

  @[simp]
  def weight (F : Forest M) [DecidableRel F.val.Adj] := ∑ e in F.val.dartNonDiagFinset, M e.ne

  lemma weight_bounded (M : PairMatrix V R) : (∃ b, ∀ F : Forest M, F.weight ≤ b) := by
    let M_max := max 0 $ Classical.choose M.bounded
    use Fintype.card V * Fintype.card V * M_max
    intro F
    calc
      F.weight = ∑ e in F.val.dartNonDiagFinset, M (e.ne) := by rfl
      _        ≤ ∑ _e in F.val.dartNonDiagFinset, M_max   := by
                                                              apply Finset.sum_le_sum
                                                              intros
                                                              simp only [ne_eq, le_max_iff, Classical.choose_spec M.bounded, or_true, M_max]
      _        = (F.val.dartNonDiagFinset).card * M_max   := by simp_all only [ne_eq, Finset.sum_const, nsmul_eq_mul, M_max]
      _        ≤ Fintype.card V * Fintype.card V * M_max  := by norm_cast; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr F.val.dartNonDiagFinset_card_le) (le_max_left ..)

  @[simp]
  lemma le_weight {g : Forest M} (h_Adj : g.val.Adj u v) : M h_Adj.ne + M h_Adj.ne.symm ≤ g.weight := by
    unfold weight
    let e₁ := NonDiag.mk (u, v) h_Adj.ne
    let e₂ := NonDiag.mk (v, u) h_Adj.ne.symm
    refine Finset.add_le_sum (N := R) (f := λ e => M e.ne) (i := e₁) (j := e₂) ?_ ?_ ?_ ?_
    · intro e he
      have := (g.val.mem_dartNonDiagFinset_iff _).mp he
      exact le_of_lt <| g.prop.right _ _ this.ne this
    · simp only [dartNonDiagFinset, Finset.filter_congr_decidable, Finset.mem_univ, Finset.mem_filter, h_Adj, and_self]
    · simp only [dartNonDiagFinset, Finset.filter_congr_decidable, Finset.mem_univ, Finset.mem_filter, h_Adj.symm, and_self]
    · by_contra h
      rw[NonDiag.ext_iff] at h
      exact h_Adj.ne h.left

  -- constructs a new forest from g with the additional edge (u, v)
  def add_edge
      (g : Forest M)
      {u v : V}
      (huv : u ≠ v)
      (h_M : 0 < min (M huv) (M huv.symm))
      (h_not_Reach : ¬g.val.Reachable u v) :
      Forest M where
    val := g.val.addEdges {s(u,v)}
    property := by
      constructor
      · exact g.val.addEdges_isAcyclic_of_not_reachable g.prop.left h_not_Reach
      · intro a b hab h_Adj
        if h_Adj' : g.val.Adj a b then
          exact g.prop.right a b hab h_Adj'
        else
          simp only [addEdges, ne_eq, Set.union_singleton, fromEdgeSet_adj, Set.mem_insert_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, mem_edgeSet] at h_Adj
          match h_Adj.left with
          | Or.inl h => match h with
            | Or.inl ⟨ha, hb⟩ =>
              subst ha hb
              exact lt_of_lt_of_le h_M (min_le_left _ _)
            | Or.inr ⟨ha, hb⟩ =>
              subst ha hb
              exact lt_of_lt_of_le h_M (min_le_right _ _)
          | Or.inr h => contradiction

  lemma weight_eq_add_of_dartNonDiagFinset_eq_union
      (g g' : Forest M)
      {u v : V}
      (huv : u ≠ v) :
      let e₁ := NonDiag.mk (u, v) huv
      let e₂ := NonDiag.mk (v, u) huv.symm
      g'.val.dartNonDiagFinset = g.val.dartNonDiagFinset ∪ {e₁, e₂} →
      Disjoint g.val.dartNonDiagFinset {e₁, e₂} →
      g'.weight = g.weight + M huv + M huv.symm := by
    intro e₁ e₂ h₁ h₂
    unfold weight
    have : e₁ ≠ e₂ := λ h => huv ((NonDiag.ext_iff ..).mp h).left
    rw[h₁, Finset.sum_union h₂, Finset.sum_pair this]
    linarith

  -- Adding an (undirected) edge increases the weight by the two corresponding matrix values.
  @[simp]
  lemma add_edge.weight_eq_add
      (g : Forest M)
      {u v : V}
      (huv : u ≠ v)
      (h_M : 0 < min (M huv) (M huv.symm))
      (h_not_Reach : ¬g.val.Reachable u v) :
      (g.add_edge huv h_M h_not_Reach).weight = g.weight + M huv + M huv.symm := by
    let g' := g.add_edge huv h_M h_not_Reach
    let e₁ := NonDiag.mk (u, v) huv
    let e₂ := NonDiag.mk (v, u) huv.symm
    have h₁ : g'.val.dartNonDiagFinset = g.val.dartNonDiagFinset ∪ {e₁, e₂} := g.val.addEdges_singleton_dartNonDiagFinset huv
    have h₂ : Disjoint g.val.dartNonDiagFinset {e₁, e₂} := g.val.dartNonDiagFinset_disjoint_of_not_adj huv (h_not_Reach ∘ SimpleGraph.Adj.reachable)
    exact weight_eq_add_of_dartNonDiagFinset_eq_union g g' huv h₁ h₂

  def remove_edge (g : Forest M) (u v : V) : Forest M where
    val := g.val.deleteEdges {s(u, v)}
    property := by
      constructor
      · exact g.val.deleteEdges_isAcyclic g.prop.left _
      · intro a b hab h_Adj
        rw[deleteEdges_adj] at h_Adj
        exact g.prop.right a b hab h_Adj.left

  -- Removing an (undirected) edge decreases the weight by the two corresponding matrix values.
  @[simp]
  lemma remove_edge.weight_eq_sub (g : Forest M) (h_Adj : g.val.Adj u v) :
      (g.remove_edge u v).weight = g.weight - M h_Adj.ne - M h_Adj.ne.symm := by
    let g' := g.remove_edge u v
    suffices g.weight = (g.remove_edge u v).weight + M h_Adj.ne + M h_Adj.ne.symm by linarith
    let e₁ := NonDiag.mk' h_Adj.ne
    let e₂ := NonDiag.mk' h_Adj.ne.symm
    have h₁ : g.val.dartNonDiagFinset = g'.val.dartNonDiagFinset ∪ {e₁, e₂} := by
      conv =>
        right
        left
        simp only [g', remove_edge, g.val.deleteEdges_singleton_dartNonDiagFinset h_Adj.ne]
      rw[Finset.sdiff_union_self_eq_union]
      apply Eq.symm
      rw[Finset.union_eq_left]
      exact g.val.subset_dartNonDiagFinset_of_adj h_Adj
    have : ¬g'.val.Adj u v := λ h => ((g.val.deleteEdges_adj ..).mp h).right rfl
    have h₂ : Disjoint g'.val.dartNonDiagFinset {e₁, e₂} := g'.val.dartNonDiagFinset_disjoint_of_not_adj h_Adj.ne this
    exact weight_eq_add_of_dartNonDiagFinset_eq_union g' g h_Adj.ne h₁ h₂

end Forest

abbrev MaximalForest (M : PairMatrix V R) := {F : Forest M // ∀ F' : Forest M, F'.weight ≤ F.weight}

instance {M : PairMatrix V R} : Nonempty (MaximalForest M) := by
  classical
  obtain ⟨F, _, hF⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun (F : Forest M) ↦ F.weight
  exact ⟨F, hF ▸ (Finset.le_sup' (·.weight) <| Finset.mem_univ ·)⟩

variable (M : PairMatrix V R)

def mkFrom (hsymm : M.Symmetrical) (g : Forest M) [DecidableRel g.val.Adj] : UndirectedNetwork V R where
  cap u v := if huv : g.val.Adj u v then M (huv.ne) else 0
  nonneg u v := by
    wlog huv : g.val.Adj u v
    · simp only [ne_eq, huv, ↓reduceDite, le_refl]
    simp only [ne_eq, huv, ↓reduceDite]
    exact le_of_lt <| g.prop.right _ _ huv.ne huv
  loopless v := by simp only [SimpleGraph.irrefl, dite_false]
  symm u v := by
    if huv : g.val.Adj u v then
      simp only [dite_true, huv, huv.symm, hsymm huv.ne]
    else
      have hvu : ¬g.val.Adj v u := huv ∘ SimpleGraph.Adj.symm
      simp only [dite_false, huv, hvu]

@[simp]
lemma mkFrom_asSimpleGraph_eq
    (hsymm : M.Symmetrical)
    (g : Forest M) :
    (mkFrom M hsymm g).asSimpleGraph = g.val := by
  ext u v
  constructor
  · intro h
    by_contra huv
    simp only [mkFrom, UndirectedNetwork.asSimpleGraph, dite_false, huv] at h
    exact lt_irrefl _ h
  · intro huv
    simp only [mkFrom, UndirectedNetwork.asSimpleGraph, dite_true, huv]
    exact g.prop.right u v huv.ne huv

theorem mkFrom_IsAcyclic
    (hsymm : M.Symmetrical)
    (g : Forest M) :
    IsAcyclic (mkFrom M hsymm g).asSimpleGraph := by
  rw[mkFrom_asSimpleGraph_eq]
  aesop

lemma mkFrom_M_le_maxFlowValue
    (hsymm : M.Symmetrical)
    (g : MaximalForest M)
    (Pr : FlowProblem (mkFrom M hsymm g).toNetwork)
    (hst : Pr.s ≠ Pr.t) :
    ∃ F : Flow Pr, M hst ≤ F.value := by
  wlog h_pos : 0 < M hst
  · use 0; rw[Flow.zero_value]; exact le_of_not_lt h_pos

  let N := mkFrom M hsymm g

  have h_st_pos_weight : 0 < min (M hst) (M hst.symm) := (by simp only [lt_min_iff]; exact ⟨by linarith, by rw[hsymm]; linarith⟩)
  have h_Reachable : N.asSimpleGraph.Reachable Pr.s Pr.t := by
    -- We will show this by contradiction: If s and t are not connected, we can
    -- connect them with their direct edge and get a forest with increased
    -- weight - this contradicts that g is actually a maximal forest.
    by_contra h
    let g' := g.val.add_edge hst h_st_pos_weight (by rwa[mkFrom_asSimpleGraph_eq] at h)
    have : g.val.weight < g'.weight := by rw[Forest.add_edge.weight_eq_add]; linarith[h_pos, hsymm hst]
    exact not_le_of_lt this $ g.prop g'

  obtain ⟨P, _⟩ := Classical.exists_true_of_nonempty h_Reachable
  have P : N.asSimpleGraph.NonemptyPath _ _ := {path := P.toPath, ne := hst}

  have M_hst_le e : (e ∈ P.path.val.darts) → M hst ≤ M e.is_adj.ne := by
    -- This step has to connect knowledge of N.asSimpleGraph and g.val, which
    -- we know to be equal. To avoid having to convert each fact separately
    -- (which also sometimes doesn't work, because rewriting a variable does
    -- not automatically rewrite all hypotheses about it), we want to use
    -- `subst` to replace all occurrences of N.asSimpleGraph with g.val.
    -- However `subst` can only substitute free variables, not arbitrary
    -- expression like N.asSimpleGraph. Therefore, we use `generalize` to
    -- forget that we are dealing with N.asSimpleGraph and instead reason about
    -- some arbitrary graph "N_asSimpleGraph" (note that instead of a period,
    -- there is an underscore), for which the hypotheses we know about
    -- N.asSimpleGraph still hold - in particular, we know that this graph is
    -- equal to g.val. This way, we can `subst` this graph for g.val at the
    -- beginning and stop worrying about it.
    have heq := mkFrom_asSimpleGraph_eq M hsymm g
    generalize N.asSimpleGraph = N_asSimpleGraph at *
    subst heq
    -- We construct a forest by replacing the edge e with the edge (s, t). If
    -- M (s, t) > M e, this forest would have a bigger weight - a
    -- contradiction to the maximality of g.
    intro he
    let g' := g.val.remove_edge e.fst e.snd
    have : ¬g'.val.Reachable Pr.s Pr.t := g.val.val.deleteEdges_not_reachable_of_mem_edges g.val.prop.left P.path (SimpleGraph.Walk.mem_edges_of_mem_darts he)
    let g'' := g'.add_edge hst h_st_pos_weight this

    by_contra hlt
    rw[not_le] at hlt
    let old := e.is_adj.ne
    let new := hst
    have : g.val.weight < g''.weight := by calc
      g.val.weight < g.val.weight + 2 * (M new - M old)                     := by simp_all only [ne_eq, Forest.weight, lt_add_iff_pos_right, gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos]
      _            = g.val.weight - M old - M old.symm + M new + M new.symm := by linarith[hsymm old, hsymm new]
      _            = g''.weight                                             := by simp only [g', g'', Forest.add_edge.weight_eq_add, Forest.remove_edge.weight_eq_sub, e.is_adj]
    exact not_le_of_lt this $ g.prop g''

  -- Now that we know that the capacity along the path is big enough, we
  -- construct the flow.
  use Flow.fromPath P (N.bottleneck P) (N.bottleneck_nonneg P) (le_refl _)
  rw[Flow.fromPath_value]
  simp only [UndirectedNetwork.bottleneck, Finset.le_min'_iff, Finset.mem_image, List.mem_toFinset, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro d hd
  apply le_trans $ M_hst_le d hd
  simp only [mkFrom, ne_eq, Forest.weight, ge_iff_le, N]
  have := d.is_adj
  simp_all only [lt_min_iff, true_and, ne_eq, Forest.weight, mkFrom_asSimpleGraph_eq, ↓reduceDite, le_refl, N]

lemma mkFrom_maxFlowValue_le_M
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (hnonneg : M.Nonneg)
    (g : MaximalForest M)
    {Pr : FlowProblem (mkFrom M hsymm g).toNetwork}
    (hst : Pr.s ≠ Pr.t)
    (F : Flow Pr) :
    F.value ≤ M hst := by
  let N := mkFrom M hsymm g
  wlog h_Reachable : N.asSimpleGraph.Reachable Pr.s Pr.t
  · rw[N.flow_value_zero_of_not_reachable h_Reachable F]
    exact hnonneg hst

  obtain ⟨P, _⟩ := Classical.exists_true_of_nonempty h_Reachable
  have P : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := {path := P.toPath, ne := hst}
  have := mkFrom_IsAcyclic M hsymm g
  apply le_trans <| N.flow_value_le_bottleneck_of_isAcyclic this P F

  have triangle_along_path {u v : V} (P : N.asSimpleGraph.NonemptyPath u v) : N.bottleneck P ≤ M P.ne := by
    induction P using SimpleGraph.NonemptyPath.ind with
    | base u v h_Adj =>
      simp only [N, mkFrom, UndirectedNetwork.bottleneck.single_edge]
      aesop
    | ind u v w P h_Adj hu hvw ih =>
      have huv : u ≠ v := h_Adj.ne
      have huw : u ≠ w := by aesop
      rw[UndirectedNetwork.bottleneck.cons]
      calc min (N.cap u v) (N.bottleneck P)
        _ ≤ min (N.cap u v) (M hvw) := min_le_min_left _ ih
        _ = min (M huv) (M hvw)     := by have : N.cap u v = M huv := (by rw[mkFrom_asSimpleGraph_eq] at h_Adj; simp only [N, mkFrom, dite_true, h_Adj]); rw[this]
        _ ≤ M huw                   := htri u v w huv hvw huw

  exact triangle_along_path P

theorem mkFrom_exists_top
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (hnonneg : M.Nonneg)
    (g : MaximalForest M)
    (Pr : FlowProblem (mkFrom M hsymm g).toNetwork) :
    ∃ F : Flow Pr, IsTop F := by
  wlog hst : Pr.s ≠ Pr.t
  · use 0
    intro F'
    simp only [Flow.le_iff, Flow.zero_value]
    exact le_of_eq <| F'.value_eq_zero_of_s_eq_t <| not_ne_iff.mp hst
  classical
  obtain ⟨F, hF⟩ := mkFrom_M_le_maxFlowValue M hsymm g Pr hst
  use F
  intro F'
  rw[Flow.le_iff]
  refine le_trans ?_ hF
  exact mkFrom_maxFlowValue_le_M M hsymm htri hnonneg g hst F'

noncomputable instance
    instOrderTop
    (M : PairMatrix V R)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (hnonneg : M.Nonneg)
    (g : MaximalForest M)
    (Pr : FlowProblem (mkFrom M hsymm g).toNetwork) :
    OrderTop (Flow Pr) where
  top := Classical.choose <| mkFrom_exists_top M hsymm htri hnonneg g Pr
  le_top := Classical.choose_spec <| mkFrom_exists_top M hsymm htri hnonneg g Pr

noncomputable instance
    instMaxFlow
    (M : PairMatrix V R)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (hnonneg : M.Nonneg)
    (g : MaximalForest M) :
    HasMaxFlow ((mkFrom M hsymm g).toNetwork) := instOrderTop M hsymm htri hnonneg g

theorem mkFrom_hasMatrixM
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (hnonneg : M.Nonneg)
    (g : MaximalForest M) :
    mkFrom M hsymm g ~ₘ @M := by
  have inst := instMaxFlow M hsymm htri hnonneg g
  use inst
  funext s t hst
  simp[Network.matrix, Network.maxFlowValue, FlowProblem.maxFlow]
  apply le_antisymm
  · exact mkFrom_maxFlowValue_le_M htri hnonneg (Pr := {s, t}) hst _
  · obtain ⟨F, hF⟩ := mkFrom_M_le_maxFlowValue M hsymm g {s, t} hst
    exact le_trans hF <| le_top (α := Flow {s, t})

end mkFlowEquivalentForest
end

theorem flowEquivalentForest
    (M : PairMatrix V R)
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (hnonneg : M.Nonneg) :
    ∃ T : UndirectedNetwork V R, T ~ₘ @M ∧ T.asSimpleGraph.IsAcyclic :=
  open mkFlowEquivalentForest in
  have g : MaximalForest M := Classical.choice inferInstance
  ⟨
    mkFrom M hsymm g,
    mkFrom_hasMatrixM M hsymm htri hnonneg g,
    mkFrom_IsAcyclic M hsymm g
  ⟩

-- theorem flowMatrixCharacterization (M : PairMatrix V R) :
--     (∃ G : UndirectedNetwork V, @M = G.matrix) ↔ (M.Symmetrical ∧ M.TriangleInequality) := excuse_me
