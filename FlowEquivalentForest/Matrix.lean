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
  lemma mem_edges (F : Forest M) (h_Adj : F.val.Adj u v) : (u, v) ∈ F.edges := by
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_univ, and_self]

  lemma edges_ne {F : Forest M} (he : e ∈ F.edges) : e.fst ≠ e.snd := by
    by_contra heq
    apply SimpleGraph.irrefl F.val
    have := edges_Adj he
    rwa[heq] at this

  lemma edges_symm {F : Forest M} (huv : (u, v) ∈ F.edges) : (v, u) ∈ F.edges := by
    have := F.val.symm $ edges_Adj huv
    simp_all only [Finset.mem_filter, Finset.mem_univ, ne_eq, true_and, and_self]

  @[simp]
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
  lemma le_weight {g : Forest M} (h_Adj : g.val.Adj u v) : M h_Adj.ne + M h_Adj.ne.symm ≤ g.weight := by
    let e₁ : g.edges := { val := (u, v), property := mem_edges g h_Adj }
    let e₂ : g.edges := { val := (v, u), property := mem_edges g h_Adj.symm }
    let f (e : g.edges) := M $ g.edges_ne e.prop
    simp only [weight, ge_iff_le]
    refine @Finset.add_le_sum g.edges _ _ f _ e₁ e₂ ?_ ?_ ?_ ?_
    · intro _ _
      simp only [ge_iff_le, zero_le]
    · simp only [Finset.univ_eq_attach, Finset.mem_attach]
    · simp only [Finset.univ_eq_attach, Finset.mem_attach]
    · aesop

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

  -- Adding an (undirected) edge increases the weight by the two corresponding matrix values.
  @[simp]
  lemma add_edge.weight_eq_add
      (g : Forest M)
      {u v : V}
      (huv : u ≠ v)
      (h_M : 0 < min (M huv) (M huv.symm))
      (h_not_Reach : ¬g.val.Reachable u v) :
      (g.add_edge huv h_M h_not_Reach).weight = g.weight + M huv + M huv.symm := sorry

  def remove_edge (g : Forest M) (h_Adj : g.val.Adj u v) : Forest M := sorry

  lemma remove_edge.disconnect
      {g : Forest M}
      (P : g.val.Path s t)
      {d : g.val.Dart}
      (hd : d ∈ P.val.darts) :
      ¬(g.remove_edge d.is_adj).val.Reachable s t := sorry

  -- Removing an (undirected) edge decreases the weight by the two corresponding matrix values.
  @[simp]
  lemma remove_edge.weight_eq_sub (g : Forest M) (h_Adj : g.val.Adj u v) :
      (g.remove_edge h_Adj).weight = g.weight - M h_Adj.ne - M h_Adj.ne.symm := sorry
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

lemma mkFrom_M_le_maxFlowValue
    (hsymm : M.Symmetrical)
    (g : MaximalForest M)
    {u v : V}
    (huv : u ≠ v) :
    M huv ≤ (mkFrom M hsymm g).maxFlowValue u v := by
  wlog h_nonzero : 0 < M huv
  · linarith

  let N := mkFrom M hsymm g

  have h_uv_pos_weight : 0 < min (M huv) (M huv.symm) := (by simp only [lt_min_iff]; exact ⟨by linarith, by rw[hsymm]; linarith⟩)
  have h_Reachable : N.asSimpleGraph.Reachable u v := by
    -- We will show this by contradiction: If u and v are not connected, we can
    -- connect them with their direct edge and get a forest with increased
    -- weight - this contradicts that g is actually a maximal forest.
    by_contra h
    let g' := g.val.add_edge huv h_uv_pos_weight (by rwa[mkFrom_asSimpleGraph_eq] at h)
    have : g.val.weight < g'.weight := by rw[Forest.add_edge.weight_eq_add]; linarith
    exact not_le_of_lt this $ g.prop g'

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
    -- We construct a forest by replacing the edge e with the edge (u, v). If
    -- M (u, v) > M e, this forest would have a bigger weight - a
    -- contradiction to the maximality of g.
    intro he
    have h_Adj_in_g : g.val.val.Adj e.fst e.snd := e.is_adj
    let g' := g.val.remove_edge h_Adj_in_g
    have : ¬g'.val.Reachable u v := Forest.remove_edge.disconnect P he
    let g'' := g'.add_edge huv h_uv_pos_weight this

    by_contra hlt
    rw[not_le] at hlt
    let old := e.is_adj.ne
    let new := huv
    have : g.val.weight < g''.weight := by calc
      g.val.weight < g.val.weight + 2 * (M new - M old)                     := by simp_all only [ne_eq, ge_iff_le, lt_add_iff_pos_right, gt_iff_lt, zero_lt_two, zero_lt_mul_left, tsub_pos_iff_lt]
      _            = g.val.weight + 2 * M new - 2 * M old                   := by rw[Nat.mul_sub_left_distrib, Nat.add_sub_assoc (Nat.mul_le_mul_left 2 (Nat.le_of_lt hlt))]
      _            = g.val.weight - 2 * M old + 2 * M new                   := Nat.sub_add_comm (by rw[two_mul]; nth_rw 2 [hsymm]; exact Forest.le_weight h_Adj_in_g)
      _            = g.val.weight - M old - M old.symm + M new + M new.symm := by rw[two_mul, two_mul]; nth_rw 2 [hsymm old, hsymm new]; rw[Nat.sub_add_eq, Nat.add_assoc]
      _            = g''.weight                                             := by simp only [Forest.add_edge.weight_eq_add, Forest.remove_edge.weight_eq_sub]
    exact not_le_of_lt this $ g.prop g''

  -- Now that we know that the capacity along the path is big enough, we
  -- construct the flow.
  use Flow.fromPath huv P
  simp[Flow.fromPath.value_eq_bottleneck, UndirectedNetwork.bottleneck]
  intro d hd
  apply le_trans $ M_huv_le  d hd
  simp only [mkFrom, ne_eq, Eq.ndrec, id_eq, eq_mpr_eq_cast, Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le]
  have := d.is_adj
  simp_all only [mkFrom_asSimpleGraph_eq, dite_true, le_refl]

lemma mkFrom_maxFlowValue_le_M
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (g : MaximalForest M)
    {u v : V}
    (huv : u ≠ v) :
    (mkFrom M hsymm g).maxFlowValue u v ≤ M huv := by
  let N := mkFrom M hsymm g
  wlog h_Reachable : N.asSimpleGraph.Reachable u v
  · linarith[maxFlow_eq_zero_from_not_Reachable N h_Reachable]

  obtain ⟨P, _⟩ := Classical.exists_true_of_nonempty h_Reachable
  have P := P.toPath
  have := mkFrom_IsAcyclic M hsymm g
  rw[Acyclic_Path_maxflow_eq_bottleneck N this huv P]

  have triangle_along_path {u v : V} (P : N.asSimpleGraph.NonemptyPath u v) : N.bottleneck P.ne P.path ≤ M P.ne := by
    induction P using SimpleGraph.NonemptyPath.ind with
    | base u v h_Adj => sorry
    | ind u v w P h_Adj hu hvw ih => sorry

  exact triangle_along_path { path := P, ne := huv }

theorem mkFrom_hasMatrixM
    (hsymm : M.Symmetrical)
    (htri : M.TriangleInequality)
    (g : MaximalForest M) :
    @M = (mkFrom M hsymm g).matrix := by
  funext u v huv
  exact Nat.le_antisymm (mkFrom_M_le_maxFlowValue M hsymm g huv) (mkFrom_maxFlowValue_le_M M hsymm htri g huv)

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
