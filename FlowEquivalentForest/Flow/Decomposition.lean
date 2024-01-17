import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.Flow.Path
import FlowEquivalentForest.SimpleGraph.Path

open BigOperators
open ContainsEdge

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {N : UndirectedNetwork V} {Pr : FlowProblem N.toNetwork}

def SimpleGraph.Walk.dart_counts {G : SimpleGraph V} (p : G.Walk u v) : Multiset (G.Dart) := Multiset.ofList p.darts

-- A FlowWalk can only visit each dart of the network as many times as the flow
-- value on this dart.
def IsFlowWalk (F : Flow Pr) (p : N.asSimpleGraph.Walk u v) :=
  ∀ d, p.dart_counts.count d ≤ F.f d.fst d.snd

-- Could be untied from N and be a Walk in the clique instead to loose the
-- UndirectedNetwork requirement. For us, it might be nicer to not involve
-- another graph here since we are working on an undirected network anyways.
abbrev Flow.Walk (F : Flow Pr) (u v : V) :=
  {p : N.asSimpleGraph.Walk u v // IsFlowWalk F p}

def Flow.Walk.nil {F : Flow Pr} : F.Walk v v where
  val := SimpleGraph.Walk.nil
  property d := by simp only [SimpleGraph.Walk.dart_counts, SimpleGraph.Walk.darts_nil, Multiset.coe_nil, Multiset.not_mem_zero, not_false_eq_true, Multiset.count_eq_zero_of_not_mem, zero_le]

abbrev Flow.Path (F : Flow Pr) (u v : V) := {p : F.Walk u v // p.val.IsPath}
def Flow.Path.path {F : Flow Pr} (p : F.Path u v) : N.asSimpleGraph.Path u v where
  val := p.val.val
  property := p.prop
def Flow.Path.nil (F : Flow Pr) : F.Path v v where
  val := Flow.Walk.nil
  property := SimpleGraph.Walk.IsPath.nil

-- Probably makes constructing the path a lot nicer, but maybe we can also manage without these definitions.
abbrev Flow.Cycle (F : Flow Pr) (v : V) := {p : F.Walk v v // p.val.IsCycle}
def Flow.Cycle.cycle {F : Flow Pr} (c : F.Cycle v) : N.asSimpleGraph.Cycle v where
  val := c.val.val
  property := c.prop
def Flow.CycleFree (F : Flow Pr) := ∀ v, IsEmpty (F.Cycle v)

theorem Flow.flowOut_s_eq_flowIn_t_of_cycleFree (F : Flow Pr) (hF : F.CycleFree) : flowOut F.f Pr.s = flowIn F.f Pr.t := sorry

noncomputable instance {F : Flow Pr} {c : F.Cycle s} {u v : V} : Decidable (contains_edge c.cycle u v) := Classical.dec _
noncomputable def Flow.remove_cycle (F : Flow Pr) (c : F.Cycle s) : Flow Pr where
  f u v := F.f u v - (if contains_edge c.cycle u v then 1 else 0)
  conservation := by
    have hf' a b : (if contains_edge c.cycle a b then 1 else 0) ≤ F.f a b := sorry
    intro v hv
    rw[flowOut, flowIn, fintype_sum_sub_distrib_of_sub_nonneg (hf' v ·), fintype_sum_sub_distrib_of_sub_nonneg (hf' · v)]

    suffices (∑ u, if contains_edge c.cycle u v then 1 else 0) = (∑ w, if contains_edge c.cycle v w then 1 else 0) by
      rw[this]
      have := F.conservation v hv
      rw[flowOut, flowIn] at this
      rw[this]

    if hp : v ∈ c.cycle.val.support then
      have h {G : SimpleGraph V} (c : G.Cycle s) (hp : v ∈ c.val.support) : (∑ u : V, if contains_edge c u v then 1 else 0) = 1 := by
        obtain ⟨u, hu_pred, hu_uniq⟩ := c.pred_exists hp
        have h1 : (if contains_edge c u v then 1 else 0) = 1 := by
          simp only [hu_pred, ite_true]
        nth_rw 2 [← h1]
        refine Finset.sum_eq_single (β := ℕ) (a := u) ?_ ?_
        · intro b hb0 hb1
          have : ¬contains_edge c b v := by
            intro h
            exact hb1 (hu_uniq b h)
          simp only [this, ite_false]
        · intro h
          exact False.elim (h (Finset.mem_univ _))

      have h2 : (∑ w : V, if contains_edge (Cycle.cycle c) v w then 1 else 0) = 1 := by
        -- obtain ⟨u, hu_pred, hu_uniq⟩ := c.pred_exists hp
        -- have h1 : (if contains_edge c u v then 1 else 0) = 1 := by
        --   simp only [hu_pred, ite_true]
        -- nth_rw 2 [← h1]
        -- refine Finset.sum_eq_single (β := ℕ) (a := u) ?_ ?_
        -- · intro b hb0 hb1
        --   have : ¬contains_edge c b v := by
        --     intro h
        --     exact hb1 (hu_uniq b h)
        --   simp only [this, ite_false]
        -- · intro h
        --   exact False.elim (h (Finset.mem_univ _))
        sorry

      rw [h c.cycle hp, h2] -- both sides are equal to 1
    else
      have h {G : SimpleGraph V} (c : G.Cycle s) (hp : v ∉ c.val.support) : (∑ u : V, if contains_edge c u v then 1 else 0) = 0 := by
        sorry
        -- have h1 : ∀ u, (if contains_edge c u v then 1 else 0) = 0 := by
        --   intro u
        --   have (h : contains_edge c u v) : v ∈ c.val.support := by
        --     have ⟨h_Adj, h_dart⟩ := h
        --     have : v ∈ c.val.support := SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ h_dart
        --     exact this
        --   by_contra
        --   simp_all only [instContainsEdgeCycle, instContainsEdgeWalk, ne_eq, forall_exists_index, imp_false,
        --     exists_false, ite_false, not_true_eq_false]

      have h2 {G : SimpleGraph V} (c : G.Cycle s) (hp : v ∉ c.val.support) : (∑ w : V, if contains_edge c v w then 1 else 0) = 0 := by
        sorry
        -- have h1 : ∀ w, (if contains_edge c v w then 1 else 0) = 0 := by
        --   intro w
        --   have (h : contains_edge c v w) : v ∈ c.val.support := by
        --     have ⟨h_Adj, h_dart⟩ := h
        --     have : v ∈ c.val.support := SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ h_dart
        --     exact this
        --   by_contra
        --   simp_all only [instContainsEdgeCycle, instContainsEdgeWalk, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ,
        --     forall_true_left, Subtype.forall, ite_eq_right_iff, one_ne_zero, forall_exists_index, imp_false,
        --     exists_false, ite_false, not_true_eq_false]

      rw [h c.cycle hp, h2 c.cycle hp]
  capacity u v := by
    refine le_trans ?_ $ F.capacity u v
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
theorem Flow.remove_cycle.value (F : Flow Pr) (C : F.Cycle v) : (F.remove_cycle C).value = F.value := sorry

theorem Flow.remove_cycle.ssubset (F : Flow Pr) (C : F.Cycle v) : F.remove_cycle C ⊂ F := sorry

noncomputable def Flow.remove_all_cycles (F : Flow Pr) : Flow Pr :=
  have : Decidable (F.CycleFree) := Classical.dec _
  if hF : F.CycleFree then
    F
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    (F.remove_cycle c).remove_all_cycles
termination_by Flow.remove_all_cycles F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_cycle.ssubset

theorem Flow.remove_all_cycles.CycleFree (F : Flow Pr) : F.remove_all_cycles.CycleFree := by
  have : Decidable (F.CycleFree) := Classical.dec _
  unfold Flow.remove_all_cycles
  if hF : F.CycleFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_true, hF]
    exact Flow.remove_all_cycles.CycleFree ((F.remove_cycle c))
termination_by Flow.remove_all_cycles.CycleFree F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_cycle.ssubset

theorem Flow.remove_all_cycles.value (F : Flow Pr) : F.remove_all_cycles.value = F.value := by
  have : Decidable (F.CycleFree) := Classical.dec _
  unfold Flow.remove_all_cycles
  if hF : F.CycleFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: (remove_all_cycles (remove_cycle F c)).value =  (remove_cycle F c).value := by exact Flow.remove_all_cycles.value ( remove_cycle F c)
    have h2 : (remove_cycle F c).value = F.value := by exact Flow.remove_cycle.value F c
    apply Eq.trans h1 h2
termination_by Flow.remove_all_cycles.value F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_cycle.ssubset

theorem Flow.remove_all_cycles.subset (F : Flow Pr) : F.remove_all_cycles ⊆ F := by
  have : Decidable (F.CycleFree) := Classical.dec _
  unfold Flow.remove_all_cycles
  if hF : F.CycleFree then
    simp only [dite_true, hF]
    exact Eq.subset' rfl
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: remove_all_cycles (remove_cycle F c) ⊆  remove_cycle F c := by exact Flow.remove_all_cycles.subset (remove_cycle F c)
    have h2 : remove_cycle F c ⊆ F := subset_of_ssubset (Flow.remove_cycle.ssubset F c)
    exact subset_trans h1 h2
termination_by Flow.remove_all_cycles.subset F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_cycle.ssubset

def Flow.Walk.transfer {F F' : Flow Pr} (p : F.Walk s t) (h : F ⊆ F') : F'.Walk s t where
  val := p.val
  property := by
    intro d
    calc
      Multiset.count d p.val.dart_counts ≤ F.f d.fst d.snd  := p.prop d
      _                                  ≤ F'.f d.fst d.snd := h ..

def Flow.Walk.transfer.val {F F' : Flow Pr} (p : F.Walk s t) (h : F ⊆ F') : (p.transfer h).val = p.val := rfl

def Flow.Path.transfer {F F' : Flow Pr} (p : F.Path s t) (h : F ⊆ F') : F'.Path s t where
  val := p.val.transfer h
  property := Flow.Walk.transfer.val p.val h ▸ p.property

theorem Flow.exists_path_of_value_nonzero_of_cycleFree
    (F : Flow Pr)
    (hF : F.value ≠ 0)
    (hC : F.CycleFree) :
    F.Path Pr.s Pr.t :=
  build_path (Flow.Path.nil F)
where
  -- Recursive definition of the path: Given a path from some vertex u to the
  -- sink, we pick the next vertex v, add it to the front of the path and
  -- recurse until we arrive at the source.
  build_path {v} (path_so_far : F.Path v Pr.t) : F.Path Pr.s Pr.t :=
    if hvs : v = Pr.s then
      hvs ▸ path_so_far
    else
      let valid_us := {u : V // F.f u v ≠ 0 }
      have : Nonempty valid_us := by
        by_contra h
        simp only [nonempty_subtype, not_exists, not_not] at h
        have hin : flowIn F.f v = 0 := Finset.sum_eq_zero (λ u _ => h u)
        if hvt : v = Pr.t then
          subst hvt
          have : flowOut F.f Pr.s = 0 := F.flowOut_s_eq_flowIn_t_of_cycleFree hC ▸ hin
          have : flowOut F.f Pr.s - flowIn F.f Pr.s = 0 := by rw[this, Nat.zero_sub]
          exact hF this
        else
          have h_not_nil : ¬path_so_far.val.val.Nil := SimpleGraph.Walk.not_nil_of_ne hvt
          let w := path_so_far.val.val.sndOfNotNil h_not_nil
          have : F.f v w ≠ 0 := by
            intro h
            let d := path_so_far.val.val.firstDart h_not_nil
            have := path_so_far.val.prop d
            simp [SimpleGraph.Walk.firstDart_toProd, h, SimpleGraph.Walk.dart_counts, List.count_eq_zero] at this
            exact this $ path_so_far.val.val.firstDart_mem_darts h_not_nil
          have : flowOut F.f v ≠ 0 := by
            intro h
            rw[flowOut, Finset.sum_eq_zero_iff] at h
            exact this $ h w (Finset.mem_univ w)
          have : flowIn F.f v ≠ 0 := F.conservation v ⟨hvs, hvt⟩ ▸ this
          exact this hin

      let u := Classical.choice this
      have : u.val ∉ path_so_far.val.val.support := sorry -- Otherwise, we would have constructed a cycle!
      let path_with_u : F.Path u Pr.t := sorry -- Add u to the front of the path.

      -- Proof for termination (the path got longer):
      have : Fintype.card V - path_with_u.val.val.length < Fintype.card V - path_so_far.val.val.length := sorry

      build_path path_with_u
termination_by build_path p => Fintype.card V - p.val.val.length

theorem Flow.exists_path_of_value_nonzero (F : Flow Pr) (hF : F.value ≠ 0) : F.Path Pr.s Pr.t :=
  let p := Flow.exists_path_of_value_nonzero_of_cycleFree
    F.remove_all_cycles
    (remove_all_cycles.value F ▸ hF)
    (remove_all_cycles.CycleFree F)
  p.transfer $ remove_all_cycles.subset _

lemma Flow.from_flowPath_subseteq (F : Flow Pr) (p : F.Path Pr.s Pr.t) (hPr : Pr.s ≠ Pr.t) :
    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hst }
    let F' := Flow.fromPath pne 1 (N.bottleneck_pos pne)
    F' ⊆ F := by
  intro pne F' u v
  wlog huv : contains_edge p.path u v
  · simp only [fromPath, ite_false, huv, zero_le]
  simp only [fromPath, ite_true, huv]

  obtain ⟨h_adj, hd⟩ := huv
  let d := SimpleGraph.Dart.mk (u, v) h_adj
  have : 1 ≤ p.val.val.dart_counts.count d := Multiset.one_le_count_iff_mem.mpr hd
  exact le_trans this (p.val.prop _)


noncomputable def Flow.remove_path (F : Flow Pr) (p : F.Path Pr.s Pr.t) : Flow Pr :=
  if hst : Pr.s = Pr.t then
    F
  else
    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hst }
    let F' := Flow.fromPath pne 1 (N.bottleneck_pos pne)
    have hle : F' ⊆ F := Flow.from_flowPath_subseteq F p hst

    Flow.sub hle

theorem Flow.remove_path.value (F : Flow Pr) (p : F.Path Pr.s Pr.t) : (F.remove_path p).value = F.value - 1 := by
  if hst : Pr.s = Pr.t then
    simp only [remove_path, dite_true, hst, F.value_eq_zero_of_s_eq_t hst]
  else
    simp only [remove_path, dite_false, hst]

    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hst }
    have := Flow.fromPath_value pne 1 (N.bottleneck_pos pne)
    conv => right; rw[←this]
    have := Flow.sub_value (Flow.from_flowPath_subseteq F p hst) (Flow.fromPath_not_backward pne 1 (N.bottleneck_pos pne))
    exact this

lemma UndirectedNetwork.maxFlow_eq_zero_of_not_reachable
    (N : UndirectedNetwork V)
    {u v : V}
    (h : ¬N.asSimpleGraph.Reachable u v) :
    N.maxFlowValue u v = 0 := by
  let Pr : FlowProblem N.toNetwork := { s := u, t := v }
  by_contra hN
  obtain ⟨F, hF⟩ := Pr.maxFlow_exists
  have : F.value ≠ 0 := λ h_zero => hN $ h_zero ▸ hF.symm
  exact h $ (F.exists_path_of_value_nonzero this).path.val.reachable

-- Not needed for our theorem, but maybe fun
-- def Flow.path_decomposition (F : Flow Pr) : Multiset (F.Path Pr.s Pr.t) := sorry
-- theorem Flow.path_decomposition.f_eq_path_count (F : Flow Pr) :
--     ∀ d : N.asSimpleGraph.Dart, F.f d.fst d.snd = Multiset.countP (d ∈ ·.val.val.darts) F.path_decomposition := sorry
