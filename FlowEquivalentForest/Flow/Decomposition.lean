import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.Flow.Path
import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation

open BigOperators
open ContainsEdge

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {N : UndirectedNetwork V} {Pr : FlowProblem N.toNetwork}

def SimpleGraph.Walk.dart_counts {G : SimpleGraph V} (p : G.Walk u v) : Multiset (G.Dart) := Multiset.ofList p.darts

theorem SimpleGraph.Walk.dart_counts_cons
    {G : SimpleGraph V}
    (h : G.Adj u v)
    (p : G.Walk v w) :
    (Walk.cons h p).dart_counts = (SimpleGraph.Dart.mk (u, v) h) ::ₘ p.dart_counts := by
  simp only [dart_counts, darts_cons, Multiset.cons_coe]

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

lemma UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero
    {F : Flow Pr}
    (h : F.f u v ≠ 0) :
    N.asSimpleGraph.Adj u v := sorry

def Flow.Path.cons
    {F : Flow Pr}
    {p : F.Path v w}
    (h : F.f u v ≠ 0)
    (h' : u ∉ p.val.val.support) :
    F.Path u w where
  val := {
    val := SimpleGraph.Walk.cons (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero h) p.val.val
    property := by
      intro d
      rw[SimpleGraph.Walk.dart_counts_cons, Multiset.count_cons]
      if hd : d = SimpleGraph.Dart.mk (u, v) (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero h) then
        simp only [hd, ite_true]
        have hdp : p.val.val.dart_counts.count d = 0 := by
          rw[Multiset.count_eq_zero, SimpleGraph.Walk.dart_counts, Multiset.mem_coe]
          by_contra h''
          have := hd ▸ p.val.val.dart_fst_mem_support_of_mem_darts h''
          exact h' this
        rw[←hd, hdp]
        by_contra h''
        simp only [zero_add, not_le, Nat.lt_one_iff] at h''
        exact h h''
      else
        simp only [hd, ite_false, add_zero]
        exact p.val.prop d
  }
  property := p.prop.cons h'

-- Probably makes constructing the path a lot nicer, but maybe we can also manage without these definitions.
abbrev Flow.Circulation (F : Flow Pr) (v : V) := {p : F.Walk v v // p.val.IsCirculation}
def Flow.Circulation.circulation {F : Flow Pr} (c : F.Circulation v) : N.asSimpleGraph.Circulation v where
  val := c.val.val
  property := c.prop
def Flow.CirculationFree (F : Flow Pr) := ∀ v, IsEmpty (F.Circulation v)

noncomputable instance {F : Flow Pr} {c : F.Circulation s} {u v : V} : Decidable (contains_edge c.circulation u v) := Classical.dec _
noncomputable def Flow.remove_circulation (F : Flow Pr) (c : F.Circulation s) : Flow Pr where
  f u v := F.f u v - (if contains_edge c.circulation u v then 1 else 0)
  conservation := by sorry
  capacity u v := by
    refine le_trans ?_ $ F.capacity u v
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
theorem Flow.remove_circulation.value (F : Flow Pr) (C : F.Circulation v) : (F.remove_circulation C).value = F.value := sorry

theorem Flow.remove_circulation.ssubset (F : Flow Pr) (C : F.Circulation v) : F.remove_circulation C ⊂ F := sorry

noncomputable def Flow.remove_all_circulations (F : Flow Pr) : Flow Pr :=
  have : Decidable (F.CirculationFree) := Classical.dec _
  if hF : F.CirculationFree then
    F
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    (F.remove_circulation c).remove_all_circulations
termination_by Flow.remove_all_circulations F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_circulation.ssubset

theorem Flow.remove_all_circulations.CirculationFree (F : Flow Pr) : F.remove_all_circulations.CirculationFree := by
  have : Decidable (F.CirculationFree) := Classical.dec _
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_true, hF]
    exact Flow.remove_all_circulations.CirculationFree ((F.remove_circulation c))
termination_by Flow.remove_all_circulations.CirculationFree F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_circulation.ssubset

theorem Flow.remove_all_circulations.value (F : Flow Pr) : F.remove_all_circulations.value = F.value := by
  have : Decidable (F.CirculationFree) := Classical.dec _
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: (remove_all_circulations (remove_circulation F c)).value =  (remove_circulation F c).value := by exact Flow.remove_all_circulations.value ( remove_circulation F c)
    have h2 : (remove_circulation F c).value = F.value := by exact Flow.remove_circulation.value F c
    apply Eq.trans h1 h2
termination_by Flow.remove_all_circulations.value F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_circulation.ssubset

theorem Flow.remove_all_circulations.subset (F : Flow Pr) : F.remove_all_circulations ⊆ F := by
  have : Decidable (F.CirculationFree) := Classical.dec _
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
    exact Eq.subset' rfl
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: remove_all_circulations (remove_circulation F c) ⊆  remove_circulation F c := by exact Flow.remove_all_circulations.subset (remove_circulation F c)
    have h2 : remove_circulation F c ⊆ F := subset_of_ssubset (Flow.remove_circulation.ssubset F c)
    exact subset_trans h1 h2
termination_by Flow.remove_all_circulations.subset F => F.range_sum
decreasing_by apply Flow.range_sum_lt_of_ssubset; apply Flow.remove_circulation.ssubset

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

theorem Flow.exists_path_of_value_nonzero_of_circulationFree
    (F : Flow Pr)
    (hF : F.value ≠ 0)
    (hC : F.CirculationFree) :
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
          have : flowIn F.f Pr.t - flowOut F.f Pr.t = 0 := by rw[hin, Nat.zero_sub]
          have : flowOut F.f Pr.s - flowIn F.f Pr.s = 0 := F.excess_s_eq_neg_excess_t ▸ this
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
      have : u.val ∉ path_so_far.val.val.support := sorry -- Otherwise, we would have constructed a circulation!
      let path_with_u : F.Path u Pr.t := Flow.Path.cons u.prop this

      -- Proof for termination (the path got longer):
      have : Fintype.card V - path_with_u.val.val.length < Fintype.card V - path_so_far.val.val.length := sorry

      build_path path_with_u
termination_by build_path p => Fintype.card V - p.val.val.length

theorem Flow.exists_path_of_value_nonzero (F : Flow Pr) (hF : F.value ≠ 0) : F.Path Pr.s Pr.t :=
  let p := Flow.exists_path_of_value_nonzero_of_circulationFree
    F.remove_all_circulations
    (remove_all_circulations.value F ▸ hF)
    (remove_all_circulations.CirculationFree F)
  p.transfer $ remove_all_circulations.subset _

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
-- def Flow.path_decomposition (F : Flow Pr) : Multiset (F.Path Pr.s Pr.t) := excuse_me
-- theorem Flow.path_decomposition_card (F : Flow Pr) : F.path_decomposition.card = F.value := excuse_me
-- theorem Flow.path_decomposition.f_eq_path_count (F : Flow Pr) :
--     ∀ d : N.asSimpleGraph.Dart, F.f d.fst d.snd = Multiset.countP (d ∈ ·.val.val.darts) F.path_decomposition := excuse_me
