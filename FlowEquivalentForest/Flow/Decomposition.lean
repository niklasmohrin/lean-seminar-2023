import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation
import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.Flow.Path
import FlowEquivalentForest.Flow.Circulation

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

theorem SimpleGraph.Walk.dart_counts_takeUntil_le
    {G : SimpleGraph V}
    (p : G.Walk s t)
    {x : V}
    (hx : x ∈ p.support) :
    (p.takeUntil x hx).dart_counts ≤ p.dart_counts := by
  conv => right; rw[←p.take_spec hx]
  simp only [dart_counts, darts_append, Multiset.coe_le]
  conv => left; rw[←List.append_nil (p.takeUntil x hx).darts]
  rw[List.subperm_append_left]
  exact List.nil_subperm

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
  property d := by simp only [SimpleGraph.Walk.dart_counts, SimpleGraph.Walk.darts_nil, Multiset.coe_nil, Multiset.not_mem_zero, not_false_eq_true, Multiset.count_eq_zero_of_not_mem, zero_le]; apply F.nonneg

def Flow.Walk.takeUntil {F : Flow Pr} (p : F.Walk v w) (u : V) (hu : u ∈ p.val.support) : F.Walk v u where
  val := p.val.takeUntil u hu
  property d := le_trans (Int.ofNat_le.mpr <| (Multiset.le_iff_count.mp (p.val.dart_counts_takeUntil_le hu) d)) (p.prop d)

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
    N.asSimpleGraph.Adj u v := by
  by_contra h'
  simp [asSimpleGraph] at h'
  have := le_antisymm h' <| N.nonneg u v
  have := this ▸ F.capacity u v
  exact h <| le_antisymm this <| F.nonneg ..

def Flow.Walk.cons
    {F : Flow Pr}
    (h : F.f u v ≠ 0)
    (p : F.Walk v w)
    (h' : ¬contains_edge p.val u v) : -- h' could be relaxed, but this suffices for our purposes
    F.Walk u w where
  val := SimpleGraph.Walk.cons (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero h) p.val
  property := by
    intro d
    rw[SimpleGraph.Walk.dart_counts_cons, Multiset.count_cons]
    if hd : d = SimpleGraph.Dart.mk (u, v) (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero h) then
      simp only [hd, ite_true]
      have hdp : p.val.dart_counts.count d = 0 := by
        rw[Multiset.count_eq_zero, SimpleGraph.Walk.dart_counts, Multiset.mem_coe]
        intro hd'
        exact h' ⟨(UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero h), hd ▸ hd'⟩
      rw[←hd, hdp]
      by_contra h''
      simp only [zero_add, not_le] at h''
      have := le_antisymm (Int.le_of_lt_add_one (b := 0) h'') (F.nonneg ..)
      exact h this
    else
      simp only [hd, ite_false, add_zero]
      exact p.prop d

def Flow.Path.cons
    {F : Flow Pr}
    {p : F.Path v w}
    (h : F.f u v ≠ 0)
    (h' : u ∉ p.val.val.support) :
    F.Path u w where
  val := Flow.Walk.cons h p (h' ∘ p.val.val.mem_support_of_contains_edge_fst)
  property := p.prop.cons h'

def Flow.Path.takeUntil
    {F : Flow Pr}
    (p : F.Path v w)
    (u : V)
    (hu : u ∈ p.val.val.support) :
    F.Path v u where
  val := p.val.takeUntil u hu
  property := p.prop.takeUntil hu

-- Probably makes constructing the path a lot nicer, but maybe we can also manage without these definitions.
abbrev Flow.Circulation (F : Flow Pr) (v : V) := {p : F.Walk v v // p.val.IsCirculation}
def Flow.Circulation.circulation {F : Flow Pr} (c : F.Circulation v) : N.asSimpleGraph.Circulation v where
  val := c.val.val
  property := c.prop

def Flow.Circulation.from_dart_and_path
    {F : Flow Pr}
    (h : F.f u v ≠ 0)
    (p : F.Path v u) :
    F.Circulation u where
  val := Flow.Walk.cons h p.val p.path.not_contains_edge_end_start
  property := p.path.cons_isCirculation (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero h)

def Flow.CirculationFree (F : Flow Pr) := ∀ v, IsEmpty (F.Circulation v)

def Flow.Circulation.toFlow {F : Flow Pr} (c : F.Circulation v₀) : Flow Pr := Flow.UnitCirculation c.circulation

theorem Flow.Circulation.toFlow_subset {F : Flow Pr} (c : F.Circulation v₀) : c.toFlow ⊆ F := by
  simp [toFlow, UnitCirculation]
  intro u v
  unfold Flow.UnitCirculation_f
  if huv : contains_edge c.circulation u v then
    simp only [huv, ite_true]
    obtain ⟨_, hd⟩ := huv
    have : 1 ≤ c.val.val.dart_counts.count _ := Multiset.one_le_count_iff_mem.mpr hd
    exact le_trans
      (Int.toNat_le.mp this)
      (c.val.prop _)
  else
    simp only [huv, ite_false, zero_le, F.nonneg]

def Flow.remove_circulation (F : Flow Pr) (c : F.Circulation s) := Flow.sub c.toFlow_subset

theorem Flow.remove_circulation_value (F : Flow Pr) (c : F.Circulation v) : (F.remove_circulation c).value = F.value := by
  rw[remove_circulation, Flow.sub_value c.toFlow_subset, Circulation.toFlow, Flow.UnitCirculation_value_zero]
  ring

theorem Flow.remove_circulation.ssubset (F : Flow Pr) (C : F.Circulation v) : F.remove_circulation C ⊂ F := by
  rw[remove_circulation]
  apply Flow.sub_ssubset_of_nonzero
  rw[Circulation.toFlow]
  exact Flow.UnitCirculation_nonzero _

noncomputable def Flow.remove_all_circulations (F : Flow Pr) : Flow Pr :=
  have : Decidable (F.CirculationFree) := Classical.dec _
  if hF : F.CirculationFree then
    F
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    (F.remove_circulation c).remove_all_circulations
termination_by F.range_sum
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
termination_by F.range_sum
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
    have h2 : (remove_circulation F c).value = F.value := by exact Flow.remove_circulation_value F c
    apply Eq.trans h1 h2
termination_by F.range_sum
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
termination_by F.range_sum
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
  -- Recursive definition of the path: Given a path from some vertex v to the
  -- sink, we pick the next vertex u, add it to the front of the path and
  -- recurse until we arrive at the source.
  build_path {v} (path_so_far : F.Path v Pr.t) : F.Path Pr.s Pr.t :=
    if hvs : v = Pr.s then
      hvs ▸ path_so_far
    else
      let valid_us := {u : V // F.f u v ≠ 0}
      have : Nonempty valid_us := by
        by_contra h
        simp only [valid_us, nonempty_subtype, not_exists, not_not] at h
        have hin : flowIn F.f v = 0 := Finset.sum_eq_zero (λ u _ => h u)
        if hvt : v = Pr.t then
          subst hvt
          have : flowIn F.f Pr.t - flowOut F.f Pr.t = 0 := by rw[hin, Nat.zero_sub]
          have : flowOut F.f Pr.s - flowIn F.f Pr.s = 0 := F.excess_s_eq_neg_excess_t ▸ this
          exact hF this
        else
          absurd hin
          have h_not_nil : ¬path_so_far.val.val.Nil := SimpleGraph.Walk.not_nil_of_ne hvt
          let w := path_so_far.val.val.sndOfNotNil h_not_nil
          have : F.f v w ≠ 0 := by
            intro h
            let d := path_so_far.val.val.firstDart h_not_nil
            have := path_so_far.val.prop d
            simp [d, SimpleGraph.Walk.firstDart_toProd, h, SimpleGraph.Walk.dart_counts, List.count_eq_zero] at this
            exact this $ path_so_far.val.val.firstDart_mem_darts h_not_nil
          have : flowOut F.f v ≠ 0 := by
            intro h
            rw[flowOut, Finset.sum_eq_zero_iff] at h
            exact this $ h w (Finset.mem_univ w)
          exact F.conservation v ⟨hvs, hvt⟩ ▸ this

      let u := Classical.choice this
      have : u.val ∉ path_so_far.val.val.support := by
        intro hu
        let tail := path_so_far.takeUntil u hu
        have := Flow.Circulation.from_dart_and_path u.prop tail
        exact (hC _).elim this
      let path_with_u : F.Path u Pr.t := Flow.Path.cons u.prop this

      -- Proof for termination (the path got longer):
      have : Fintype.card V - path_with_u.val.val.length < Fintype.card V - path_so_far.val.val.length := by
        simp[Flow.Path.cons, Flow.Walk.cons, SimpleGraph.Walk.length_cons]
        exact Nat.sub_lt_sub_left path_so_far.prop.length_lt (Nat.lt.base _)

      build_path path_with_u
termination_by Fintype.card V - path_so_far.val.val.length

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
  · simp only [F', fromPath, ite_false, huv, zero_le]
  simp only [F', fromPath, ite_true, huv]

  obtain ⟨h_adj, hd⟩ := huv
  let d := SimpleGraph.Dart.mk (u, v) h_adj
  have : 1 ≤ p.val.val.dart_counts.count d := Multiset.one_le_count_iff_mem.mpr hd
  exact le_trans this (p.val.prop _)

def Flow.remove_path (F : Flow Pr) (p : F.Path Pr.s Pr.t) : Flow Pr :=
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
