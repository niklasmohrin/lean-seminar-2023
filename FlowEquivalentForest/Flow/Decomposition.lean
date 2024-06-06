import Mathlib.Algebra.Order.Field.Basic

import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation
import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.Flow.Path
import FlowEquivalentForest.Flow.Circulation

open BigOperators
open ContainsEdge

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type*} [LinearOrderedField R]
variable {N : UndirectedNetwork V R} {Pr : FlowProblem N.toNetwork}

-- Could be untied from N and be a Walk in the clique instead to loose the
-- UndirectedNetwork requirement. For us, it might be nicer to not involve
-- another graph here since we are working on an undirected network anyways.
structure Flow.Walk (F : Flow Pr) (u v : V) where
  walk : N.asSimpleGraph.Walk u v
  val : R
  pos : 0 < val
  cap : ∀ d, walk.dart_counts.count d * val ≤ F.f d.fst d.snd

def Flow.Walk.nil {F : Flow Pr} (val : R) (hpos : 0 < val) : F.Walk v v where
  walk := SimpleGraph.Walk.nil
  val := val
  pos := hpos
  cap d := by simp [SimpleGraph.Walk.dart_counts]; exact F.nonneg ..

def Flow.Walk.takeUntil {F : Flow Pr} (p : F.Walk v w) (u : V) (hu : u ∈ p.walk.support) : F.Walk v u where
  walk := p.walk.takeUntil u hu
  val := p.val
  pos := p.pos
  cap d := by
    refine le_trans ?_ (p.cap d)
    apply (mul_le_mul_right p.pos).mpr
    exact Nat.cast_le.mpr <| Multiset.le_iff_count.mp (p.walk.dart_counts_takeUntil_le hu) d

lemma Flow.Walk.val_le_f {F : Flow Pr} (p : F.Walk u v) (hd : d ∈ p.walk.darts) : p.val ≤ F.f d.fst d.snd :=
  calc
    p.val = 1                          * p.val := (one_mul _).symm
    _     ≤ p.walk.dart_counts.count d * p.val := (mul_le_mul_right p.pos).mpr (Nat.one_le_cast.mpr (Multiset.one_le_count_iff_mem.mpr hd))
    _     ≤ F.f d.fst d.snd                    := p.cap ..

section

variable {F : Flow Pr} {u v : V} (p : F.Walk u v) (hp : ¬p.walk.Nil)

def Flow.Walk.Saturating := ∃ d ∈ p.walk.darts, p.walk.dart_counts.count d * p.val = F.f d.fst d.snd

private def Flow.Walk.capList := p.walk.darts.map (fun d ↦ F.f d.fst d.snd / p.walk.dart_counts.count d)
private lemma Flow.Walk.capList_length_pos : 0 < p.capList.length := by
  by_contra hzero
  absurd hp
  simp[capList] at hzero
  have := SimpleGraph.Walk.eq_of_length_eq_zero hzero
  subst this
  exact SimpleGraph.Walk.nil_iff_length_eq.mpr hzero

def Flow.Walk.saturatingVal := p.capList.minimum_of_length_pos <| p.capList_length_pos hp

lemma Flow.Walk.exists_saturatingVal : ∃ d ∈ p.walk.darts, p.walk.dart_counts.count d * p.saturatingVal hp = F.f d.fst d.snd := by
  simp only [saturatingVal]
  have := List.minimum_of_length_pos_mem <| p.capList_length_pos hp
  simp only [capList, List.mem_map] at this
  obtain ⟨d, hd, hd'⟩ := this
  use d
  constructor
  · exact hd
  · rw[←hd']
    apply mul_div_cancel₀
    simp only [ne_eq, Nat.cast_eq_zero, Multiset.count_eq_zero, not_not]
    exact hd

lemma Flow.Walk.exists_saturatingVal' : ∃ d ∈ p.walk.darts, p.saturatingVal hp = F.f d.fst d.snd / p.walk.dart_counts.count d := by
  obtain ⟨d, hd, hd'⟩ := p.exists_saturatingVal hp
  use d
  constructor
  · exact hd
  · apply eq_div_of_mul_eq
    · rw[@Nat.cast_ne_zero]
      exact Ne.symm <| ne_of_lt <| Multiset.count_pos.mpr <| hd
    · rwa[mul_comm] at hd'

lemma Flow.Walk.val_le_saturatingVal : p.val ≤ p.saturatingVal hp := by
  obtain ⟨d, hd, hd'⟩ := p.exists_saturatingVal' hp
  rw[hd']
  have : 0 < p.walk.dart_counts.count d := Multiset.count_pos.mpr <| hd
  rw[le_div_iff' (Nat.cast_pos.mpr this)]
  exact p.cap d

def Flow.Walk.make_Saturating : F.Walk u v where
  walk := p.walk
  val := p.saturatingVal hp
  pos := lt_of_lt_of_le p.pos <| p.val_le_saturatingVal hp
  cap d := by
    wlog hd : d ∈ p.walk.darts
    · simp[SimpleGraph.Walk.dart_counts, hd, F.nonneg]

    have : 0 < p.walk.dart_counts.count d := Multiset.count_pos.mpr <| hd
    rw[←le_div_iff' (Nat.cast_pos.mpr this)]
    simp only [saturatingVal, capList, List.minimum_of_length_pos_le_iff, val]
    apply List.minimum_le_of_mem'
    simp only [List.mem_map]
    use d

theorem Flow.Walk.make_Saturating_Saturating : (p.make_Saturating hp).Saturating := p.exists_saturatingVal hp

end

abbrev Flow.Path (F : Flow Pr) (u v : V) := {p : F.Walk u v // p.walk.IsPath}

def Flow.Path.path {F : Flow Pr} (p : F.Path u v) : N.asSimpleGraph.Path u v where
  val := p.val.walk
  property := p.prop

def Flow.Path.nil (F : Flow Pr) (val : R) (hpos : 0 < val) : F.Path v v where
  val := Flow.Walk.nil val hpos
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
    (p : F.Walk v w)
    (h : p.val ≤ F.f u v)
    (h' : ¬contains_edge p.walk u v) : -- h' could be relaxed, but this suffices for our purposes
    F.Walk u w where
  walk := SimpleGraph.Walk.cons
    (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero (ne_of_lt (lt_of_lt_of_le p.pos h)).symm)
    p.walk
  val := p.val
  pos := p.pos
  cap d := by
    have hnonzero := (ne_of_lt (lt_of_lt_of_le p.pos h)).symm
    rw[SimpleGraph.Walk.dart_counts_cons, Multiset.count_cons]
    if hd : d = SimpleGraph.Dart.mk (u, v) (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero hnonzero) then
      simp only [hd, ite_true]
      have hdp : p.walk.dart_counts.count d = 0 := by
        rw[Multiset.count_eq_zero, SimpleGraph.Walk.dart_counts, Multiset.mem_coe]
        intro hd'
        exact h' ⟨(UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero hnonzero), hd ▸ hd'⟩
      rw[←hd, hdp]
      ring_nf
      exact h
    else
      simp only [hd, ite_false, add_zero]
      exact p.cap d

def Flow.Path.cons
    {F : Flow Pr}
    {p : F.Path v w}
    (h : p.val.val ≤ F.f u v)
    (h' : u ∉ p.val.walk.support) :
    F.Path u w where
  val := p.val.cons h (h' ∘ p.val.walk.mem_support_of_contains_edge_fst)
  property := p.prop.cons h'

def Flow.Path.takeUntil
    {F : Flow Pr}
    (p : F.Path v w)
    (u : V)
    (hu : u ∈ p.val.walk.support) :
    F.Path v u where
  val := p.val.takeUntil u hu
  property := p.prop.takeUntil hu

-- Probably makes constructing the path a lot nicer, but maybe we can also manage without these definitions.
abbrev Flow.Circulation (F : Flow Pr) (v : V) := {p : F.Walk v v // p.walk.IsCirculation}
def Flow.Circulation.circulation {F : Flow Pr} (c : F.Circulation v) : N.asSimpleGraph.Circulation v where
  val := c.val.walk
  property := c.prop

def Flow.Circulation.from_dart_and_path
    {F : Flow Pr}
    (p : F.Path v u)
    (h : p.val.val ≤ F.f u v) :
    F.Circulation u where
  val := p.val.cons h p.path.not_contains_edge_end_start
  property := p.path.cons_isCirculation (UndirectedNetwork.asSimpleGraph_adj_of_f_nonzero (ne_of_lt (lt_of_lt_of_le p.val.pos h)).symm)

def Flow.CirculationFree (F : Flow Pr) := ∀ v, IsEmpty (F.Circulation v)

noncomputable instance {F : Flow Pr} : Decidable (F.CirculationFree) := Classical.dec _

private lemma Flow.Circulation.toFlow_cap {F : Flow Pr} (c : F.Circulation v₀) :
    ∀ d ∈ c.val.walk.darts, c.val.val ≤ N.cap d.fst d.snd := by
  intro d hd
  exact le_trans (c.val.val_le_f hd) (F.capacity ..)

@[simp]
def Flow.Circulation.toFlow {F : Flow Pr} (c : F.Circulation v₀) : Flow Pr :=
  Flow.fromCirculation
    c.circulation
    c.val.val
    (le_of_lt c.val.pos)
    c.toFlow_cap

lemma Flow.Circulation.toFlow_nonzero {F : Flow Pr} (c : F.Circulation v₀) : c.toFlow ≠ 0 := by
  rw[Circulation.toFlow]
  exact Flow.fromCirculation_nonzero c.circulation c.val.val c.toFlow_cap c.val.pos

theorem Flow.Circulation.toFlow_subset {F : Flow Pr} (c : F.Circulation v₀) : c.toFlow ⊆ F := by
  simp [toFlow, fromCirculation]
  intro u v
  unfold Flow.fromCirculation_f
  if huv : contains_edge c.circulation u v then
    simp only [huv, ite_true]
    obtain ⟨_, hd⟩ := huv
    exact c.val.val_le_f hd
  else
    simp only [huv, ite_false, zero_le, F.nonneg]

def Flow.Circulation.make_Saturating {F : Flow Pr} (c : F.Circulation v₀) : F.Circulation v₀ where
  val := c.val.make_Saturating c.circulation.prop.not_nil
  property := c.prop

def Flow.remove_circulation (F : Flow Pr) (c : F.Circulation s) := Flow.sub c.toFlow_subset

theorem Flow.remove_circulation_activeArcs_ssub_of_Saturating (F : Flow Pr) (c : F.Circulation v₀) (hc : c.val.Saturating) :
    (Flow.sub c.toFlow_subset).activeArcs ⊂ F.activeArcs := by
  obtain ⟨d, hd, hd'⟩ := hc
  apply Flow.sub_activeArcs_ssubset c.toFlow_subset (u := d.fst) (v := d.snd)
  constructor
  · exact lt_of_lt_of_le c.val.pos <| c.val.val_le_f hd
  · have : contains_edge c.circulation d.fst d.snd := by simp[SimpleGraph.instContainsEdgeCirculation]; use d.is_adj; exact hd
    simp[←hd', fromCirculation, this]
    suffices c.val.walk.dart_counts.count d = 1 by rw[this]; ring
    exact Multiset.count_eq_one_of_mem c.circulation.prop.dart_counts_nodup hd

@[simp]
theorem Flow.remove_circulation_value (F : Flow Pr) (c : F.Circulation v) : (F.remove_circulation c).value = F.value := by
  rw[remove_circulation, Flow.sub_value c.toFlow_subset, Circulation.toFlow, Flow.fromCirculation_value_zero]
  ring

theorem Flow.remove_circulation.ssubset (F : Flow Pr) (C : F.Circulation v) : F.remove_circulation C ⊂ F := by
  rw[remove_circulation]
  apply Flow.sub_ssubset_of_nonzero
  exact C.toFlow_nonzero

noncomputable def Flow.remove_all_circulations (F : Flow Pr) : Flow Pr :=
  if hF : F.CirculationFree then
    F
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    (F.remove_circulation c.make_Saturating).remove_all_circulations
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_Saturating (c.val.make_Saturating_Saturating c.circulation.prop.not_nil)

theorem Flow.remove_all_circulations.CirculationFree (F : Flow Pr) : F.remove_all_circulations.CirculationFree := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_true, hF]
    exact Flow.remove_all_circulations.CirculationFree ((F.remove_circulation c.make_Saturating))
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_Saturating (c.val.make_Saturating_Saturating c.circulation.prop.not_nil)

@[simp]
theorem Flow.remove_all_circulations.value (F : Flow Pr) : F.remove_all_circulations.value = F.value := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: (remove_all_circulations (remove_circulation F c.make_Saturating)).value =  (remove_circulation F c.make_Saturating).value := by exact Flow.remove_all_circulations.value (remove_circulation F c.make_Saturating)
    have h2 : (remove_circulation F c.make_Saturating).value = F.value := by exact Flow.remove_circulation_value F c.make_Saturating
    apply Eq.trans h1 h2
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_Saturating (c.val.make_Saturating_Saturating c.circulation.prop.not_nil)

theorem Flow.remove_all_circulations.subset (F : Flow Pr) : F.remove_all_circulations ⊆ F := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
    exact Eq.subset' rfl
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: remove_all_circulations (remove_circulation F c.make_Saturating) ⊆  remove_circulation F c.make_Saturating := by exact Flow.remove_all_circulations.subset (remove_circulation F c.make_Saturating)
    have h2 : remove_circulation F c.make_Saturating ⊆ F := subset_of_ssubset (Flow.remove_circulation.ssubset F c.make_Saturating)
    exact subset_trans h1 h2
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_Saturating (c.val.make_Saturating_Saturating c.circulation.prop.not_nil)

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

theorem Flow.exists_path_of_value_pos_of_circulationFree
    (F : Flow Pr)
    (hF : 0 < F.value)
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
        have hin : flowIn F.f v = 0 := Fintype.sum_eq_zero _ h
        if hvt : v = Pr.t then
          subst hvt
          have : excess F.f Pr.t ≤ 0 := by simp[excess, F.flowOut_nonneg, hin]
          have : F.value ≤ 0 := F.value_eq_excess_t ▸ this
          omega
        else
          have h_not_nil : ¬path_so_far.val.val.Nil := SimpleGraph.Walk.not_nil_of_ne hvt
          let w := path_so_far.val.val.sndOfNotNil h_not_nil
          have hw : F.f v w ≠ 0 := by
            intro h
            let d := path_so_far.val.val.firstDart h_not_nil
            have := path_so_far.val.prop d
            simp [d, SimpleGraph.Walk.firstDart_toProd, h, SimpleGraph.Walk.dart_counts, List.count_eq_zero] at this
            exact this $ path_so_far.val.val.firstDart_mem_darts h_not_nil
          have : flowOut F.f v ≠ 0 := by
            intro h
            rw[flowOut] at h
            have : ∀ w, F.f v w = 0 := by simp[(Fintype.sum_eq_zero_iff_of_nonneg (F.nonneg v)).mp h]
            exact hw <| this w
          exact (F.conservation v ⟨hvs, hvt⟩ ▸ this) hin

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

theorem Flow.exists_path_of_value_pos (F : Flow Pr) (hF : 0 < F.value) : F.Path Pr.s Pr.t :=
  let p := Flow.exists_path_of_value_pos_of_circulationFree
    F.remove_all_circulations
    (remove_all_circulations.value F ▸ hF)
    (remove_all_circulations.CirculationFree F)
  p.transfer $ remove_all_circulations.subset _

lemma Flow.from_flowPath_subseteq (F : Flow Pr) (p : F.Path Pr.s Pr.t) (hPr : Pr.s ≠ Pr.t) :
    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hPr }
    let F' := Flow.fromPath pne 1 (by trivial) (N.bottleneck_pos pne)
    F' ⊆ F := by
  intro pne F' u v
  wlog huv : contains_edge p.path u v
  · simp only [F', fromPath, ite_false, huv, zero_le, F.nonneg]
  simp only [F', fromPath, ite_true, huv]

  obtain ⟨h_adj, hd⟩ := huv
  let d := SimpleGraph.Dart.mk (u, v) h_adj
  have : 1 ≤ p.val.val.dart_counts.count d := Multiset.one_le_count_iff_mem.mpr hd
  exact le_trans (Int.ofNat_le.mpr this) (p.val.prop _)

def Flow.remove_path (F : Flow Pr) (p : F.Path Pr.s Pr.t) : Flow Pr :=
  if hst : Pr.s = Pr.t then
    F
  else
    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hst }
    let F' := Flow.fromPath pne 1 (by trivial) (N.bottleneck_pos pne)
    have hle : F' ⊆ F := Flow.from_flowPath_subseteq F p hst

    Flow.sub hle

theorem Flow.remove_path.value (F : Flow Pr) (p : F.Path Pr.s Pr.t) (hst : Pr.s ≠ Pr.t) : (F.remove_path p).value = F.value - 1 := by
  simp only [remove_path, dite_false, hst]
  let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hst }
  have := Flow.fromPath_value pne 1 (by trivial) (N.bottleneck_pos pne)
  conv => right; rw[←this]
  exact Flow.sub_value (F.from_flowPath_subseteq p hst)

lemma UndirectedNetwork.maxFlow_eq_zero_of_not_reachable
    (N : UndirectedNetwork V)
    {u v : V}
    (h : ¬N.asSimpleGraph.Reachable u v) :
    N.maxFlowValue u v = 0 := by
  let Pr : FlowProblem N.toNetwork := { s := u, t := v }
  by_contra hN
  let F := (⊤ : Flow Pr)
  have : 0 < F.value := Ne.lt_of_le' hN Pr.maxFlow_nonneg
  exact h $ (F.exists_path_of_value_pos this).path.val.reachable

-- Not needed for our theorem, but maybe fun
-- def Flow.path_decomposition (F : Flow Pr) : Multiset (F.Path Pr.s Pr.t) := excuse_me
-- theorem Flow.path_decomposition_card (F : Flow Pr) : F.path_decomposition.card = F.value := excuse_me
-- theorem Flow.path_decomposition.f_eq_path_count (F : Flow Pr) :
--     ∀ d : N.asSimpleGraph.Dart, F.f d.fst d.snd = Multiset.countP (d ∈ ·.val.val.darts) F.path_decomposition := excuse_me
