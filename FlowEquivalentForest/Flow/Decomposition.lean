import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation
import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.Flow.Path
import FlowEquivalentForest.Flow.Circulation

open BigOperators
open ContainsEdge

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
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

def Flow.Walk.relax_val {F : Flow Pr} (p : F.Walk u v) (new_val : R) (hpos : 0 < new_val) : F.Walk u v where
  walk := p.walk
  val := min p.val new_val
  pos := lt_min p.pos hpos
  cap d := by
    refine le_trans ?_ (p.cap d)
    exact mul_le_mul_of_nonneg_left (min_le_left ..) (by positivity)

section

variable {F : Flow Pr} {u v : V} (p : F.Walk u v) (hp : ¬p.walk.Nil)

def Flow.Walk.Saturating := ∃ d ∈ p.walk.darts, p.walk.dart_counts.count d * p.val = F.f d.fst d.snd

private def Flow.Walk.fList := p.walk.darts.map fun d ↦ F.f d.fst d.snd
private lemma Flow.Walk.fList_length_pos : 0 < p.fList.length := by
  by_contra hzero
  absurd hp
  simp[Flow.Walk.fList] at hzero
  have := SimpleGraph.Walk.eq_of_length_eq_zero hzero
  subst this
  exact SimpleGraph.Walk.nil_iff_length_eq.mpr hzero

def Flow.Walk.fList_min := p.fList.minimum_of_length_pos <| p.fList_length_pos hp

lemma Flow.Walk.exists_fList_min : ∃ d ∈ p.walk.darts, p.fList_min hp = F.f d.fst d.snd := by
  simp only [fList_min]
  have := List.minimum_of_length_pos_mem <| p.fList_length_pos hp
  simp only [Flow.Walk.fList, List.mem_map] at this
  obtain ⟨d, hd, hd'⟩ := this
  exact ⟨d, hd, by rw[←hd']⟩

lemma Flow.Walk.val_le_fList_min : p.val ≤ p.fList_min hp := by
  obtain ⟨d, hd, hd'⟩ := p.exists_fList_min hp
  rw[hd']
  exact p.val_le_f hd

variable (hp' : p.walk.darts.Nodup)

def Flow.Walk.make_saturating : F.Walk u v where
  walk := p.walk
  val := p.fList_min hp
  pos := lt_of_lt_of_le p.pos <| p.val_le_fList_min hp
  cap d := by
    wlog hd : d ∈ p.walk.darts
    · simp[SimpleGraph.Walk.dart_counts, hd, F.nonneg]
    have : p.walk.dart_counts.count d = 1 := p.walk.dart_counts.count_eq_one_of_mem hp' hd
    simp[this, fList_min, fList]
    apply List.minimum_le_of_mem'
    rw[List.mem_map]
    refine ⟨d, hd, rfl⟩

theorem Flow.Walk.make_saturating_Saturating : (p.make_saturating hp hp').Saturating := by
  obtain ⟨d, ⟨hd, hd'⟩⟩ := p.exists_fList_min hp
  use d
  constructor
  · simp[make_saturating]; exact hd
  · have : p.walk.dart_counts.count d = 1 := p.walk.dart_counts.count_eq_one_of_mem hp' hd
    simp[this, make_saturating, hd']

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

def Flow.Path.relax_val {F : Flow Pr} (p : F.Path u v) (new_val : R) (hpos : 0 < new_val) : F.Path u v where
  val := p.val.relax_val new_val hpos
  property := p.prop

lemma Flow.Path.val_le_bottleneck {F : Flow Pr} (p : F.Path u v) (hne : u ≠ v) :
    let pne : N.asSimpleGraph.NonemptyPath u v := { path := p.path, ne := hne }
    p.val.val ≤ N.bottleneck pne := by
  intro pne
  obtain ⟨d, hd, hd'⟩ := N.exists_bottleneck_dart pne
  calc
    p.val.val ≤ F.f d.fst d.snd   := p.val.val_le_f hd
    _         ≤ N.cap d.fst d.snd := F.capacity ..
    _         = N.bottleneck pne  := hd'

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

def Flow.Circulation.make_saturating {F : Flow Pr} (c : F.Circulation v₀) : F.Circulation v₀ where
  val := c.val.make_saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup
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
    (F.remove_circulation c.make_saturating).remove_all_circulations
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_saturating (c.val.make_saturating_Saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup)

theorem Flow.remove_all_circulations.CirculationFree (F : Flow Pr) : F.remove_all_circulations.CirculationFree := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_true, hF]
    exact Flow.remove_all_circulations.CirculationFree ((F.remove_circulation c.make_saturating))
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_saturating (c.val.make_saturating_Saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup)

@[simp]
theorem Flow.remove_all_circulations.value (F : Flow Pr) : F.remove_all_circulations.value = F.value := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: (remove_all_circulations (remove_circulation F c.make_saturating)).value =  (remove_circulation F c.make_saturating).value := by exact Flow.remove_all_circulations.value (remove_circulation F c.make_saturating)
    have h2 : (remove_circulation F c.make_saturating).value = F.value := by exact Flow.remove_circulation_value F c.make_saturating
    apply Eq.trans h1 h2
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_saturating (c.val.make_saturating_Saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup)

theorem Flow.remove_all_circulations.subset (F : Flow Pr) : F.remove_all_circulations ⊆ F := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
    exact Eq.subset' rfl
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: remove_all_circulations (remove_circulation F c.make_saturating) ⊆  remove_circulation F c.make_saturating := by exact Flow.remove_all_circulations.subset (remove_circulation F c.make_saturating)
    have h2 : remove_circulation F c.make_saturating ⊆ F := subset_of_ssubset (Flow.remove_circulation.ssubset F c.make_saturating)
    exact subset_trans h1 h2
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_circulation_activeArcs_ssub_of_Saturating c.make_saturating (c.val.make_saturating_Saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup)

def Flow.Walk.transfer {F F' : Flow Pr} (p : F.Walk s t) (h : F ⊆ F') : F'.Walk s t :=
  { p with cap := (by intro d; exact le_trans (p.cap d) (h ..)) }

def Flow.Path.transfer {F F' : Flow Pr} (p : F.Path s t) (h : F ⊆ F') : F'.Path s t where
  val := p.val.transfer h
  property := p.property

theorem Flow.exists_path_of_value_pos_of_circulationFree
    (F : Flow Pr)
    (hF : 0 < F.value)
    (hC : F.CirculationFree) :
    F.Path Pr.s Pr.t :=
  build_path (Flow.Path.nil F F.value (by positivity))
where
  -- Recursive definition of the path: Given a path from some vertex v to the
  -- sink, we pick the next vertex u, add it to the front of the path and
  -- recurse until we arrive at the source.
  build_path {v} (path_so_far : F.Path v Pr.t) : F.Path Pr.s Pr.t :=
    if hvs : v = Pr.s then
      hvs ▸ path_so_far
    else
      let valid_us := {u : V // 0 < F.f u v}
      have : Nonempty valid_us := by
        by_contra h
        simp only [valid_us, nonempty_subtype, not_exists, not_not] at h
        have hin : flowIn F.f v = 0 := Fintype.sum_eq_zero _ (by
          intro u
          exact le_antisymm (le_of_not_lt (h u)) (F.nonneg u v)
        )
        if hvt : v = Pr.t then
          subst hvt
          have : excess F.f Pr.t ≤ 0 := by simp[excess, F.flowOut_nonneg, hin]
          have : F.value ≤ 0 := F.value_eq_excess_t ▸ this
          exact not_lt_of_le this hF
        else
          have h_not_nil : ¬path_so_far.val.walk.Nil := SimpleGraph.Walk.not_nil_of_ne hvt
          let w := path_so_far.val.walk.sndOfNotNil h_not_nil
          have hw : F.f v w ≠ 0 := by
            have := path_so_far.val.val_le_f <| path_so_far.val.walk.firstDart_mem_darts h_not_nil
            have := lt_of_lt_of_le path_so_far.val.pos this
            exact (ne_of_lt this).symm
          have : flowOut F.f v ≠ 0 := by
            intro h
            rw[flowOut] at h
            have : ∀ w, F.f v w = 0 := by simp[(Fintype.sum_eq_zero_iff_of_nonneg (F.nonneg v)).mp h]
            exact hw <| this w
          exact (F.conservation v ⟨hvs, hvt⟩ ▸ this) hin

      let u := Classical.choice this
      let path_so_far_with_new_val := path_so_far.relax_val (F.f u v) u.prop
      have hval_le_uv : path_so_far_with_new_val.val.val ≤ F.f u v := min_le_right ..

      have : u.val ∉ path_so_far_with_new_val.val.walk.support := by
        intro hu
        let tail := path_so_far_with_new_val.takeUntil u hu
        have := Flow.Circulation.from_dart_and_path tail hval_le_uv
        exact (hC _).elim this
      let path_with_u : F.Path u Pr.t := Flow.Path.cons hval_le_uv this

      -- Proof for termination (the path got longer):
      have : Fintype.card V - path_with_u.val.walk.length < Fintype.card V - path_so_far.val.walk.length := by
        simp[Flow.Path.cons, Flow.Walk.cons, SimpleGraph.Walk.length_cons]
        exact Nat.sub_lt_sub_left path_so_far.prop.length_lt (Nat.lt.base _)

      build_path path_with_u
termination_by Fintype.card V - path_so_far.val.walk.length

theorem Flow.exists_path_of_value_pos (F : Flow Pr) (hF : 0 < F.value) : F.Path Pr.s Pr.t :=
  let p := Flow.exists_path_of_value_pos_of_circulationFree
    F.remove_all_circulations
    (remove_all_circulations.value F ▸ hF)
    (remove_all_circulations.CirculationFree F)
  p.transfer $ remove_all_circulations.subset _

lemma Flow.from_flowPath_subseteq (F : Flow Pr) (p : F.Path Pr.s Pr.t) (hPr : Pr.s ≠ Pr.t) :
    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hPr }
    let F' := Flow.fromPath pne p.val.val p.val.pos.le (p.val_le_bottleneck hPr)
    F' ⊆ F := by
  intro pne F' u v
  wlog huv : contains_edge p.path u v
  · simp only [F', fromPath, ite_false, huv, zero_le, F.nonneg]
  simp only [F', fromPath, ite_true, huv]
  obtain ⟨_, hd⟩ := huv
  exact p.val.val_le_f hd

def Flow.remove_path (F : Flow Pr) (p : F.Path Pr.s Pr.t) : Flow Pr :=
  if hst : Pr.s = Pr.t then
    F
  else
    let pne : N.asSimpleGraph.NonemptyPath Pr.s Pr.t := { path := p.path, ne := hst }
    let F' := Flow.fromPath pne p.val.val p.val.pos.le (p.val_le_bottleneck hst)
    have hle : F' ⊆ F := Flow.from_flowPath_subseteq F p hst

    Flow.sub hle

@[simp]
theorem Flow.remove_path_value (F : Flow Pr) (p : F.Path Pr.s Pr.t) (hst : Pr.s ≠ Pr.t) : (F.remove_path p).value = F.value - p.val.val := by
  simp only [remove_path, dite_false, hst, sub_value, fromPath_value]

@[simp]
theorem Flow.remove_path_subset (F : Flow Pr) (p : F.Path Pr.s Pr.t) : F.remove_path p ⊆ F := by
  if hst : Pr.s = Pr.t then
    simp only [remove_path, hst, dite_true, subset_rfl]
  else
    simp only [remove_path, hst, dite_false, sub_subset]

inductive Flow.Decomposition : (F : Flow Pr) → Type (max (u_v + 1) (u_r + 1)) where
  | nil : Flow.Decomposition 0
  | cons :
    {F : Flow Pr} →
    (p : F.Path Pr.s Pr.t) →
    (F.remove_path p).Decomposition →
    F.Decomposition

def Flow.Decomposition.size {F : Flow Pr} : F.Decomposition → ℕ
  | nil => 0
  | cons _ D => D.size + 1

def Flow.Decomposition.Saturating {F : Flow Pr} : F.Decomposition → Prop
  | nil => True
  | cons p D => p.val.Saturating ∧ D.Saturating

abbrev Flow.SaturatingDecomposition (F : Flow Pr) := { D : F.Decomposition // D.Saturating }

noncomputable instance {F : Flow Pr} : Nonempty F.SaturatingDecomposition := sorry
noncomputable instance {F : Flow Pr} : Nonempty F.Decomposition :=
  Nonempty.intro <| (Classical.choice inferInstance : F.SaturatingDecomposition).val

namespace Flow

variable (F : Flow Pr)

theorem value_le_sum_f
    (ds : Finset N.asSimpleGraph.Dart)
    (hds : ∀ p : N.asSimpleGraph.Path Pr.s Pr.t, ∃ d ∈ ds, d ∈ p.val.darts) :
    F.value ≤ ∑ d in ds, F.f d.fst d.snd := by
  have h_right_nonneg := Finset.sum_nonneg (s := ds) (fun d _ ↦ F.nonneg d.fst d.snd)
  wlog hst : Pr.s ≠ Pr.t
  · exact F.value_eq_zero_of_s_eq_t (not_ne_iff.mp hst) ▸ h_right_nonneg

  have D : F.Decomposition := Classical.choice inferInstance
  induction D with
  | nil => exact Pr.nullFlow_value ▸ h_right_nonneg
  | @cons F p D' hF' =>
    wlog h_value : 0 ≤ F.value
    · exact le_trans (le_of_not_le h_value) h_right_nonneg

    specialize hF' <| Finset.sum_nonneg (s := ds) (fun d _ ↦ (F.remove_path p).nonneg d.fst d.snd)

    let F' := F.remove_path p
    obtain ⟨d, hd, hd'⟩ := hds p.path
    let u := d.fst
    let v := d.snd
    have hf : F'.f u v + p.val.val = F.f u v := by
      have hp : contains_edge p.path u v := ⟨d.is_adj, hd'⟩
      simp only [F', remove_path, Flow.sub, dite_false, hst, fromPath]
      -- annoyingly, we cannot use hp directly because the function subtraction
      -- is not evaluated in the goal, so we need to do that first
      simp only [HSub.hSub, Sub.sub, hp, ite_true]
      exact add_eq_of_eq_sub rfl

    let ds' := ds.erase d

    calc
      F.value = F'.value                                + p.val.val := by rw[F.remove_path_value p hst]; ring
      _       ≤ ∑ d in ds , F'.f d.fst d.snd            + p.val.val := add_le_add_right hF' _
      _       = ∑ d in ds', F'.f d.fst d.snd + F'.f u v + p.val.val := by rw[Finset.sum_erase_add ds _ hd]
      _       = ∑ d in ds', F'.f d.fst d.snd + F.f  u v             := by simp only [hf, add_assoc]
      _       ≤ ∑ d in ds', F.f  d.fst d.snd + F.f  u v             := by apply add_le_add_right; exact Finset.sum_le_sum <| fun d _ ↦ F.remove_path_subset ..
      _       = ∑ d in ds , F.f  d.fst d.snd                        := Finset.sum_erase_add ds _ hd

theorem value_le_f
    (d : N.asSimpleGraph.Dart)
    (hd : ∀ p : N.asSimpleGraph.Path Pr.s Pr.t, d ∈ p.val.darts) :
    F.value ≤ F.f d.fst d.snd :=
  le_of_le_of_eq
    (F.value_le_sum_f {d} fun p ↦ ⟨d, Finset.mem_singleton_self d, hd p⟩)
    (Finset.sum_singleton ..)

end Flow
