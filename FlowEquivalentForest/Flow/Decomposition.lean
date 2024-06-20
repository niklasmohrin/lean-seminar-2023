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

lemma Flow.Walk.Saturating.not_nil {F : Flow Pr} {p : F.Walk u v} (h : p.Saturating) : ¬p.walk.Nil := by
  open SimpleGraph.Walk in
  obtain ⟨_, hd, _⟩ := h
  cases h'' : p.walk with
  | nil => subst_vars; rw[h'', darts_nil] at hd; contradiction
  | cons _ _ => exact not_nil_cons

class ToSubflow.{u} (F : Flow Pr) (α : Type u) where
  to_subflow : α → Flow Pr
  subset : ∀ a, to_subflow a ⊆ F

open ToSubflow (to_subflow)

@[simp]
def Flow.remove_subflow_from (F : Flow Pr) [inst : ToSubflow F α] (a : α) : Flow Pr :=
  Flow.sub <| inst.subset a

class MaintainsSaturation (F : Flow Pr) (prop : F.Walk u v → Prop) extends ToSubflow F (Subtype prop) where
  maintains_saturation (p : Subtype prop) :
    p.val.Saturating → ∃ u v, 0 < F.f u v ∧ (to_subflow p).f u v = F.f u v

abbrev Flow.Path (F : Flow Pr) (u v : V) := {p : F.Walk u v // p.walk.IsPath}

@[simp]
def Flow.Path.path {F : Flow Pr} (p : F.Path u v) : N.asSimpleGraph.Path u v where
  val := p.val.walk
  property := p.prop

@[simp]
def Flow.Path.reverse_problem {F : Flow Pr} (p : F.Path u v) : F.reverse_problem.Path u v where
  val := { p.val with cap := p.val.cap }
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

@[simp]
instance Flow.instPathToSubflowForward (F : Flow Pr) : ToSubflow F (F.Path Pr.s Pr.t) where
  to_subflow p :=
    if hst : Pr.s = Pr.t then
      0
    else
      Flow.fromPath
        { path := p.path, ne := hst }
        p.val.val
        p.val.pos.le
        (p.val_le_bottleneck hst)
  subset p := by
    wlog hst : Pr.s ≠ Pr.t
    · simp at hst; simp[hst]
    simp only [instHasSubsetFlow, hst, ↓reduceDite, Flow.fromPath]
    intro u v
    wlog huv : contains_edge p.path u v
    · simp only [huv, ↓reduceIte, F.nonneg]
    simp only [huv, ↓reduceIte]
    exact p.val.val_le_f huv.2

@[simp]
instance Flow.instPathToSubflowBackward (F : Flow Pr) : ToSubflow F (F.Path Pr.t Pr.s) where
  to_subflow p := Flow.reverse_problem <| F.reverse_problem.instPathToSubflowForward.to_subflow p.reverse_problem
  subset p := F.reverse_problem.instPathToSubflowForward.subset p.reverse_problem

instance Flow.instPathMaintainsSaturationForward (F : Flow Pr) : MaintainsSaturation F (fun (p : F.Walk Pr.s Pr.t) ↦ p.walk.IsPath) where
  maintains_saturation p h := by
    wlog hst : Pr.s ≠ Pr.t
    · exfalso
      generalize Pr.s = u, Pr.t = v at hst p
      simp at hst
      subst hst
      exact p.val.walk.isPath_iff_eq_nil.mp p.prop ▸ h.not_nil <| .nil
    obtain ⟨d, hd, hd'⟩ := h
    use d.fst, d.snd, lt_of_lt_of_le p.val.pos (p.val.val_le_f hd)
    have := Multiset.count_eq_one_of_mem
      (Multiset.coe_nodup.mpr (SimpleGraph.Walk.darts_nodup_of_support_nodup p.prop.support_nodup))
      hd
    simp[hst, Flow.fromPath, d.is_adj, hd, ←hd', SimpleGraph.Walk.dart_counts, this]

instance Flow.instPathMaintainsSaturationBackward (F : Flow Pr) : MaintainsSaturation F (fun (p : F.Walk Pr.t Pr.s) ↦ p.walk.IsPath) where
  maintains_saturation p h := F.reverse_problem.instPathMaintainsSaturationForward.maintains_saturation (Flow.Path.reverse_problem p) h

theorem Flow.remove_subflow_from_activeArcs_ssubset_of_saturating
    (F : Flow Pr)
    {prop : F.Walk u v → Prop}
    [MaintainsSaturation F prop]
    (p : Subtype prop)
    (h : p.val.Saturating) :
    (F.remove_subflow_from p).activeArcs ⊂ F.activeArcs := by
  simp only [remove_subflow_from]
  obtain ⟨_, _, huv⟩ := MaintainsSaturation.maintains_saturation p h
  exact Flow.sub_activeArcs_ssubset _ huv

def Flow.Path.make_saturating {F : Flow Pr} (p : F.Path u v) (hp : ¬p.val.walk.Nil) : F.Path u v where
  val := p.val.make_saturating hp <| SimpleGraph.Walk.darts_nodup_of_support_nodup p.path.prop.support_nodup
  property := p.prop

lemma Flow.Path.make_saturating_Saturating {F : Flow Pr} (p : F.Path u v) (hp : ¬p.val.walk.Nil) : (p.make_saturating hp).val.Saturating :=
  p.val.make_saturating_Saturating hp <| SimpleGraph.Walk.darts_nodup_of_support_nodup p.path.prop.support_nodup

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

def Flow.Circulation.reverse_problem {F : Flow Pr} (c : F.Circulation v) : F.reverse_problem.Circulation v where
  val := { c.val with cap := c.val.cap }
  property := c.property

def Flow.CirculationFree (F : Flow Pr) := ∀ v, IsEmpty (F.Circulation v)

def Flow.CirculationFree.reverse_problem {F : Flow Pr} (h : F.CirculationFree) : F.reverse_problem.CirculationFree := by
  intro v
  by_contra h'
  obtain ⟨c⟩ := not_isEmpty_iff.mp h'
  exact (h v).elim c.reverse_problem

noncomputable instance {F : Flow Pr} : Decidable (F.CirculationFree) := Classical.dec _

lemma FlowProblem.circulationFree_zero : (0 : Flow Pr).CirculationFree := by
  intro v
  by_contra h
  obtain ⟨c⟩ := not_isEmpty_iff.mp h
  exact lt_irrefl _
    <| lt_of_lt_of_le c.val.pos
    <| c.val.val_le_f
    <| c.val.walk.firstDart_mem_darts c.circulation.prop.not_nil

private lemma Flow.Circulation.toFlow_cap {F : Flow Pr} (c : F.Circulation v₀) :
    ∀ d ∈ c.val.walk.darts, c.val.val ≤ N.cap d.fst d.snd := by
  intro d hd
  exact le_trans (c.val.val_le_f hd) (F.capacity ..)

@[simp]
instance Flow.instCirculationToSubflow (F : Flow Pr) : ToSubflow F (F.Circulation v₀) where
  to_subflow c := Flow.fromCirculation c.circulation c.val.val c.val.pos.le c.toFlow_cap
  subset c u v := by
    by_cases huv : contains_edge c.circulation u v
    · simp[fromCirculation, fromCirculation_f, huv, c.val.val_le_f huv.2]
    · simp[fromCirculation, fromCirculation_f, huv, F.nonneg]

lemma Flow.Circulation.toFlow_nonzero {F : Flow Pr} (c : F.Circulation v₀) : to_subflow F c ≠ 0 :=
  Flow.fromCirculation_nonzero c.circulation c.val.val c.toFlow_cap c.val.pos

def Flow.Circulation.make_saturating {F : Flow Pr} (c : F.Circulation v₀) : F.Circulation v₀ where
  val := c.val.make_saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup
  property := c.prop

lemma Flow.Circulation.make_saturating_Saturating {F : Flow Pr} (c : F.Circulation v₀) : c.make_saturating.val.Saturating :=
  (c.val.make_saturating_Saturating c.circulation.prop.not_nil c.circulation.prop.darts_nodup)

instance (F : Flow Pr) : MaintainsSaturation F (fun (p : F.Walk v v) ↦ p.walk.IsCirculation) where
  maintains_saturation c h := by
    obtain ⟨d, hd, hd'⟩ := h
    use d.fst, d.snd, lt_of_lt_of_le c.val.pos (c.val.val_le_f hd)
    have := Multiset.count_eq_one_of_mem c.prop.dart_counts_nodup hd
    simp[Flow.fromCirculation, Flow.fromCirculation_f, Flow.Circulation.circulation, d.is_adj, hd, ←hd', this]

@[simp]
theorem Flow.remove_circulation_value (F : Flow Pr) (c : F.Circulation v) : (F.remove_subflow_from c).value = F.value := by simp

theorem Flow.remove_circulation.ssubset (F : Flow Pr) (C : F.Circulation v) : F.remove_subflow_from C ⊂ F := by
  rw[remove_subflow_from]
  apply Flow.sub_ssubset_of_nonzero
  exact C.toFlow_nonzero

noncomputable def Flow.remove_all_circulations (F : Flow Pr) : Flow Pr :=
  if hF : F.CirculationFree then
    F
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    (F.remove_subflow_from c.make_saturating).remove_all_circulations
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_subflow_from_activeArcs_ssubset_of_saturating c.make_saturating c.make_saturating_Saturating

theorem Flow.remove_all_circulations.CirculationFree (F : Flow Pr) : F.remove_all_circulations.CirculationFree := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_true, hF]
    exact Flow.remove_all_circulations.CirculationFree ((F.remove_subflow_from c.make_saturating))
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_subflow_from_activeArcs_ssubset_of_saturating c.make_saturating c.make_saturating_Saturating

@[simp]
theorem Flow.remove_all_circulations.value (F : Flow Pr) : F.remove_all_circulations.value = F.value := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1: (remove_all_circulations (F.remove_subflow_from c.make_saturating)).value =  (F.remove_subflow_from c.make_saturating).value := by exact Flow.remove_all_circulations.value (F.remove_subflow_from c.make_saturating)
    have h2 : (F.remove_subflow_from c.make_saturating).value = F.value := by exact Flow.remove_circulation_value F c.make_saturating
    apply Eq.trans h1 h2
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_subflow_from_activeArcs_ssubset_of_saturating c.make_saturating c.make_saturating_Saturating

theorem Flow.remove_all_circulations.subset (F : Flow Pr) : F.remove_all_circulations ⊆ F := by
  unfold Flow.remove_all_circulations
  if hF : F.CirculationFree then
    simp only [dite_true, hF]
    exact Eq.subset' rfl
  else
    let c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hF
    simp only [dite_false, hF]
    have h1 := Flow.remove_all_circulations.subset (F.remove_subflow_from c.make_saturating)
    have h2 := subset_of_ssubset (Flow.remove_circulation.ssubset F c.make_saturating)
    exact subset_trans h1 h2
termination_by F.activeArcs.card
decreasing_by apply Finset.card_lt_card; exact F.remove_subflow_from_activeArcs_ssubset_of_saturating c.make_saturating c.make_saturating_Saturating

def Flow.Walk.transfer {F F' : Flow Pr} (p : F.Walk s t) (h : F ⊆ F') : F'.Walk s t :=
  { p with cap := (by intro d; exact le_trans (p.cap d) (h ..)) }

def Flow.Path.transfer {F F' : Flow Pr} (p : F.Path s t) (h : F ⊆ F') : F'.Path s t where
  val := p.val.transfer h
  property := p.property

theorem Flow.exists_path_to_of_flowIn_pos_of_circulationFree
    (F : Flow Pr)
    {t : V}
    (ht : 0 < flowIn F.f t)
    (hC : F.CirculationFree) :
    ∃ s, excess F.f s < 0 ∧ Nonempty (F.Path s t) :=
  build_path (Flow.Path.nil F 1 (by positivity))
where
  -- Recursive definition of the path: Given a path from some vertex v to the
  -- sink, we pick the next vertex u, add it to the front of the path and
  -- recurse until we arrive at the source.
  build_path {v} (path_so_far : F.Path v t) : ∃ s, excess F.f s < 0 ∧ Nonempty (F.Path s t) :=
    if hv : flowIn F.f v < flowOut F.f v then
      ⟨v, by unfold excess; linarith[hv], .intro path_so_far⟩
    else
      let valid_us := {u : V // 0 < F.f u v}
      have : Nonempty valid_us := by
        by_contra h
        simp only [valid_us, nonempty_subtype, not_exists, not_not] at h
        have hin : flowIn F.f v = 0 := Fintype.sum_eq_zero _ (by
          intro u
          exact le_antisymm (le_of_not_lt (h u)) (F.nonneg u v)
        )
        if hvt : v = t then
          subst hvt
          rw[hin] at ht
          exact lt_irrefl _ ht
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
          have : 0 < flowOut F.f v := lt_of_le_of_ne (F.flowOut_nonneg v) this.symm
          exact hv <| hin ▸ this

      let u := Classical.choice this
      let path_so_far_with_new_val := path_so_far.relax_val (F.f u v) u.prop
      have hval_le_uv : path_so_far_with_new_val.val.val ≤ F.f u v := min_le_right ..

      have : u.val ∉ path_so_far_with_new_val.val.walk.support := by
        intro hu
        let tail := path_so_far_with_new_val.takeUntil u hu
        have := Flow.Circulation.from_dart_and_path tail hval_le_uv
        exact (hC _).elim this
      let path_with_u : F.Path u t := Flow.Path.cons hval_le_uv this

      -- Proof for termination (the path got longer):
      have : Fintype.card V - path_with_u.val.walk.length < Fintype.card V - path_so_far.val.walk.length := by
        simp[Flow.Path.cons, Flow.Walk.cons, SimpleGraph.Walk.length_cons]
        exact Nat.sub_lt_sub_left path_so_far.prop.length_lt (Nat.lt.base _)

      build_path path_with_u
termination_by Fintype.card V - path_so_far.val.walk.length

theorem Flow.exists_path_of_value_pos_of_circulationFree
    (F : Flow Pr)
    (hF : 0 < F.value)
    (hC : F.CirculationFree) :
    F.Path Pr.s Pr.t := by
  apply Classical.choice
  have ht : 0 < flowIn F.f Pr.t := by
    rw[F.value_eq_excess_t, excess] at hF
    exact lt_of_lt_of_le hF <| sub_le_self _ <| F.flowOut_nonneg Pr.t
  obtain ⟨s, hs, hs'⟩ := F.exists_path_to_of_flowIn_pos_of_circulationFree ht hC
  suffices s = Pr.s from this ▸ hs'
  suffices s ≠ Pr.t from (F.eq_st_of_excess_nonzero hs.ne).resolve_right this
  exact lt_asymm (F.value_eq_excess_t ▸ hF) ∘ (· ▸ hs)

theorem Flow.exists_path_of_value_pos (F : Flow Pr) (hF : 0 < F.value) : F.Path Pr.s Pr.t :=
  let p := Flow.exists_path_of_value_pos_of_circulationFree
    F.remove_all_circulations
    (remove_all_circulations.value F ▸ hF)
    (remove_all_circulations.CirculationFree F)
  p.transfer $ remove_all_circulations.subset _

theorem Flow.value_nonzero_of_circulationFree_of_nonzero (F : Flow Pr) (hc : F.CirculationFree) (h : F ≠ 0) : F.value ≠ 0 := by
  have : ∃ u v, F.f u v ≠ 0 := by by_contra h0; simp at h0; absurd h; ext u v; exact h0 u v
  obtain ⟨u, v, huv⟩ := this
  have hv : 0 < flowIn F.f v := Fintype.sum_pos ⟨(F.nonneg · v), fun h ↦ huv <| le_antisymm (h u) (F.nonneg u v)⟩
  obtain ⟨s, hs, hs'⟩ := F.exists_path_to_of_flowIn_pos_of_circulationFree hv hc
  rw[Flow.value_eq_excess_t]
  if hs' : s = Pr.s then
    subst_vars
    linarith[F.excess_s_eq_neg_excess_t, hs]
  else if ht' : s = Pr.t then
    subst_vars
    linarith[hs]
  else
    absurd hs
    simp[F.conservation s ⟨hs', ht'⟩, excess]

@[simp]
theorem Flow.remove_path_value (F : Flow Pr) (p : F.Path Pr.s Pr.t) (hst : Pr.s ≠ Pr.t) :
    (F.remove_subflow_from p).value = F.value - p.val.val := by simp[hst]

theorem Flow.remove_backward_path_value (F : Flow Pr) (p : F.Path Pr.t Pr.s) (hst : Pr.s ≠ Pr.t) :
    (F.remove_subflow_from p).value = F.value + p.val.val := by simp[hst.symm]

inductive Flow.Decomposition : (F : Flow Pr) → Type (max (u_v + 1) (u_r + 1)) where
  | zero : Flow.Decomposition 0
  | path : {F : Flow Pr} → (p : F.Path Pr.s Pr.t) → (F.remove_subflow_from p).Decomposition → F.Decomposition
  | backwards_path : {F : Flow Pr} → (p : F.Path Pr.t Pr.s) → (F.remove_subflow_from p).Decomposition → F.Decomposition
  | circulation : {F : Flow Pr} → (v : V) → (c : F.Circulation v) → (F.remove_subflow_from c).Decomposition → F.Decomposition

def Flow.Decomposition.Saturating {F : Flow Pr} : F.Decomposition → Prop
  | zero => True
  | path p D => p.val.Saturating ∧ D.Saturating
  | backwards_path p D => p.val.Saturating ∧ D.Saturating
  | circulation _ c D => c.val.Saturating ∧ D.Saturating

abbrev Flow.SaturatingDecomposition (F : Flow Pr) := { D : F.Decomposition // D.Saturating }

noncomputable instance Flow.SaturatingDecomposition.instNonempty (F : Flow Pr) : Nonempty F.SaturatingDecomposition := by
  apply Nonempty.intro
  if h0 : F = 0 then
    subst h0
    exact ⟨.zero, .intro⟩
  else if hc : F.CirculationFree then
    have hv := F.value_nonzero_of_circulationFree_of_nonzero hc h0
    have hst := F.s_ne_t_of_value_nonzero hv
    if hv_pos : 0 < F.value then
      have p := F.exists_path_of_value_pos_of_circulationFree hv_pos hc
      have hp : ¬p.val.walk.Nil := SimpleGraph.Walk.not_nil_of_ne hst
      let F' := F.remove_subflow_from <| p.make_saturating hp
      have : F'.activeArcs.card < F.activeArcs.card := by
        apply Finset.card_lt_card
        exact F.remove_subflow_from_activeArcs_ssubset_of_saturating (p.make_saturating hp) (p.make_saturating_Saturating hp)
      have D := Classical.choice <| instNonempty F'
      exact ⟨.path (p.make_saturating hp) D, ⟨p.make_saturating_Saturating hp, D.prop⟩⟩
    else if hv_neg : F.value < 0 then
      have p := (F.reverse_problem.exists_path_of_value_pos_of_circulationFree (by linarith[hv_neg, F.value_reverse_problem]) hc.reverse_problem).reverse_problem
      simp only [F.reverse_problem_involutive, FlowProblem.reverse] at p
      have hp : ¬p.val.walk.Nil := SimpleGraph.Walk.not_nil_of_ne hst.symm
      let F' := F.remove_subflow_from <| p.make_saturating hp
      have : F'.activeArcs.card < F.activeArcs.card := by
        apply Finset.card_lt_card
        exact F.remove_subflow_from_activeArcs_ssubset_of_saturating (p.make_saturating hp) (p.make_saturating_Saturating hp)
      have D := Classical.choice <| instNonempty F'
      exact ⟨.backwards_path (p.make_saturating hp) D, ⟨p.make_saturating_Saturating hp, D.prop⟩⟩
    else
      exact False.elim <| hv <| le_antisymm (le_of_not_lt hv_pos) (le_of_not_lt hv_neg)
  else
    have c := Classical.choice $ not_isEmpty_iff.mp $ Classical.choose_spec $ not_forall.mp hc
    let F' := F.remove_subflow_from c.make_saturating
    have : F'.activeArcs.card < F.activeArcs.card := by
      apply Finset.card_lt_card
      exact F.remove_subflow_from_activeArcs_ssubset_of_saturating c.make_saturating c.make_saturating_Saturating
    have D := Classical.choice <| instNonempty F'
    exact ⟨.circulation _ c.make_saturating D, ⟨c.make_saturating_Saturating, D.prop⟩⟩
termination_by F.activeArcs.card

noncomputable instance {F : Flow Pr} : Nonempty F.Decomposition :=
  .intro (Classical.choice inferInstance : F.SaturatingDecomposition).val

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
  | zero => exact Pr.nullFlow_value ▸ h_right_nonneg
  | @path F p _ hF' =>
    let F' := F.remove_subflow_from p
    specialize hF' <| Finset.sum_nonneg (s := ds) (fun d _ ↦ F'.nonneg d.fst d.snd)

    obtain ⟨d, hd, hd'⟩ := hds p.path
    let u := d.fst
    let v := d.snd
    have hf : F'.f u v + p.val.val = F.f u v := by
      have hp : contains_edge p.path u v := ⟨d.is_adj, hd'⟩
      simp only [F', remove_subflow_from, to_subflow, Flow.sub, dite_false, hst, fromPath]
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
      _       ≤ ∑ d in ds', F.f  d.fst d.snd + F.f  u v             := by apply add_le_add_right; exact Finset.sum_le_sum <| fun d _ ↦ Flow.sub_subset ..
      _       = ∑ d in ds , F.f  d.fst d.snd                        := Finset.sum_erase_add ds _ hd
  | @backwards_path F p _ hF' =>
    let F' := F.remove_subflow_from p
    specialize hF' <| Finset.sum_nonneg (s := ds) (fun d _ ↦ F'.nonneg d.fst d.snd)
    calc
      F.value = F'.value - p.val.val        := by rw[F.remove_backward_path_value p hst]; ring
      _       ≤ F'.value                    := sub_le_self _ p.val.pos.le
      _       ≤ ∑ d in ds, F'.f d.fst d.snd := hF'
      _       ≤ ∑ d in ds, F.f d.fst d.snd  := Finset.sum_le_sum fun _ _ ↦ Flow.sub_subset ..
  | @circulation F v c _ hF' =>
    let F' := F.remove_subflow_from c
    specialize hF' <| Finset.sum_nonneg (s := ds) (fun d _ ↦ F'.nonneg d.fst d.snd)
    calc
      F.value = F'.value                    := (F.remove_circulation_value c).symm
      _       ≤ ∑ d in ds, F'.f d.fst d.snd := hF'
      _       ≤ ∑ d in ds, F.f d.fst d.snd  := Finset.sum_le_sum fun _ _ ↦ Flow.sub_subset ..

theorem value_le_f
    (d : N.asSimpleGraph.Dart)
    (hd : ∀ p : N.asSimpleGraph.Path Pr.s Pr.t, d ∈ p.val.darts) :
    F.value ≤ F.f d.fst d.snd :=
  le_of_le_of_eq
    (F.value_le_sum_f {d} fun p ↦ ⟨d, Finset.mem_singleton_self d, hd p⟩)
    (Finset.sum_singleton ..)

end Flow
