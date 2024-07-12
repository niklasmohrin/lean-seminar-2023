import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Cut

open BigOperators
open ContainsEdge

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
variable (N : Network V R)

def Network.activeArcs : Finset (NonDiag V) := Finset.univ.filter fun t ↦ 0 < N.cap t.fst t.snd

def Network.activePath (s t : V) := { p : (⊤ : SimpleGraph V).NonemptyPath s t // 0 < N.bottleneck p }

instance : Fintype (N.activePath s t) := Subtype.fintype _

variable {N} {Pr : FlowProblem N} (F : Flow Pr)

namespace Flow

theorem value_eq_flowOut_sub_flowIn_on (a : Finset V) (hs : Pr.s ∈ a) (ht : Pr.t ∉ a) :
    F.value = Finset.sum a (flowOut F.f) - Finset.sum a (flowIn F.f) := by
  have hst : Pr.s ≠ Pr.t := ht ∘ (· ▸ hs)

  have : a = (insert Pr.s a).erase Pr.t := by simp[hs, ht]
  rw[this]
  clear hs ht this
  induction a using Finset.induction_on with
  | empty =>
    have : Finset.erase {Pr.s} Pr.t = {Pr.s} := by simp[Ne.symm hst]
    simp[this, value]
  | @insert v a hv ih =>
    wlog hs : v ≠ Pr.s
    · simp at hs; simp[hs, ih]
    wlog ht : v ≠ Pr.t
    · simp at ht
      subst ht
      have : Pr.t ∉ insert Pr.s a := by simp[Finset.mem_insert, Ne.symm hst, hv]
      rw[Finset.Insert.comm, Finset.erase_insert this]
      simp[ih, Finset.sum_erase, this]
    rw[Finset.Insert.comm, Finset.erase_insert_of_ne ht]
    have : v ∉ (insert Pr.s a).erase Pr.t := by simp[hs, ht, hv]
    simp_rw[Finset.sum_insert this]
    rw[ih, F.conservation v ⟨hs, ht⟩]
    ring

theorem value_eq_flowOut_sub_flowIn_on' (a : Finset V) (hs : Pr.s ∈ a) (ht : Pr.t ∉ a) :
    F.value = ∑ u in a, ∑ v in aᶜ, F.f u v - ∑ u in aᶜ, ∑ v in a, F.f u v := by
  have := F.value_eq_flowOut_sub_flowIn_on a hs ht
  simp[flowOut, flowIn] at this
  conv at this => right; left; rw[Finset.sum_comm, ← Finset.sum_compl_add_sum a, Finset.sum_comm]; right; rw[Finset.sum_comm]
  conv at this => right; right; rw[Finset.sum_comm, ← Finset.sum_compl_add_sum a]
  ring_nf at this
  exact this

def residualNetwork : Network V R where
  cap u v := N.cap u v - F.f u v + F.f v u
  nonneg u v := by norm_num; linarith[N.nonneg u v, F.capacity u v, F.nonneg v u]
  loopless := by simp[N.loopless, F.loopless]

abbrev ResidualFlow := Flow ({ s := Pr.s, t := Pr.t : FlowProblem F.residualNetwork })

def add (F' : F.ResidualFlow) : Flow Pr where
  f u v := max 0 <| F.f u v + F'.f u v - F.f v u - F'.f v u
  nonneg _ _ := le_max_left 0 _
  capacity u v := by
    simp only [residualNetwork, max_le_iff, N.nonneg, tsub_le_iff_right, true_and]
    calc F.f u v + F'.f u v
      _ ≤ F.f u v + F.residualNetwork.cap u v     := by linarith[F'.capacity u v]
      _ = F.f u v + N.cap u v - F.f u v + F.f v u := by rw[residualNetwork]; ring
      _ = N.cap u v + F.f v u                     := by ring
      _ ≤ N.cap u v + F'.f v u + F.f v u          := by linarith[F'.nonneg v u]
  conservation v hv := by
    generalize hg : F.f + F'.f = g at *
    have hg' u v : max 0 (F.f u v + F'.f u v - F.f v u - F'.f v u) = max 0 (g u v - g v u) := by
      conv => right; right; simp[←hg, sub_add_eq_sub_sub]
    simp only [flowOut, flowIn, hg']
    clear hg'

    have h (f : V → R) : ∑ x, max 0 (f x) = ∑ x in Finset.univ.filter (0 < f ·), f x := by
      rw[Finset.sum_filter, Finset.sum_congr rfl]
      intro x _
      by_cases h : (0 < f x) <;> simp[h, le_of_lt, le_of_not_lt]

    simp[h, sub_eq_sub_iff_add_eq_add] 
    have : Disjoint (Finset.univ.filter fun u ↦ g u v < g v u) (Finset.univ.filter fun u ↦ g v u < g u v) := by
      intro s hs hs' u hu
      have h1 : g u v < g v u := (Finset.mem_filter.mp <| hs hu).right
      have h2 : g v u < g u v := (Finset.mem_filter.mp <| hs' hu).right
      exact False.elim <| lt_asymm h1 h2
    rw[←Finset.sum_union this, ←Finset.sum_union this.symm]
    have : (Finset.univ.filter fun u ↦ g u v < g v u) ∪ (Finset.univ.filter fun u ↦ g v u < g u v) = (Finset.univ.filter fun u ↦ g u v ≠ g v u) := sorry
    rw[this, Finset.union_comm, this]
    suffices ∑ u, g u v = ∑ u, g v u by
      let eqs := Finset.univ.filter (fun u ↦ g u v = g v u)
      simp only [←Finset.sum_add_sum_compl eqs] at this
      have heqs : ∑ u in eqs, g u v = ∑ u in eqs, g v u := Finset.sum_congr rfl fun u hu ↦ by simpa [eqs, Finset.mem_filter] using hu
      simp[heqs, eqs] at this
      linarith[heqs, this]
    subst g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw[← flowOut, ←flowOut, ← flowIn, ← flowIn, F.conservation v hv, F'.conservation v hv]

def augment_with (p : (completeGraph V).NonemptyPath Pr.s Pr.t) : Flow Pr :=
  F.add <| Flow.fromPath
    p
    (F.residualNetwork.bottleneck p)
    (F.residualNetwork.bottleneck_nonneg p)
    le_rfl

theorem isTop_of_not_exists_active_path (h : IsEmpty (F.residualNetwork.activePath Pr.s Pr.t)) : IsTop F := by
  wlog hst : Pr.s ≠ Pr.t
  · simp only [ne_eq, not_not] at hst; intro F'; simp[Flow.value_eq_zero_of_s_eq_t, hst]

  classical
  let c : Cut Pr := {
    left := Finset.univ.filter fun v ↦ v = Pr.s ∨ Nonempty (F.residualNetwork.activePath Pr.s v),
    s_mem := by simp,
    t_not_mem := by simp[hst.symm, h]
  }

  suffices F.value = c.value by simp[IsTop, this, c.bounds_flow]

  rw[F.value_eq_flowOut_sub_flowIn_on' c.left c.s_mem c.t_not_mem]
  suffices hc : (∀ u v, u ∈ c.left → v ∈ c.right → F.f u v = N.cap u v ∧ F.f v u = 0) by
    rw[Cut.value, Cut.right, ←Finset.sum_product', Finset.sum_comm, ←Finset.sum_product', ←Finset.sum_sub_distrib, ←Finset.sum_product']
    apply Finset.sum_congr rfl
    intro (u, v) huv
    rw[Finset.mem_product] at huv
    linarith[hc u v huv.left huv.right]

  intro u v hu hv
  have hadj : (completeGraph V).Adj u v := Finset.mem_compl.mp hv ∘ (· ▸ hu)
  simp[not_or] at hu hv

  suffices F.residualNetwork.cap u v = 0 by
    simp[residualNetwork] at this
    have h := le_antisymm (F.capacity u v) (by linarith[this, F.nonneg v u])
    exact ⟨h, by linarith[h, this]⟩

  by_contra hne
  have hlt : 0 < F.residualNetwork.cap u v := lt_of_le_of_ne'
    (by simp[residualNetwork]; linarith[F.capacity u v, F.nonneg v u, N.nonneg u v])
    hne

  absurd hv.right
  simp only [not_and, not_isEmpty_iff]
  if hs : u = Pr.s then
    generalize Pr.s = s at hs ⊢
    subst s
    exact .intro {
      val := hadj.toNonemptyPath
      property := by simpa[F.residualNetwork.bottleneck_single_edge hadj, residualNetwork]
    }
  else
    have p := Classical.choice <| hu.resolve_left hs
    exact .intro {
      val := {
        path := {
          val := p.val.path.val.concat hadj
          property := sorry
        }
        ne := Ne.symm hv.left
      }
      property := sorry
    }

end Flow

noncomputable section dinitz

namespace Network

variable (N)

def dist (u v : V) :=
  Finset.min <| Finset.univ.image fun (p : N.activePath u v) ↦ p.val.path.val.length

lemma exists_residualPath_of_dist_ne_top (h : N.dist u v ≠ ⊤) :
    ∃ p : N.activePath u v, p.val.path.val.length = (N.dist u v).untop h := by
  have : (Finset.univ (α := N.activePath u v)).Nonempty := by
    by_contra hempty
    absurd h
    simp at hempty
    rw[dist, Finset.min_eq_top, hempty, Finset.image_empty]
  rw[←Finset.image_nonempty (f := (·.val.path.val.length))] at this
  obtain ⟨l, hl⟩ := Finset.min_of_nonempty this
  have := Finset.mem_of_min hl
  rw[Finset.mem_image] at this
  obtain ⟨p, _, hp⟩ := this
  use p
  simp[hp, dist, hl]

def levelNetwork s := N.filter fun u v ↦ N.dist s v = N.dist s u + 1

end Network

namespace Flow

def IsBlocking := ∀ p : N.activePath Pr.s Pr.t, ∃ d ∈ p.val.path.val.darts, F.f d.fst d.snd = N.cap d.fst d.snd

abbrev LevelFlow := Flow { s := Pr.s, t := Pr.t : FlowProblem (F.residualNetwork.levelNetwork Pr.s) }

def LevelFlow.toResidualFlow (F' : F.LevelFlow) : F.ResidualFlow where
  f := F'.f
  nonneg := F'.nonneg
  conservation := F'.conservation
  capacity := sorry

lemma foo {a b : R} : a - max 0 b + max 0 (-b) = a - b := by by_cases h : 0 ≤ b; simp[h]; simp at h; simp[h.le]; ring

private theorem dist_le_add_dist_of_isBlocking
    (hF : F.residualNetwork.dist Pr.s v ≠ ⊤)
    {F' : F.LevelFlow}
    (hF' : F'.IsBlocking) :
    F.residualNetwork.dist Pr.s v ≤ (F.add F'.toResidualFlow).residualNetwork.dist Pr.s v := by
  rw[← WithTop.coe_untop _ hF]
  wlog hdist : (F.add F'.toResidualFlow).residualNetwork.dist Pr.s v ≠ ⊤
  · simp only [ne_eq, not_not] at hdist; rw[hdist]; exact le_top
  obtain ⟨⟨p, hpb⟩, hpl⟩ := (F.add F'.toResidualFlow).residualNetwork.exists_residualPath_of_dist_ne_top hdist
  rw[← WithTop.coe_untop _ hdist, ←hpl, WithTop.coe_le_coe]
  simp only
  sorry

  -- rw[← WithTop.coe_untop _ hdist, ←hpl, WithTop.coe_le_coe]
  -- induction p using SimpleGraph.NonemptyPath.ind with
  -- | base h => sorry
  -- | ind _ => sorry

private theorem dist_lt_add_dist_of_isBlocking (hF : F.residualNetwork.dist Pr.s Pr.t ≠ ⊤) {F' : F.LevelFlow} (hF' : F'.IsBlocking) :
    F.residualNetwork.dist Pr.s Pr.t < (F.add F'.toResidualFlow).residualNetwork.dist Pr.s Pr.t := by
  apply lt_of_le_of_ne <| F.dist_le_add_dist_of_isBlocking hF hF'
  rw[← WithTop.coe_untop _ hF]

  intro heq
  absurd hF'

  obtain ⟨⟨p, hpb⟩, hpl⟩ := (F.add F'.toResidualFlow).residualNetwork.exists_residualPath_of_dist_ne_top (by
    rw[←heq]
    exact WithTop.coe_ne_top
  )
  simp[IsBlocking]

  let p' : (F.residualNetwork.levelNetwork Pr.s).activePath Pr.s Pr.t := {
    val := p
    property := by
      apply lt_of_lt_of_eq hpb
      apply Eq.symm
      unfold Network.levelNetwork
      -- apply F.residualNetwork.bottleneck_filter_eq_of_forall p
      sorry
  }
  obtain ⟨d, hd, hd'⟩ := hF' p'
  -- have hN : 0 < N.cap u v := sorry
  have : (F.add F'.toResidualFlow).residualNetwork.cap d.fst d.snd = 0 := by
    simp[residualNetwork, add, LevelFlow.toResidualFlow]
    have : F.f d.snd d.fst + F'.f d.snd d.fst - F.f d.fst d.snd - F'.f d.fst d.snd = -(F.f d.fst d.snd + F'.f d.fst d.snd - F.f d.snd d.fst - F'.f d.snd d.fst) := by ring
    simp only [this, foo]
    simp only [residualNetwork] at hd'
    rw[hd']
    ring_nf

    -- simp only [add] at hd'
  have : (F.add F').residualNetwork.bottleneck p = 0 := sorry
  exact hpb.ne this.symm

  -- use {
  --   val := p
  --   property := sorry
  -- }
  -- intro d hd
  -- let (u, v) := d.toProd
  -- apply ne_of_lt
  -- have := (F.add F').residualNetwork.bottleneck_le_dart _ hd
  -- have := lt_of_lt_of_le hpb this
  -- simp only [residualNetwork, add] at this ⊢
  -- -- a - (max 0 b) + (max 0 -b) = a - b + 0 (b >= 0) or a - 0 + -b (b < 0) = a - b
  -- let x := F.f u v + F'.f u v - F.f v u - F'.f v u
  -- have : x < N.cap u v := sorry
  -- rw[max_lt_iff]
  -- constructor
  -- · exact hpb
  -- · exact this
  -- apply lt_of_sub_pos
  -- calc 0
  --   _ < N.cap u v - x := this
  --   _ = N.cap u v - F.f u v - F'.f u v + F.f v u + F'.f v u := by simp[x]; ring
  --   _ = N.cap u v - F.f u v - F'.f u v + F.f v u            := sorry
  --   _ = F.residualNetwork.cap u v - F'.f u v := by simp[residualNetwork]; ring

private abbrev dinitz_loop_size := Fintype.card V - (F.dist Pr.s Pr.t).untop' (Fintype.card V)
lemma dinitz_loop_decreasing_by (hF : F.dist Pr.s Pr.t ≠ ⊤) (hF' : F.IsBlocking F') :
    (F.add F').dinitz_loop_size < F.dinitz_loop_size := by
  have hdist := F.dist_lt_add_dist_of_isBlocking hF hF'
  simp only [dinitz_loop_size] at hdist ⊢
  have F_dist_lt_length : (F.dist Pr.s Pr.t).untop hF < Fintype.card V := by
    obtain ⟨p, hp⟩ := F.exists_residualPath_of_dist_ne_top hF
    rw[←hp]
    exact p.val.path.prop.length_lt
  rw[←WithTop.coe_untop _ hF, WithTop.untop'_coe]
  apply Nat.sub_lt_sub_left F_dist_lt_length
  rw[WithTop.lt_untop'_iff]
  · simp[hdist]
  · intro; exact F_dist_lt_length

instance : Decidable (∃ F', F.IsBlocking F') := Classical.dec _

def dinitz_loop (F : Flow Pr) : Flow Pr := 
  if h : ∃ F', F.IsBlocking F' then -- TODO: rephrase
    dinitz_loop <| F.add <| Classical.choose h 
  else
    F
termination_by F.dinitz_loop_size
decreasing_by exact F.dinitz_loop_decreasing_by sorry (Classical.choose_spec h)

lemma dinitz_loop_idempotent (F : Flow Pr) : dinitz_loop (dinitz_loop F) = dinitz_loop F := by
  nth_rw 3 [dinitz_loop]
  nth_rw 2 [dinitz_loop]
  by_cases h : ∃ F', F.IsBlocking F'
  · simp[h]; exact dinitz_loop_idempotent _
  · simp[h]; rw[dinitz_loop]; simp[h]
termination_by F.dinitz_loop_size
decreasing_by exact F.dinitz_loop_decreasing_by (Classical.choose_spec h)

def dinitz (Pr : FlowProblem N) : Flow Pr := dinitz_loop 0

-- theorem dinitz_isTop : IsTop (dinitz Pr) := by
--   apply isTop_of_not_exists_active_path
--   rw[dinitz, isEmpty_iff]
--   have : ¬ ∃ F', (dinitz Pr).IsBlocking F' := by
--     intro h
--     have : dinitz.loop Pr (dinitz Pr) ≠ dinitz Pr := by
--       rw[dinitz.loop]; simp[h]; sorry
--       -- rw[dinitz]; nth_rw 2 [dinitz.loop]
--     simp[dinitz] at this
--     exact this <| dinitz_loop_idempotent Pr _
--   intro p
--   sorry

end dinitz

-- theorem ford_isTop : IsTop F.ford := by
--   let c : Cut Pr := {
--     s := Finset.univ.filter fun v ↦ ∃ p : (completeGraph V).NonemptyPath Pr.s v, 0 < F.ford.residualNetwork.bottleneck
--   }

end Flow