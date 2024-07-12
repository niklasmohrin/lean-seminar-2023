import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Cut

open BigOperators
open ContainsEdge

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
variable (N : Network V R)

variable {N} {Pr : FlowProblem N} (F : Flow Pr)

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
