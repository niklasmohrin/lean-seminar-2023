import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Cut

open BigOperators
open ContainsEdge

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
variable (N : Network V R)

def Network.activeArcs : Finset (NonDiag V) := Finset.univ.filter fun t ↦ 0 < N.cap t.fst t.snd
def Network.activePath (s t : V) := { p : (completeGraph V).NonemptyPath s t // 0 < N.bottleneck p }

namespace Flow

variable {N} {Pr : FlowProblem N} (F : Flow Pr)

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

def add (F' : Flow ({ s := Pr.s, t := Pr.t : FlowProblem F.residualNetwork })) : Flow Pr where
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

    have h (f : V → R) : ∑ x, max 0 (f x) = ∑ x in Finset.univ.filter (0 < f ·), f x := sorry
    simp[h, sub_eq_sub_iff_add_eq_add] 
    have : Disjoint (Finset.univ.filter fun u ↦ g u v < g v u) (Finset.univ.filter fun u ↦ g v u < g u v) := sorry
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

theorem augment_with_residualNetwork_activeArcs_ssubset
    (p : (completeGraph V).NonemptyPath Pr.s Pr.t)
    (hp : 0 < F.residualNetwork.bottleneck p) :
    (F.augment_with p).residualNetwork.activeArcs ⊂ F.residualNetwork.activeArcs := by
  simp only [augment_with, add, residualNetwork, Network.activeArcs, fromPath]
  apply ssubset_of_subset_of_ne
  · intro a ha
    if h : contains_edge p.path a.fst a.snd then
      simp only [Finset.mem_filter, ite_true, h] at ha ⊢
      sorry
    else
      simp[h]
      sorry
  · sorry

noncomputable def ford (F : Flow Pr) : Flow Pr := by
  classical
  if h : ∃ (p : (completeGraph V).NonemptyPath Pr.s Pr.t), 0 < F.residualNetwork.bottleneck p then
    let p := Classical.choose h
    have : (F.augment_with p).residualNetwork.activeArcs.card < F.residualNetwork.activeArcs.card := by
      apply Finset.card_lt_card
      exact F.augment_with_residualNetwork_activeArcs_ssubset p <| Classical.choose_spec h
    exact (F.augment_with p).ford
  else
    exact F
termination_by F.residualNetwork.activeArcs.card

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

-- theorem ford_isTop : IsTop F.ford := by
--   let c : Cut Pr := {
--     s := Finset.univ.filter fun v ↦ ∃ p : (completeGraph V).NonemptyPath Pr.s v, 0 < F.ford.residualNetwork.bottleneck
--   }

end Flow
