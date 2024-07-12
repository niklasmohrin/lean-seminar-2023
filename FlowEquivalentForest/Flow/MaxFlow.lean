import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Cut

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
variable {N : Network V R}

open BigOperators
open ContainsEdge

section HasMaxFlow

abbrev HasMaxFlow (N : Network V R) := (Pr : FlowProblem N) → OrderTop (Flow Pr)

variable [HasMaxFlow N]

namespace FlowProblem

variable (Pr : FlowProblem N)

noncomputable def maxFlow : R := (⊤ : Flow Pr).value

lemma maxFlow_nonneg : 0 ≤ Pr.maxFlow := by
  have := le_top (a := Pr.nullFlow)
  simp only [Flow.le_iff, nullFlow_value] at this
  exact this

end FlowProblem

namespace Network

variable (N)

noncomputable def maxFlowValue (u v : V) := { s := u, t := v : FlowProblem N}.maxFlow
lemma maxFlowValue_nonneg (u v : V) : 0 ≤ N.maxFlowValue u v := { s := u, t := v : FlowProblem N}.maxFlow_nonneg

end Network

namespace UndirectedNetwork

variable (N : UndirectedNetwork V R)

lemma flow_value_zero_of_not_reachable
    {Pr : FlowProblem N.toNetwork}
    (h : ¬N.asSimpleGraph.Reachable Pr.s Pr.t)
    (F : Flow Pr) :
    F.value = 0 := by
  by_contra hN
  absurd h
  wlog hst : Pr.s ≠ Pr.t
  · simp at hst; rw[hst]
  if hF : 0 < F.value then
    have p := F.exists_path_of_value_pos hF
    exact (p.path.val.transfer N.asSimpleGraph
      (N.mem_edgeSet_of_bottleneck_pos { path := p.path, ne := hst } <| p.bottleneck_pos hst)
    ).reachable
  else
    have : 0 ≤ F.reverse_problem.value := by simp[le_of_not_lt hF]
    have : 0 < F.reverse_problem.value := lt_of_le_of_ne this (by simp[hN])
    have := F.reverse_problem.exists_path_of_value_pos this
    have p := F.reverse_problem_involutive ▸ this.reverse_problem
    exact (p.path.val.transfer N.asSimpleGraph
      (N.mem_edgeSet_of_bottleneck_pos { path := p.path, ne := hst.symm } <| p.bottleneck_pos hst.symm)
    ).reachable.symm

theorem flow_value_le_bottleneck_of_isAcyclic
    (hG : N.asSimpleGraph.IsAcyclic)
    {Pr : FlowProblem N.toNetwork}
    (P : N.asSimpleGraph.NonemptyPath Pr.s Pr.t)
    (F : Flow Pr) :
    F.value ≤ N.bottleneck P.transfer_top := by
  open SimpleGraph in
  obtain ⟨d, hd₁, hd₂⟩ := N.exists_bottleneck_dart P.transfer_top
  refine calc
    F.value ≤ F.f d.fst d.snd             := F.value_le_f d ?_
    _       ≤ N.cap d.fst d.snd           := F.capacity ..
    _       = N.bottleneck P.transfer_top := hd₂
  intro p' hp'
  let p'' := p'.transfer N.asSimpleGraph <| N.mem_edgeSet_of_bottleneck_pos _ hp'
  have : p'' = P := by ext; simp[hG.path_unique p''.path P.path]
  subst this
  simp[p''] at hd₁
  rwa[← p'.path.val.transfer_mem_darts_iff d ⊤ le_top]

variable [HasMaxFlow N.toNetwork]

lemma maxFlowValue_eq_zero_of_not_reachable
    {u v : V}
    (h : ¬N.asSimpleGraph.Reachable u v) :
    N.maxFlowValue u v = 0 :=
  flow_value_zero_of_not_reachable (Pr := { s := u, t := v }) h ⊤

theorem maxFlowValue_eq_bottleneck_of_isAcyclic
    (hG : N.asSimpleGraph.IsAcyclic)
    (P : N.asSimpleGraph.NonemptyPath s t) :
    N.maxFlowValue s t = N.bottleneck P.transfer_top := by
  let Pr : FlowProblem N.toNetwork := {s, t}

  suffices N.maxFlowValue s t ≤ N.bottleneck P.transfer_top by
    apply le_antisymm this
    have := Flow.fromPath_value P.transfer_top (N.bottleneck P.transfer_top) (N.bottleneck_nonneg P.transfer_top) le_rfl
    rw[←this]
    exact le_top (α := Flow Pr)

  suffices ∀ F : Flow Pr, F.value ≤ N.bottleneck P.transfer_top by simp_all only [Network.maxFlowValue, FlowProblem.maxFlow, Finset.mem_image, forall_exists_index, Finset.max'_le_iff, Finset.mem_univ, true_and, forall_apply_eq_imp_iff, implies_true]
  intro F
  exact flow_value_le_bottleneck_of_isAcyclic hG (Pr := Pr) P F

end UndirectedNetwork

end HasMaxFlow

namespace Flow

variable {Pr : FlowProblem N} (F : Flow Pr)

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
    have : (Finset.univ.filter fun u ↦ g u v < g v u) ∪ (Finset.univ.filter fun u ↦ g v u < g u v) = (Finset.univ.filter fun u ↦ g u v ≠ g v u) := by simp[Finset.ext_iff]
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
    if hv' : v ∈ p.val.path.val.support then
      exact .intro <| {
        val := p.val.takeUntil v hv' (Ne.symm hv.left)
        property := lt_of_lt_of_le p.property <| F.residualNetwork.bottleneck_le_takeUntil p.val hv' (Ne.symm hv.left)
      }
    else
      exact .intro {
        val := p.val.concat hadj hv'
        property := by
          rw[F.residualNetwork.bottleneck_concat p.val hv']
          exact lt_min p.property hlt
      }

end Flow
