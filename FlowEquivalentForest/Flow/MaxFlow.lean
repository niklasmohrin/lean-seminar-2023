import FlowEquivalentForest.Flow.Decomposition

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedField R]
variable {N : Network V R}

open BigOperators
open ContainsEdge

namespace FlowProblem

variable (Pr : FlowProblem N)

theorem exists_top : ∃ F : Flow Pr, IsTop F := sorry

noncomputable instance _root_.Flow.instOrderTop : OrderTop (Flow Pr) where
  top := Classical.choose Pr.exists_top
  le_top := Classical.choose_spec Pr.exists_top

noncomputable def maxFlow : R := (⊤ : Flow Pr).value

lemma maxFlow_nonneg : 0 ≤ Pr.maxFlow := by
  have := le_top (a := Pr.nullFlow)
  simp only [instPreorderFlow, Preorder.lift, nullFlow_value] at this
  exact this

end FlowProblem

namespace Network

variable (N : Network V R)

noncomputable def maxFlowValue (u v : V) := { s := u, t := v : FlowProblem N}.maxFlow
lemma maxFlowValue_nonneg (u v : V) : 0 ≤ N.maxFlowValue u v := { s := u, t := v : FlowProblem N}.maxFlow_nonneg

end Network

namespace UndirectedNetwork

variable (N : UndirectedNetwork V R)

lemma maxFlowValue_eq_zero_of_not_reachable
    {u v : V}
    (h : ¬N.asSimpleGraph.Reachable u v) :
    N.maxFlowValue u v = 0 := by
  let Pr : FlowProblem N.toNetwork := { s := u, t := v }
  by_contra hN
  let F := (⊤ : Flow Pr)
  have : 0 < F.value := Ne.lt_of_le' hN Pr.maxFlow_nonneg
  exact h $ (F.exists_path_of_value_pos this).path.val.reachable

theorem maxFlowValue_eq_bottleneck_of_isAcyclic
    (hG : N.asSimpleGraph.IsAcyclic)
    (P : N.asSimpleGraph.NonemptyPath u v) :
    N.maxFlowValue u v = N.bottleneck P := by
  let Pr : FlowProblem N.toNetwork := {s := u, t := v}

  suffices N.maxFlowValue u v ≤ N.bottleneck P by
    refine le_antisymm this ?_
    have := Flow.fromPath_value (Pr := Pr) P (N.bottleneck P) (le_of_lt <| N.bottleneck_pos P) le_rfl
    rw[←this]
    exact le_top (α := Flow Pr)

  suffices ∀ F : Flow Pr, F.value ≤ N.bottleneck P by simp_all only [Network.maxFlowValue, FlowProblem.maxFlow, Finset.mem_image, forall_exists_index, Finset.max'_le_iff, Finset.mem_univ, true_and, forall_apply_eq_imp_iff, implies_true]

  intro F
  obtain ⟨d, hd₁, hd₂⟩ := N.exists_bottleneck_dart P
  have hd₃ (P' : N.asSimpleGraph.Path u v) : d ∈ P'.val.darts := hG.path_unique P.path P' ▸ hd₁
  calc
    F.value ≤ F.f d.fst d.snd   := F.value_le_f d hd₃
    _       ≤ N.cap d.fst d.snd := F.capacity ..
    _       = N.bottleneck P    := hd₂

end UndirectedNetwork
