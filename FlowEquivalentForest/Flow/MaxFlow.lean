import FlowEquivalentForest.Flow.Decomposition

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
variable {N : Network V R}

open BigOperators
open ContainsEdge

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
  if hF : 0 < F.value then
    exact (F.exists_path_of_value_pos hF).path.val.reachable
  else
    have : 0 ≤ F.reverse_problem.value := by simp[le_of_not_lt hF]
    have : 0 < F.reverse_problem.value := lt_of_le_of_ne this (by simp[hN])
    have := F.reverse_problem.exists_path_of_value_pos this
    have := F.reverse_problem_involutive ▸ this.reverse_problem
    exact this.path.val.reachable.symm

theorem flow_value_le_bottleneck_of_isAcyclic
    (hG : N.asSimpleGraph.IsAcyclic)
    {Pr : FlowProblem N.toNetwork}
    (P : N.asSimpleGraph.NonemptyPath Pr.s Pr.t)
    (F : Flow Pr) :
    F.value ≤ N.bottleneck P := by
  obtain ⟨d, hd₁, hd₂⟩ := N.exists_bottleneck_dart P
  have hd₃ (P' : N.asSimpleGraph.Path _ _) : d ∈ P'.val.darts := hG.path_unique P.path P' ▸ hd₁
  calc
    F.value ≤ F.f d.fst d.snd   := F.value_le_f d hd₃
    _       ≤ N.cap d.fst d.snd := F.capacity ..
    _       = N.bottleneck P    := hd₂

variable [HasMaxFlow N.toNetwork]

lemma maxFlowValue_eq_zero_of_not_reachable
    {u v : V}
    (h : ¬N.asSimpleGraph.Reachable u v) :
    N.maxFlowValue u v = 0 :=
  flow_value_zero_of_not_reachable (Pr := { s := u, t := v }) h ⊤

theorem maxFlowValue_eq_bottleneck_of_isAcyclic
    (hG : N.asSimpleGraph.IsAcyclic)
    (P : N.asSimpleGraph.NonemptyPath u v) :
    N.maxFlowValue u v = N.bottleneck P := by
  let Pr : FlowProblem N.toNetwork := {s := u, t := v}

  suffices N.maxFlowValue u v ≤ N.bottleneck P by
    refine le_antisymm this ?_
    have := Flow.fromPath_value P (N.bottleneck P) (le_of_lt <| N.bottleneck_pos P) le_rfl
    rw[←this]
    exact le_top (α := Flow Pr)

  suffices ∀ F : Flow Pr, F.value ≤ N.bottleneck P by simp_all only [Network.maxFlowValue, FlowProblem.maxFlow, Finset.mem_image, forall_exists_index, Finset.max'_le_iff, Finset.mem_univ, true_and, forall_apply_eq_imp_iff, implies_true]
  intro F
  exact flow_value_le_bottleneck_of_isAcyclic hG (Pr := Pr) P F

end UndirectedNetwork
