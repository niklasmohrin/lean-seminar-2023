import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Flow.Path

open ContainsEdge

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedField R]
variable {N : UndirectedNetwork V R} {Pr : FlowProblem N.toNetwork}

theorem Flow.value_le_f
    (F : Flow Pr)
    (d : N.asSimpleGraph.Dart)
    (hd : ∀ p : N.asSimpleGraph.Path Pr.s Pr.t, d ∈ p.val.darts):
    F.value ≤ F.f d.fst d.snd := by
  wlog hst : Pr.s ≠ Pr.t
  · exact F.value_eq_zero_of_s_eq_t (not_ne_iff.mp hst) ▸ F.nonneg ..

  have D : F.Decomposition := Classical.choice inferInstance
  induction D with
  | nil => exact Pr.nullFlow_value ▸ (0 : Flow Pr).nonneg ..
  | @cons F p D' hF' =>
    wlog h_value : 0 ≤ F.value
    · exact le_trans (le_of_not_le h_value) (F.nonneg ..)

    let F' := F.remove_path p
    let u := d.fst
    let v := d.snd
    have hf : F'.f u v + p.val.val = F.f u v := by
      have hp : contains_edge p.path u v := ⟨d.is_adj, (hd p.path)⟩
      simp only [F', remove_path, Flow.sub, dite_false, hst, fromPath]
      -- annoyingly, we cannot use hp directly because the function subtraction
      -- is not evaluated in the goal, so we need to do that first
      simp only [HSub.hSub, Sub.sub, hp, ite_true]
      exact add_eq_of_eq_sub rfl

    calc
      F.value = F'.value + p.val.val := by rw[F.remove_path_value p hst]; ring
      _       ≤ F'.f u v + p.val.val := add_le_add_right hF' _
      _       = F.f u v              := hf

theorem Acyclic_Path_maxflow_eq_bottleneck
    (G : UndirectedNetwork V)
    (hG : G.asSimpleGraph.IsAcyclic)
    (P : G.asSimpleGraph.NonemptyPath u v) :
    G.maxFlowValue u v = G.bottleneck P := by
  let Pr : FlowProblem G.toNetwork := {s := u, t := v}

  suffices G.maxFlowValue u v ≤ G.bottleneck P by
    refine le_antisymm this ?_
    have := Flow.fromPath_value (Pr := Pr) P (G.bottleneck P) (le_of_lt <| G.bottleneck_pos P) le_rfl
    rw[←this]
    exact le_top (α := Flow Pr)

  suffices ∀ F : Flow Pr, F.value ≤ G.bottleneck P by simp_all only [Network.maxFlowValue, FlowProblem.maxFlow, Finset.mem_image, forall_exists_index, Finset.max'_le_iff, Finset.mem_univ, true_and, forall_apply_eq_imp_iff, implies_true]

  intro F
  obtain ⟨d, hd₁, hd₂⟩ := G.exists_bottleneck_dart P
  have hd₃ (P' : G.asSimpleGraph.Path u v) : d ∈ P'.val.darts := hG.path_unique P.path P' ▸ hd₁
  calc
    F.value ≤ F.f d.fst d.snd   := F.value_le_f d hd₃
    _       ≤ G.cap d.fst d.snd := F.capacity ..
    _       = G.bottleneck P    := hd₂
