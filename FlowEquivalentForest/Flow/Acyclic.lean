import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Flow.Path

open BigOperators
open ContainsEdge

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedField R]
variable {N : UndirectedNetwork V R} {Pr : FlowProblem N.toNetwork}

theorem Flow.value_le_sum_f
    (F : Flow Pr)
    (ds : Finset N.asSimpleGraph.Dart)
    (hds : ∀ p : N.asSimpleGraph.Path Pr.s Pr.t, ∃ d ∈ ds, d ∈ p.val.darts):
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
