import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.Flow.Decomposition
import FlowEquivalentForest.Flow.Path

open ContainsEdge

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {N : UndirectedNetwork V} {Pr : FlowProblem N.toNetwork}

theorem Flow.value_le_f
    (F : Flow Pr)
    (d : N.asSimpleGraph.Dart)
    (hd : ∀ p : N.asSimpleGraph.Path Pr.s Pr.t, d ∈ p.val.darts):
    F.value ≤ F.f d.fst d.snd := by
  wlog hst : Pr.s ≠ Pr.t
  · exact F.value_eq_zero_of_s_eq_t (not_ne_iff.mp hst) ▸ zero_le _

  let u := d.fst
  let v := d.snd

  suffices ∀ n, ∀ F : Flow Pr, F.value = n → F.value ≤ F.f u v from this F.value F rfl

  intro n
  induction n with
  | zero => intro F hF; linarith[hF]
  | succ n ih =>
    intro F hF
    obtain p := F.exists_path_of_value_nonzero (by linarith)
    let F' := F.remove_path p
    have hF' : F'.value = n := by rw[Flow.remove_path.value F p, hF]; rfl
    have hf : F'.f u v + 1 = F.f u v := by
      have hp : contains_edge p.path u v := ⟨d.is_adj, (hd p.path)⟩
      simp only [F', remove_path, Flow.sub, dite_false, hst, fromPath]
      -- annoyingly, we cannot use hp directly because the function subtraction
      -- is not evaluated in the goal, so we need to do that first
      simp only [HSub.hSub, Sub.sub, hp, ite_true]
      have : F.f u v ≠ 0 := by
        by_contra h₀
        have h := h₀ ▸ p.val.prop d
        simp[SimpleGraph.Walk.dart_counts] at h
        exact List.not_mem_of_count_eq_zero h $ hd p.path

      exact Nat.succ_pred this

    calc
      F.value = F'.value + 1 := by rw[hF, hF']
      _       ≤ F'.f u v + 1 := Nat.add_le_add_right (ih F' hF') 1
      _       = F.f u v      := hf

theorem Acyclic_Path_maxflow_eq_bottleneck
    (G : UndirectedNetwork V)
    (hG : G.asSimpleGraph.IsAcyclic)
    (P : G.asSimpleGraph.NonemptyPath u v) :
    G.maxFlowValue u v = G.bottleneck P := by
  let Pr : FlowProblem G.toNetwork := {s := u, t := v}

  suffices G.maxFlowValue u v ≤ G.bottleneck P by
    refine Nat.le_antisymm this ?_
    have := Flow.fromPath_value (Pr := Pr) P (G.bottleneck P) (le_refl _)
    rw[←this]
    apply Finset.le_max'
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]

  suffices ∀ F : Flow Pr, F.value ≤ G.bottleneck P by simp_all only [Network.maxFlowValue, FlowProblem.maxFlow, Finset.mem_image, forall_exists_index, Finset.max'_le_iff, Finset.mem_univ, true_and, forall_apply_eq_imp_iff, implies_true]

  intro F
  obtain ⟨d, hd₁, hd₂⟩ := G.exists_bottleneck_dart P
  have hd₃ (P' : G.asSimpleGraph.Path u v) : d ∈ P'.val.darts := hG.path_unique P.path P' ▸ hd₁
  calc
    F.value ≤ F.f d.fst d.snd   := F.value_le_f d hd₃
    _       ≤ G.cap d.fst d.snd := F.capacity ..
    _       = G.bottleneck P    := hd₂
