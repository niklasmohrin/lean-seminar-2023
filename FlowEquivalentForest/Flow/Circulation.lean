import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation

open BigOperators
open ContainsEdge

variable
  {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {G : UndirectedNetwork V}
  {Pr : FlowProblem G.toNetwork}

noncomputable instance {G : SimpleGraph V} {c : G.Circulation v0} {u v : V} : Decidable (contains_edge c u v) := Classical.dec _

@[simp]
noncomputable abbrev Flow.UnitCirculation_f (c : G.asSimpleGraph.Circulation v₀) (u v : V) := if contains_edge c u v then 1 else 0

lemma Flow.UnitCirculation_f_flowOut_eq_flowIn (c : G.asSimpleGraph.Circulation v₀) (v : V) : flowOut (Flow.UnitCirculation_f c) v = flowIn (Flow.UnitCirculation_f c) v := by
  if h_sup : v ∈ c.val.support then
    have h_out : flowOut (fun u v ↦ if contains_edge c u v then 1 else 0) v = 1 := by
      obtain ⟨w, hw_succ, hw_uniq⟩ := c.succ_exists h_sup
      have h1 : (if contains_edge c v w then 1 else 0) = 1 := by
        simp only [hw_succ, ite_true]
      unfold flowOut
      nth_rw 2 [← h1]
      refine Finset.sum_eq_single (β := ℕ) (a := w) ?_ ?_
      · intro b _ hb1
        have : ¬contains_edge c v b := by
          intro h
          exact hb1 (hw_uniq b h)
        simp only [this, ite_false]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    have h_in : flowIn (fun u v ↦ if contains_edge c u v then 1 else 0) v = 1 := by
      obtain ⟨u, hu_pred, hu_uniq⟩ := c.pred_exists h_sup
      have h1 : (if contains_edge c u v then 1 else 0) = 1 := by
        simp only [hu_pred, ite_true]
      nth_rw 2 [← h1]
      refine Finset.sum_eq_single (β := ℕ) (a := u) ?_ ?_
      · intro b _ hb1
        have : ¬contains_edge c b v := by
          intro h
          exact hb1 (hu_uniq b h)
        simp only [this, ite_false]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    rw [h_out, h_in]
  else
    have h_out : flowOut (fun u v ↦ if contains_edge c u v then 1 else 0) v = 0 := by
      have c_false (w : V) : contains_edge c v w = False := by
        by_contra h_c
        apply h_sup
        have hh :contains_edge c v w := by                  simp_all only [ne_eq, instContainsEdgeWalk, eq_iff_iff,iff_false, not_exists, not_forall, not_not]
        have ⟨  h_adj, hi⟩   :=  hh
        have blub := c.val.dart_fst_mem_support_of_mem_darts hi
        simp_all only [ne_eq, instContainsEdgeWalk, eq_iff_iff, iff_false, not_true_eq_false,
          not_false_eq_true, exists_const]
      have c_false_all : ∀ w, contains_edge c v w = False := by
        intro u
        exact c_false u
      unfold flowOut
      have c_false2 : ∀ w, (fun u v ↦ if contains_edge c u v then 1 else 0) v w = 0 := by
        intro u
        simp only [c_false, ite_false]
      apply Finset.sum_eq_zero
      intro u _
      simp_all only [ne_eq, instContainsEdgeWalk, forall_const, eq_iff_iff, iff_false,
        not_exists]
    have h_in : flowIn (fun u v ↦ if contains_edge c u v then 1 else 0) v = 0 := by
      have c_false (u : V) : contains_edge c u v = False := by
        by_contra h_c
        apply h_sup
        have hh :contains_edge c u v := by
          simp_all only [ne_eq, instContainsEdgeWalk, eq_iff_iff,iff_false, not_exists, not_forall, not_not]
        have ⟨  h_adj, hi⟩   :=  hh
        have blub := c.val.dart_snd_mem_support_of_mem_darts hi
        simp_all only [ne_eq, instContainsEdgeWalk, eq_iff_iff, iff_false, not_true_eq_false,
          not_false_eq_true, exists_const]
      have c_false_all : ∀ u, contains_edge c u v = False := by
        intro u
        exact c_false u
      unfold flowIn
      have c_false2 : ∀ u, (fun u v ↦ if contains_edge c u v then 1 else 0) u v = 0 := by
        intro u
        simp only [c_false, ite_false]
      apply Finset.sum_eq_zero
      intro u _
      simp_all only [ne_eq, instContainsEdgeWalk, forall_const, eq_iff_iff, iff_false,
        not_exists]
    rw [h_out, h_in]

noncomputable def Flow.UnitCirculation (c : G.asSimpleGraph.Circulation v0) : Flow Pr where
  f := Flow.UnitCirculation_f c
  conservation v _ := UnitCirculation_f_flowOut_eq_flowIn c v
  capacity := by
    intro u v
    sorry

theorem Flow.UnitCirculation_value_zero (c : G.asSimpleGraph.Circulation v₀) :
    (Flow.UnitCirculation (Pr := Pr) c).value = 0 := by
  rw [value, UnitCirculation]
  rw [Flow.UnitCirculation_f_flowOut_eq_flowIn c Pr.s]
  exact Nat.sub_self (flowIn (UnitCirculation_f c) Pr.s)

theorem Flow.UnitCirculation_nonzero (c : G.asSimpleGraph.Circulation v₀) :
    (Flow.UnitCirculation (Pr := Pr) c) ≠ 0 := by
  let d := c.val.firstDart c.prop.not_nil
  suffices UnitCirculation_f c d.fst d.snd ≠ 0 by
    intro h
    injection h with f_eq
    rw[f_eq] at this
    contradiction
  simp only [UnitCirculation_f, SimpleGraph.Walk.firstDart_toProd, ne_eq, ite_eq_right_iff, imp_false, not_not]
  use d.is_adj
  exact c.val.firstDart_mem_darts c.prop.not_nil

theorem Flow.UnitCirculation_not_backward (c : G.asSimpleGraph.Circulation v₀) :
    ¬(Flow.UnitCirculation (Pr := Pr) c).Backward := by
  rw [Backward, UnitCirculation, not_lt, Flow.UnitCirculation_f_flowOut_eq_flowIn c Pr.s]
