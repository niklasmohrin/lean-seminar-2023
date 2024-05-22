import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation

open BigOperators
open ContainsEdge

variable
  {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {N : UndirectedNetwork V}
  {Pr : FlowProblem N.toNetwork}

@[simp]
abbrev Flow.UnitCirculation_f (c : N.asSimpleGraph.Circulation v₀) (u v : V) : ℤ := if contains_edge c u v then 1 else 0

lemma Flow.UnitCirculation_f_flowOut_eq_flowIn (c : N.asSimpleGraph.Circulation v₀) (v : V) : flowOut (Flow.UnitCirculation_f c) v = flowIn (Flow.UnitCirculation_f c) v := by
  simp only [flowOut, flowIn, UnitCirculation_f]
  if h_sup : v ∈ c.val.support then
    obtain ⟨u, hu_pred, hu_uniq⟩ := c.pred_exists h_sup
    obtain ⟨w, hw_succ, hw_uniq⟩ := c.succ_exists h_sup
    rw[Finset.sum_eq_single w, Finset.sum_eq_single u]
    · simp only [hu_pred, hw_succ]
    · intro u' _ hu'; simp; by_contra h; exact hu' <| hu_uniq u' h
    · intro h; exact False.elim <| h <| Finset.mem_univ u
    · intro w' _ hw'; simp; by_contra h; exact hw' <| hw_uniq w' h
    · intro h; exact False.elim <| h <| Finset.mem_univ w
  else
    rw[Finset.sum_eq_zero, Finset.sum_eq_zero]
    · simp; intro u hu; exact h_sup <| c.val.dart_snd_mem_support_of_mem_darts hu.snd
    · simp; intro w hw; exact h_sup <| c.val.dart_fst_mem_support_of_mem_darts hw.snd

def Flow.UnitCirculation (c : N.asSimpleGraph.Circulation v0) : Flow Pr where
  f := Flow.UnitCirculation_f c
  nonneg u v := by unfold UnitCirculation_f; omega
  conservation v _ := UnitCirculation_f_flowOut_eq_flowIn c v
  capacity := by
    intro u v
    simp
    if h : contains_edge c u v then
      simp [h]
      obtain ⟨hAdj, _⟩ := h
      unfold UndirectedNetwork.asSimpleGraph at hAdj
      simp at hAdj
      exact hAdj
    else
      simp [h, N.nonneg]


theorem Flow.UnitCirculation_value_zero (c : N.asSimpleGraph.Circulation v₀) :
    (Flow.UnitCirculation (Pr := Pr) c).value = 0 := by
  rw [value, UnitCirculation, Flow.UnitCirculation_f_flowOut_eq_flowIn c Pr.s]
  linarith

theorem Flow.UnitCirculation_nonzero (c : N.asSimpleGraph.Circulation v₀) :
    (Flow.UnitCirculation (Pr := Pr) c) ≠ 0 := by
  let d := c.val.firstDart c.prop.not_nil
  suffices UnitCirculation_f c d.fst d.snd = 1 by
    intro h
    injection h with f_eq
    rw[f_eq] at this
    simp only [f_eq, zero_ne_one] at this
  suffices contains_edge c d.fst d.snd by simp_all only [SimpleGraph.Walk.firstDart_toProd, UnitCirculation_f, ite_true]
  use d.is_adj
  exact c.val.firstDart_mem_darts c.prop.not_nil

theorem Flow.UnitCirculation_not_backward (c : N.asSimpleGraph.Circulation v₀) :
    ¬(Flow.UnitCirculation (Pr := Pr) c).Backward := by
  rw [Backward, UnitCirculation, not_lt, Flow.UnitCirculation_f_flowOut_eq_flowIn c Pr.s]
