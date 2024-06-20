import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.SimpleGraph.Path
import FlowEquivalentForest.SimpleGraph.Circulation

open BigOperators
open ContainsEdge

variable
  {V : Type*} [Fintype V] [DecidableEq V]
  {R : Type*} [LinearOrderedCommRing R]
  {N : UndirectedNetwork V R}
  {Pr : FlowProblem N.toNetwork}

@[simp]
abbrev Flow.fromCirculation_f (c : N.asSimpleGraph.Circulation v₀) (x : R) (u v : V) : R := if contains_edge c u v then x else 0

lemma Flow.fromCirculation_f_flowOut_eq_flowIn (c : N.asSimpleGraph.Circulation v₀) (x : R) (v : V) :
    flowOut (Flow.fromCirculation_f c x) v = flowIn (Flow.fromCirculation_f c x) v := by
  simp only [flowOut, flowIn, fromCirculation_f]
  if h_sup : v ∈ c.val.support then
    obtain ⟨u, hu_pred, hu_uniq⟩ := c.pred_exists h_sup
    obtain ⟨w, hw_succ, hw_uniq⟩ := c.succ_exists h_sup
    rw[Finset.sum_eq_single w, Finset.sum_eq_single u]
    · simp only [hu_pred, hw_succ]
    · intro u' _ hu'; by_contra h; simp at h; exact hu' <| hu_uniq u' h.left
    · intro h; exact False.elim <| h <| Finset.mem_univ u
    · intro w' _ hw'; by_contra h; simp at h; exact hw' <| hw_uniq w' h.left
    · intro h; exact False.elim <| h <| Finset.mem_univ w
  else
    rw[Finset.sum_eq_zero, Finset.sum_eq_zero]
    · simp only [Finset.mem_univ, ite_eq_right_iff, forall_true_left]; intro u hu; absurd h_sup; exact c.val.dart_snd_mem_support_of_mem_darts hu.snd
    · simp only [Finset.mem_univ, ite_eq_right_iff, forall_true_left]; intro w hw; absurd h_sup; exact c.val.dart_fst_mem_support_of_mem_darts hw.snd

def Flow.fromCirculation (c : N.asSimpleGraph.Circulation v0) (x : R) (hnonneg : 0 ≤ x) (hcap : ∀ d ∈ c.val.darts, x ≤ N.cap d.fst d.snd) : Flow Pr where
  f := Flow.fromCirculation_f c x
  nonneg u v := by unfold fromCirculation_f; exact ite_nonneg hnonneg le_rfl
  conservation v _ := fromCirculation_f_flowOut_eq_flowIn c x v
  capacity := by
    intro u v
    simp only [fromCirculation_f]
    if h : contains_edge c u v then
      simp [h]
      obtain ⟨_, hd⟩ := h
      exact hcap _ hd
    else
      simp [h, N.nonneg]

variable {v₀ : V} (c : N.asSimpleGraph.Circulation v₀) (x : R) (hnonneg : 0 ≤ x) (hcap : ∀ d ∈ c.val.darts, x ≤ N.cap d.fst d.snd)

@[simp]
theorem Flow.fromCirculation_value_zero : (Flow.fromCirculation (Pr := Pr) c x hnonneg hcap).value = 0 := by
  rw [value, fromCirculation, Flow.fromCirculation_f_flowOut_eq_flowIn c x Pr.s]
  linarith

theorem Flow.fromCirculation_nonzero (hpos : 0 < x) : (Flow.fromCirculation (Pr := Pr) c x (le_of_lt hpos) hcap) ≠ 0 := by
  let d := c.val.firstDart c.prop.not_nil
  suffices fromCirculation_f c x d.fst d.snd = x by
    intro h
    injection h with f_eq
    rw[f_eq] at this
    simp only [f_eq, zero_ne_one] at this
    exact (ne_of_lt hpos) this
  suffices contains_edge c d.fst d.snd by simp_all only [ne_eq, SimpleGraph.Walk.firstDart_toProd, fromCirculation_f, ↓reduceIte, d]
  use d.is_adj
  exact c.val.firstDart_mem_darts c.prop.not_nil
