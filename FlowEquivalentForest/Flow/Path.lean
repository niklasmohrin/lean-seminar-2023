import FlowEquivalentForest.Flow.Basic
import FlowEquivalentForest.SimpleGraph.Path

open BigOperators
open ContainsEdge

variable
  {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {N : UndirectedNetwork V}
  {Pr : FlowProblem N.toNetwork}

def Flow.fromPath
    (P : N.asSimpleGraph.NonemptyPath Pr.s Pr.t)
    (x : ℤ)
    (hnonneg : 0 ≤ x)
    (hx : x ≤ N.bottleneck P) :
    Flow Pr :=
  let contains_edge := contains_edge P.path

  let f u v : ℤ := if contains_edge u v then x else 0
  have nonneg u v : 0 ≤ f u v := by simp only [f]; omega

  have contains_edge_from_nonzero {u v} (h : f u v ≠ 0) : contains_edge u v := by by_contra; simp_all only [UndirectedNetwork.bottleneck, Finset.le_min'_iff, Finset.mem_image, List.mem_toFinset, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, instPathContainsEdge, instContainsEdgeWalk, ne_eq, ite_eq_right_iff, not_forall, exists_prop, exists_and_right, not_true_eq_false, f, contains_edge]
  have conservation v : v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v := by
    intro hv
    if hp : v ∈ P.path.val.support then
      obtain ⟨u, hu_pred, hu_uniq⟩ := P.path.pred_exists hp hv.left
      obtain ⟨w, hw_succ, hw_uniq⟩ := P.path.succ_exists hp hv.right

      let us := Finset.filter (contains_edge · v) Finset.univ
      have us_singleton : us = {u} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu_pred⟩, fun x hx => hu_uniq x (Finset.mem_filter.mp hx).right⟩
      have sum_usc_zero : (∑ u' in usᶜ, f u' v) = 0 := by
        apply Finset.sum_eq_zero
        intro u' hu'
        by_contra hnonzero
        have : u' ∈ us := Finset.mem_filter.mpr ⟨Finset.mem_univ u', contains_edge_from_nonzero hnonzero⟩
        exact Finset.mem_compl.mp hu' this

      -- The same again, but the other way around
      let ws := Finset.filter (contains_edge v ·) Finset.univ
      have ws_singleton : ws = {w} := Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw_succ⟩, fun x hx => hw_uniq x (Finset.mem_filter.mp hx).right⟩
      have sum_wsc_zero : (∑ w' in wsᶜ, f v w') = 0 := by
        apply Finset.sum_eq_zero
        intro w' hw'
        by_contra hnonzero
        have : w' ∈ ws := Finset.mem_filter.mpr ⟨Finset.mem_univ w', contains_edge_from_nonzero hnonzero⟩
        exact Finset.mem_compl.mp hw' this

      calc
        flowOut f v = ∑ w', f v w'                                 := rfl
        _           = (∑ w' in ws, f v w') + (∑ w' in wsᶜ, f v w') := (Finset.sum_add_sum_compl ws _).symm
        _           = ∑ w' in ws, f v w'                           := add_right_eq_self.mpr sum_wsc_zero
        _           = f v w                                        := by rw[ws_singleton, Finset.sum_singleton]
        _           = x                                            := if_pos hw_succ
        _           = f u v                                        := (if_pos hu_pred).symm
        _           = ∑ u' in us, f u' v                           := by rw[us_singleton, Finset.sum_singleton]
        _           = (∑ u' in us, f u' v) + (∑ u' in usᶜ, f u' v) := (add_right_eq_self.mpr sum_usc_zero).symm
        _           = ∑ u', f u' v                                 := Finset.sum_add_sum_compl us _
        _           = flowIn f v                                   := rfl
    else
      have h_out u : f v u = 0 := by
        by_contra h_nonzero
        have ⟨h_Adj, h_dart⟩ := contains_edge_from_nonzero h_nonzero
        have : v ∈ P.path.val.support := SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ h_dart
        simp_all only [contains_edge, List.elem_iff, UndirectedNetwork.bottleneck, ne_eq, ite_eq_right_iff, forall_exists_index, not_forall, exists_prop, exists_and_right, and_imp, implies_true, forall_const,not_true_eq_false]
      have h_in u : f u v = 0 := by
        by_contra h_nonzero
        have ⟨h_Adj, h_dart⟩  := contains_edge_from_nonzero h_nonzero
        have : v ∈ P.path.val.support := SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ h_dart
        simp_all only [contains_edge, List.elem_iff, UndirectedNetwork.bottleneck, ne_eq, ite_eq_right_iff, forall_exists_index, not_forall, exists_prop, exists_and_right, and_imp, implies_true, forall_const,not_true_eq_false]
      calc
        flowOut f v = ∑ u : V, f v u := rfl
        _           = 0              := Finset.sum_eq_zero $ fun u _ => h_out u
        _           = ∑ u, f u v     := (Finset.sum_eq_zero $ fun u _ => h_in u).symm
        _           = flowIn f v     := rfl
  have capacity u v : f u v ≤ N.cap u v := by
    if he : contains_edge u v then
      calc
        f u v = x                := by simp only [f, he, ite_true]
        _     ≤ N.bottleneck P   := hx
        _     ≤ N.cap u v        := UndirectedNetwork.bottleneck.le_dart P he.snd
    else
      have : f u v = 0 := by simp only [f, he, ite_false]
      linarith[N.nonneg u v]

  { f, nonneg, conservation, capacity }

@[simp]
lemma Flow.fromPath_value
    (P : N.asSimpleGraph.NonemptyPath Pr.s Pr.t)
    (x : ℤ)
    (hnonneg : 0 ≤ x)
    (hx : x ≤ N.bottleneck P) :
    let F := Flow.fromPath P x hnonneg hx
    F.value = x := by
  intro F
  have h_in : flowIn F.f Pr.s = 0 := by
    rw[flowIn, Finset.sum_eq_zero]
    intro u _
    suffices ¬contains_edge P.path u Pr.s by simp_all only [F, fromPath, contains_edge, ite_false]
    exact P.path.no_pred_first

  obtain ⟨v, hv⟩ := P.path.succ_exists (SimpleGraph.Walk.start_mem_support P.path.val) P.ne
  have h_out_succ : F.f Pr.s v = x := by simp only [F, fromPath, hv.left, ite_true]
  have h_out : flowOut F.f Pr.s = x := by
    rw[←h_out_succ]
    apply Finset.sum_eq_single
    · intro v' _ hne
      suffices ¬contains_edge P.path Pr.s v' by simp only [F, fromPath, this, ite_false]
      by_contra h
      exact hne $ hv.right v' h
    · have := Finset.mem_univ v; intro; contradiction

  rw[Flow.value, h_in, h_out]
  ring
