import FlowEquivalentForest.Flow.Decomposition

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]

open BigOperators

section

variable {N : Network V R}

structure Cut (Pr : FlowProblem N) where
  left : Finset V
  s_mem : Pr.s ∈ left
  t_not_mem : Pr.t ∉ left

variable {Pr : FlowProblem N}

@[simp]
abbrev Cut.right (c : Cut Pr) : Finset V := c.leftᶜ

def Cut.t_mem_right (c : Cut Pr) : Pr.t ∈ c.right := by rw[right, Finset.mem_compl]; exact c.t_not_mem

def Cut.value (c : Cut Pr) : R := ∑ u in c.left, ∑ v in c.right, N.cap u v

end

namespace Cut

variable {N : UndirectedNetwork V R} [DecidableRel N.asSimpleGraph.Adj] {Pr : FlowProblem N.toNetwork} (c : Cut Pr)

def crossing_darts : Finset (N.asSimpleGraph.Dart) :=
  Finset.univ.filter fun d ↦ d.fst ∈ c.left ∧ d.snd ∈ c.right

@[simp]
instance : Membership (N.asSimpleGraph.Dart) (Cut Pr) where
  mem d c := d ∈ c.crossing_darts

theorem value_eq_sum_crossing_darts : c.value = ∑ d in c.crossing_darts, N.cap d.fst d.snd := by
  rw[value, ←Finset.sum_product', right, crossing_darts]
  apply Eq.symm
  apply Finset.sum_of_injOn SimpleGraph.Dart.toProd
  · intro d _ d' _ h
    exact (SimpleGraph.Dart.ext_iff d d').mpr h
  · intro d hd
    simp at hd ⊢
    exact hd
  · intro (u, v) huv huv'
    by_contra h
    simp at huv huv'
    exact huv'
      (SimpleGraph.Dart.mk (u, v) (lt_of_le_of_ne (N.nonneg u v) (Ne.symm h)))
      huv.left huv.right rfl
  · simp

open SimpleGraph Walk in
theorem exists_crossing_dart (hu : u ∈ c.left) (hw : w ∈ c.right) :
    (p : N.asSimpleGraph.Walk u w) → ∃ d ∈ c.crossing_darts, d ∈ p.darts
  | nil => by rw[right, Finset.mem_compl] at hw; contradiction
  | cons' u v w huv p' => by
    if hv : v ∈ c.left then
      obtain ⟨d, hd, hd'⟩ := exists_crossing_dart hv hw p'
      exact ⟨d, hd, List.mem_of_mem_tail hd'⟩
    else
      use Dart.mk (u, v) huv
      simp[crossing_darts, hu, hv]

theorem exists_crossing_dart_st :
    (p : N.asSimpleGraph.Walk Pr.s Pr.t) → ∃ d ∈ c.crossing_darts, d ∈ p.darts :=
  c.exists_crossing_dart c.s_mem c.t_mem_right

theorem bounds_flow (c : Cut Pr) (F : Flow Pr) : F.value ≤ c.value := by
  apply le_trans <| F.value_le_sum_f c.crossing_darts fun p ↦ c.exists_crossing_dart_st p.val
  rw[value_eq_sum_crossing_darts]
  exact Finset.sum_le_sum fun d _ ↦ F.capacity ..

end Cut
