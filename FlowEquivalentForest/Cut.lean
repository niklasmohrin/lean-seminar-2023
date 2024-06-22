import FlowEquivalentForest.Flow.Decomposition

universe u_v u_r
variable {V : Type u_v} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type u_r} [LinearOrderedCommRing R]
variable {N : Network V R}

open BigOperators

section

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

variable {Pr : FlowProblem N} (c : Cut Pr)

def crossing_darts : Finset ((⊤ : SimpleGraph V).Dart) :=
  Finset.univ.filter fun d ↦ d.fst ∈ c.left ∧ d.snd ∈ c.right

@[simp]
instance : Membership ((⊤ : SimpleGraph V).Dart) (Cut Pr) where
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
    exfalso
    simp at huv huv'
    exact huv'
      (SimpleGraph.Dart.mk (u, v) fun heq ↦ by simp at heq; exact huv.right <| heq ▸ huv.left)
      huv.left huv.right rfl
  · simp

open SimpleGraph Walk in
theorem exists_crossing_dart (hu : u ∈ c.left) (hw : w ∈ c.right) :
    (p : (completeGraph V).Walk u w) → ∃ d ∈ c.crossing_darts, d ∈ p.darts
  | nil => by rw[right, Finset.mem_compl] at hw; contradiction
  | cons' u v w huv p' => by
    if hv : v ∈ c.left then
      obtain ⟨d, hd, hd'⟩ := exists_crossing_dart hv hw p'
      exact ⟨d, hd, List.mem_of_mem_tail hd'⟩
    else
      use Dart.mk (u, v) huv
      simp[crossing_darts, hu, hv]

theorem exists_crossing_dart_st :
    (p : (completeGraph V).Walk Pr.s Pr.t) → ∃ d ∈ c.crossing_darts, d ∈ p.darts :=
  c.exists_crossing_dart c.s_mem c.t_mem_right

variable (F : Flow Pr)

theorem bounds_flow : F.value ≤ c.value := by
  apply le_trans <| F.value_le_sum_f c.crossing_darts fun p _ ↦ c.exists_crossing_dart_st p.path.val
  rw[value_eq_sum_crossing_darts]
  exact Finset.sum_le_sum fun d _ ↦ F.capacity ..

end Cut
