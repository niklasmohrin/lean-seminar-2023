import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Set.Image
import Mathlib.Init.Set
import Mathlib.Algebra.BigOperators.Basic
open BigOperators

-- Every nonempty (infinite) set of natural numbers that is bounded from above has a maximum.
--
-- The proof works by either using the bound itself (if it is a member of the set), or recursively
-- using the theorem with the bound decreased by one. We need to explicitly spell out to Lean that
-- this recursion terminates by showing that b-1 < b (which would not be the case for b = 0, but
-- fortunately, this is impossible by the Nonempty hypothesis).
theorem max_from_Nonempty_bounded
    (s : Set ℕ)
    (hs : s.Nonempty)
    {b : ℕ}
    (hb : ∀ x ∈ s, x ≤ b) :
    ∃ m ∈ s, ∀ x ∈ s, x ≤ m := by
  if hb' : b ∈ s then
    use b
  else
    have : b ≠ 0 := by
      by_contra
      obtain ⟨x, hx⟩ := hs
      have : x = 0 := by aesop
      simp_all only [nonpos_iff_eq_zero, not_true]
    have : b-1 < b := Nat.pred_lt this

    have h' : ∀ x ∈ s, x ≤ b-1 := by
      intro x hx
      have : x ≠ b := ne_of_mem_of_not_mem hx hb'
      have : x < b := this.lt_of_le $ hb x hx
      exact Nat.le_pred_of_lt this
    exact max_from_Nonempty_bounded s hs h'

-- Every nonempty (infinite) set and weighting function `w` (where the weights are natural numbers)
-- with an upper bound on the weight of the elements has a maximal element with respect to `w`.
--
-- For the proof, we use the theorem above on the image set `w(s)` and then extract the preimage of
-- the maximum image as our element with maximum weight.
theorem max_from_Nonempty_bounded_wrt
    (s : Set α)
    (hs : s.Nonempty)
    (w : α → ℕ)
    {b : ℕ}
    (hb : ∀ x ∈ s, w x ≤ b) :
    ∃ m ∈ s, ∀ x ∈ s, w x ≤ w m := by
  have : ∀ y ∈ w '' s, y ≤ b := by aesop
  obtain ⟨m', hm'⟩ := max_from_Nonempty_bounded (w '' s) (hs.image w) this
  obtain ⟨m, hm⟩ := (Set.mem_image w s m').mp hm'.left
  use m
  constructor
  · exact hm.left
  · intro x a
    simp_all only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem finset_sum_sub_distrib_of_sub_nonneg
    [Fintype α]
    {f g : α → ℕ}
    (h_le : ∀ x : α, g x ≤ f x)
  :
    ∑ x, (f x - g x) = ∑ x, f x - ∑ x, g x := by
  sorry
