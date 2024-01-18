import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Set.Image
import Mathlib.Init.Set
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Prod

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

lemma Finset.eq_of_sum_eq_of_forall_other_eq
    [DecidableEq α]
    [AddCommMonoid β]
    [IsLeftCancelAdd β]
    [IsRightCancelAdd β]
    {f g : α → β}
    (hsum : Finset.sum s f = Finset.sum s g)
    (ha : a ∈ s)
    (ha' : ∀ a' ∈ s, a' ≠ a → f a' = g a') :
    f a = g a := by
  induction s using Finset.induction_on with
  | empty => contradiction
  | @insert x s' hx ih =>
    rw[Finset.sum_insert hx, Finset.sum_insert hx] at hsum
    if hax : a = x then
      subst hax
      have : Finset.sum s' f = Finset.sum s' g := sum_congr rfl (by
        intro b hb
        exact ha' b (mem_insert_of_mem hb) (ne_of_mem_of_not_mem hb hx)
      )
      exact add_right_cancel (this ▸ hsum)
    else
      apply ih
      · have := ha' x (mem_insert_self x s') (hax ∘ Eq.symm)
        exact add_left_cancel $ this ▸ hsum
      · exact mem_of_mem_insert_of_ne ha hax
      · intro b hb hne
        exact ha' b (mem_insert_of_mem hb) hne

/--
If we sum over a difference of natural numbers such that none of the terms ever
get clamp at zero, we can split the sum of differences into a difference of
sums.

The proof works by induction uses the assumption to move the newly added terms
of the sums into the right positions.
--/
theorem finset_sum_sub_distrib_of_sub_nonneg
    [DecidableEq α]
    (s : Finset α)
    {f g : α → ℕ}
    (h_le : ∀ x ∈ s, g x ≤ f x) :
    ∑ x in s, (f x - g x) = ∑ x in s, f x - ∑ x in s, g x := by
  induction' s using Finset.induction_on' with a s' _ _ has' hi
  · repeat rw[Finset.sum_empty]
    ring
  · have h_le' := fun x hx => h_le x (Finset.mem_insert_of_mem hx)
    repeat rw[Finset.sum_insert has']
    have : ∑ x in s', g x ≤ ∑ x in s', f x := Finset.sum_le_sum h_le'
    rw[hi h_le', Nat.sub_add_eq, ←Nat.add_sub_assoc this, Nat.sub_add_comm (h_le a (Finset.mem_insert_self a s'))]

-- Same as finset_sum_sub_distrib_of_sub_nonneg, but for summing over all elements of a finite type.
theorem fintype_sum_sub_distrib_of_sub_nonneg
    [Fintype α]
    [DecidableEq α]
    {f g : α → ℕ}
    (h_le : ∀ x : α, g x ≤ f x) :
    ∑ x, (f x - g x) = ∑ x, f x - ∑ x, g x :=
  finset_sum_sub_distrib_of_sub_nonneg Finset.univ fun x _ => h_le x

lemma Nat.sub_eq_sub_of_add_eq_add
    {a b c d : ℕ}
    (h : a + b = c + d) :
    a - d = c - b := by
  wlog hac : a ≤ c
  · exact (this h.symm (Nat.le_of_not_le hac)).symm
  have hdb : d ≤ b := by
    by_contra h''
    simp at h''
    have := calc
      a + b ≤ c + b := Nat.add_le_add_right hac b
      _ < c + d     := Nat.add_lt_add_left h'' c
    rw[h] at this
    exact LT.lt.false this

  wlog hda : d ≤ a
  · simp at hda
    have : a ≤ d := Nat.le_of_lt hda
    have : a - d = 0 := Nat.sub_eq_zero_of_le this
    rw[this]
    have : c ≤ b := by
      by_contra h'
      simp at h'
      have := calc
        a + b < d + b := by exact Nat.add_lt_add_right hda b
        _ < d + c := by exact Nat.add_lt_add_left h' d
        _ = c + d := by exact Nat.add_comm d c
      rw[h] at this
      exact LT.lt.false this
    have : c - b = 0 := Nat.sub_eq_zero_of_le this
    rw[this]

  have : a + b - b = c + d - b := by exact congrFun (congrArg HSub.hSub h) b
  have : a = c + d - b := by exact eq_tsub_of_add_eq h
  have : a - d = c + d - b - d := by exact congr (congrArg HSub.hSub this) rfl
  have : a - d = c + d - d - b := by rwa[Nat.sub_right_comm _ d b]
  have : a - d = c - b := by
    conv at this => right; left; rw[Nat.add_sub_assoc (le_refl d), Nat.sub_self, Nat.add_zero]
    exact this
  exact this

-- A pair of two elements that are not equal (that is, they are not on the diagonal of a matrix).
@[ext]
structure NonDiag (α : Type*) extends (α × α) where
  ne : fst ≠ snd

lemma NonDiag.toProd_injective : Function.Injective (@NonDiag.toProd α) := by
  intro a b h
  ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

noncomputable instance [Fintype α] : Fintype (NonDiag α) := Fintype.ofInjective NonDiag.toProd NonDiag.toProd_injective

lemma NonDiag.card_le [Fintype α] : Fintype.card (NonDiag α) ≤ Fintype.card (α × α) := Fintype.card_le_of_injective NonDiag.toProd NonDiag.toProd_injective

instance [DecidableEq α] : DecidableEq (NonDiag α) := by
  intro a b
  rw[NonDiag.ext_iff]
  exact And.decidable
