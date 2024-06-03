import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Basic

-- A function from all pairs of distinct α values to β.
def PairMatrix (α β : Type*) := {x y : α} → (hxy : x ≠ y) → β

-- -- The constant zero matrix
-- instance {α : outParam Type} [Zero β] : Zero (PairMatrix α β) where zero := @fun _ _ _ => 0
--
-- instance {α : outParam Type} [PartialOrder β] : PartialOrder (PairMatrix α β) where
--   le m m' := ∀ {a a'}, (h : a ≠ a') → m h ≤ m' h
--   le_refl m := by simp
--   le_trans m₁ m₂ m₃ h₁₂ h₂₃ a a' h := le_trans (h₁₂ h) (h₂₃ h)
--   le_antisymm m₁ m₂ h h' := by
--     funext a a' ha
--     exact le_antisymm (h ha) (h' ha)

-- Symmetry of a PairMatrix requires that the order of the input pair does not matter.
def PairMatrix.Symmetrical (M : PairMatrix α β) := ∀ {x y}, (h : x ≠ y) → M h = M h.symm

def PairMatrix.Nonneg [Zero β] [LE β] (M : PairMatrix α β) := ∀ {x y}, (h : x ≠ y) → 0 ≤ M h

-- The values in a PairMatrix with finitely many cells are bounded from above.
theorem PairMatrix.bounded {M : PairMatrix α β} [Fintype α] [Nonempty β] [LinearOrder β] :
    ∃ b : β, ∀ (x y : α) (hxy : x ≠ y), M hxy ≤ b := by
  let inner a := {b | ∃ a', ∃ h : a ≠ a', M h = b}
  let all_bs := ⋃ a, inner a
  suffices h : all_bs.Finite by have ⟨b, hb⟩ := h.bddAbove; aesop
  suffices h : ∀ a, (inner a).Finite from Set.finite_iUnion h
  intro a
  suffices Finite (inner a) from Set.toFinite (inner a)
  let α' := {a' // a ≠ a'}
  let f (a' : α') : inner a := ⟨M a'.prop, by aesop⟩
  apply Finite.of_surjective f
  intro b
  aesop
