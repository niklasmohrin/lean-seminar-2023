import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem deleteEdges_isAcyclic (G : SimpleGraph V) (hG : G.IsAcyclic) (s : Set (Sym2 V)) : (G.deleteEdges s).IsAcyclic := by
  by_contra h
  suffices ¬G.IsAcyclic by contradiction
  simp[isAcyclic_iff_path_unique] at h ⊢
  obtain ⟨a, b, p₁, hp₁, p₂, hp₂, hne⟩ := h
  have hle := SimpleGraph.deleteEdges_le G s
  use a
  use b
  use p₁.mapLe hle
  use (SimpleGraph.Walk.mapLe_isPath hle).mpr hp₁
  use p₂.mapLe hle
  use (SimpleGraph.Walk.mapLe_isPath hle).mpr hp₂
  by_contra heq
  refine hne $ Walk.map_injective_of_injective ?_ a b $ heq
  exact (Setoid.injective_iff_ker_bot ⇑(Hom.mapSpanningSubgraphs hle)).mpr rfl
