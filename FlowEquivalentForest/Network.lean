import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice

import FlowEquivalentForest.SimpleGraph.Path

section

variable (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V]

structure Network where
  cap : V → V → ℤ
  nonneg : ∀ u v, 0 ≤ cap u v
  loopless: ∀ v, cap v v = 0

structure UndirectedNetwork extends Network V where
  symm : ∀ u v, cap u v = cap v u

end

section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def Network.capRange (N : Network V): Finset ℤ := Finset.image (λ t ↦ N.cap t.1 t.2) (@Finset.univ (V × V) _) -- (Finset.product Finset.univ Finset.univ)

lemma Network.capRange_NonEmpty {N: Network V} : Finset.Nonempty (Network.capRange N) := by simp only [capRange, Finset.Nonempty.image_iff, Finset.univ_nonempty]

def Network.capMax (N : Network V) : ℤ := Finset.max' (Network.capRange N) Network.capRange_NonEmpty

lemma Network.capMax_max {N : Network V} : ∀ {u v}, N.cap u v ≤ N.capMax := (by
  have h0: ∀ t : V × V, N.cap t.1 t.2 ∈ N.capRange := by
    simp [Network.capRange]

  have h1: ∀ c ∈ N.capRange, c ≤ N.capMax := by
    simp [Network.capMax]
    apply Finset.le_max'

  intro u v
  simp_all only [Prod.forall]
)

def UndirectedNetwork.asSimpleGraph (N : UndirectedNetwork V) : SimpleGraph V where
  Adj u v := 0 < N.cap u v
  symm := by
    intro u v huv
    rw[N.symm]
    exact huv
  loopless := by
    intro v hv
    rw[N.loopless] at hv
    exact LT.lt.false hv

@[simp]
def UndirectedNetwork.bottleneck
    {N : UndirectedNetwork V}
    (P : N.asSimpleGraph.NonemptyPath s t) : ℤ
  := (P.path.val.darts.toFinset.image (λ e => N.cap e.fst e.snd)).min' (by
    apply (Finset.Nonempty.image_iff _).mpr
    exact Walk_darts_Nonempty_from_ne P.ne P.path.val
  )

lemma UndirectedNetwork.bottleneck.single_edge
    {N : UndirectedNetwork V}
    (h: N.asSimpleGraph.Adj u v) :
    N.bottleneck h.toNonemptyPath = N.cap u v := by
  simp_all only [bottleneck, SimpleGraph.Adj.toNonemptyPath, SimpleGraph.Adj.toPath, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, Finset.image_singleton, Finset.min'_singleton]

lemma UndirectedNetwork.bottleneck.cons
    {N : UndirectedNetwork V}
    (h_Adj : N.asSimpleGraph.Adj u v)
    (P : N.asSimpleGraph.NonemptyPath v w)
    (hu : u ∉ P.path.val.support) :
    N.bottleneck (SimpleGraph.NonemptyPath.cons h_Adj P hu) = min (N.cap u v) (N.bottleneck P) := by
  simp [SimpleGraph.NonemptyPath.cons.darts]
  rw[min_comm]
  apply Finset.min'_insert

@[simp]
lemma UndirectedNetwork.bottleneck.le_dart
    {N : UndirectedNetwork V}
    (P : N.asSimpleGraph.NonemptyPath s t)
    {d : N.asSimpleGraph.Dart}
    (hd : d ∈ P.path.val.darts) :
    N.bottleneck P ≤ N.cap d.toProd.fst d.toProd.snd := by
  apply Finset.min'_le
  rw[Finset.mem_image]
  use d
  rw[List.mem_toFinset]
  exact ⟨hd, rfl⟩

lemma UndirectedNetwork.exists_bottleneck_dart
    {N : UndirectedNetwork V}
    (P : N.asSimpleGraph.NonemptyPath s t) :
    ∃ d ∈ P.path.val.darts, N.cap d.fst d.snd = N.bottleneck P := by
  obtain ⟨d, hd₁, hd₂⟩ := Finset.mem_image.mp (Finset.min'_mem (P.path.val.darts.toFinset.image (λ e => N.cap e.fst e.snd)) (by
    apply (Finset.Nonempty.image_iff _).mpr
    exact Walk_darts_Nonempty_from_ne P.ne P.path.val
  ))
  exact ⟨d, List.mem_toFinset.mp hd₁, hd₂⟩

lemma UndirectedNetwork.bottleneck_pos
    {N : UndirectedNetwork V}
    (P : N.asSimpleGraph.NonemptyPath s t) :
    0 < N.bottleneck P := by
  by_contra h
  simp only [bottleneck, Finset.lt_min'_iff, Finset.mem_image, List.mem_toFinset, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, not_lt, nonpos_iff_eq_zero, exists_prop] at h
  obtain ⟨d, _, hd₂⟩ := h
  absurd hd₂
  have : N.asSimpleGraph.Adj d.fst d.snd := d.is_adj
  simp only [UndirectedNetwork.asSimpleGraph, hd₂, d.is_adj] at this
  exact not_le.mpr this

lemma UndirectedNetwork.bottleneck_nonneg
    {N : UndirectedNetwork V}
    (P : N.asSimpleGraph.NonemptyPath s t) :
    0 ≤ N.bottleneck P := le_of_lt <| UndirectedNetwork.bottleneck_pos P

end
