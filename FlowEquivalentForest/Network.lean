import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice

import FlowEquivalentForest.SimpleGraph.Path

section

variable (V : Type*) (R : Type*) [OrderedRing R]

structure Network where
  cap : V → V → R
  nonneg : ∀ u v, 0 ≤ cap u v
  loopless: ∀ v, cap v v = 0

structure UndirectedNetwork extends Network V R where
  symm : ∀ u v, cap u v = cap v u

end

section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {R : Type*} [LinearOrderedRing R]

def Network.capRange (N : Network V R) := Finset.image (λ t ↦ N.cap t.1 t.2) (@Finset.univ (V × V) _)

lemma Network.capRange_NonEmpty {N: Network V R} : Finset.Nonempty (Network.capRange N) := by simp only [capRange, Finset.Nonempty.image_iff, Finset.univ_nonempty]

def Network.capMax (N : Network V R) := Finset.max' (Network.capRange N) Network.capRange_NonEmpty

lemma Network.capMax_max {N : Network V R} : ∀ {u v}, N.cap u v ≤ N.capMax := (by
  have h0: ∀ t : V × V, N.cap t.1 t.2 ∈ N.capRange := by
    simp [Network.capRange]

  have h1: ∀ c ∈ N.capRange, c ≤ N.capMax := by
    simp [Network.capMax]
    apply Finset.le_max'

  intro u v
  simp_all only [Prod.forall]
)

namespace Network
variable (N : Network V R)

variable { s t : V } (P : (completeGraph V).NonemptyPath s t)

def bottleneck : R := (P.path.val.darts.toFinset.image (λ e => N.cap e.fst e.snd)).min' (by
    rw[Finset.image_nonempty]
    exact Walk_darts_Nonempty_from_ne P.ne P.path.val
  )

@[simp]
lemma bottleneck_single_edge {u v : V} (h : (completeGraph V).Adj u v) :
    N.bottleneck h.toNonemptyPath = N.cap u v := by
  simp_all only [bottleneck, SimpleGraph.Adj.toNonemptyPath, SimpleGraph.Adj.toPath, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, Finset.image_singleton, Finset.min'_singleton]

@[simp]
lemma bottleneck_cons (P : (completeGraph V).NonemptyPath v w) (hu : u ∉ P.path.val.support) :
    have h_adj := fun heq ↦ (heq ▸ hu) P.path.val.start_mem_support
    N.bottleneck (SimpleGraph.NonemptyPath.cons h_adj P hu) = min (N.cap u v) (N.bottleneck P) := by
  simp [bottleneck, SimpleGraph.NonemptyPath.cons.darts]
  rw[min_comm, Finset.min'_insert]

@[simp]
lemma bottleneck_le_dart {d : (completeGraph V).Dart} (hd : d ∈ P.path.val.darts) :
    N.bottleneck P ≤ N.cap d.toProd.fst d.toProd.snd := by
  apply Finset.min'_le
  rw[Finset.mem_image]
  use d
  rw[List.mem_toFinset]
  exact ⟨hd, rfl⟩

lemma exists_bottleneck_dart : ∃ d ∈ P.path.val.darts, N.cap d.fst d.snd = N.bottleneck P := by
  obtain ⟨d, hd₁, hd₂⟩ := Finset.mem_image.mp (Finset.min'_mem (P.path.val.darts.toFinset.image (λ e => N.cap e.fst e.snd)) (by
    rw[Finset.image_nonempty]
    exact Walk_darts_Nonempty_from_ne P.ne P.path.val
  ))
  exact ⟨d, List.mem_toFinset.mp hd₁, hd₂⟩

@[simp]
lemma bottleneck_nonneg : 0 ≤ N.bottleneck P := by
  simp[bottleneck, N.nonneg]

lemma lt_bottleneck_of_lt_cap (h : ∀ d ∈ P.path.val.darts, x < N.cap d.fst d.snd) : x < N.bottleneck P := sorry

variable (p : V → V → Prop) [DecidableRel p] (p' : V → V → Prop) [DecidableRel p']

def filter : Network V R where
  cap u v := if p u v then N.cap u v else 0
  nonneg u v := by by_cases (p u v) <;> simp[*, N.nonneg]
  loopless v := by by_cases (p v v) <;> simp[*, N.loopless]

lemma filter_filter : (N.filter p).filter p' = N.filter (fun u v ↦ p u v ∧ p' u v) := sorry

variable {p}

lemma bottleneck_filter_eq_of_forall (P : (completeGraph V).NonemptyPath s t) (h : ∀ d ∈ P.path.val.darts, p d.fst d.snd) :
    (N.filter p).bottleneck P = N.bottleneck P := sorry

def activePath (s t : V) := { p : (⊤ : SimpleGraph V).NonemptyPath s t // 0 < N.bottleneck p }

instance : Fintype (N.activePath s t) := Subtype.fintype _

end Network

namespace UndirectedNetwork

variable (N : UndirectedNetwork V R)

def asSimpleGraph : SimpleGraph V where
  Adj u v := 0 < N.cap u v
  symm := by
    intro u v huv
    rw[N.symm]
    exact huv
  loopless := by
    intro v hv
    rw[N.loopless] at hv
    exact LT.lt.false hv

theorem mem_edgeSet_of_bottleneck_pos
    (p : (completeGraph V).NonemptyPath s t)
    (h : 0 < N.bottleneck p)
    (e : Sym2 V)
    (he : e ∈ p.path.val.edges) :
    e ∈ N.asSimpleGraph.edgeSet := by
  obtain ⟨⟨u, v⟩, huv⟩ := e.exists_rep
  subst huv
  simp only [SimpleGraph.mem_edgeSet, asSimpleGraph]
  apply lt_of_lt_of_le h
  match p.path.val.mem_darts_of_mem_edges he with
  | Or.inl hd => exact N.bottleneck_le_dart p hd
  | Or.inr hd => exact N.symm u v ▸ (N.bottleneck_le_dart p hd)

end UndirectedNetwork
end
