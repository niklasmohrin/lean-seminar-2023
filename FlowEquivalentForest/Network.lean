import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice

import FlowEquivalentForest.SimpleGraph.Path

section

variable ( V : Type* ) [Fintype V] [DecidableEq V] [Nonempty V]

structure Network where
  cap : V → V → ℕ
  loopless: ∀ v, cap v v = 0

structure UndirectedNetwork extends Network V where
  symm: ∀ u v, cap u v = cap v u

end

section

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

def Network.capRange (G : Network V): Finset ℕ := Finset.image (λ t ↦ G.cap t.1 t.2) (@Finset.univ (V × V) _) -- (Finset.product Finset.univ Finset.univ)

lemma Network.capRange_NonEmpty { G: Network V } : Finset.Nonempty (Network.capRange G) := by simp only [capRange, Finset.Nonempty.image_iff, Finset.univ_nonempty]

def Network.capMax (G : Network V) : ℕ := Finset.max' (Network.capRange G) Network.capRange_NonEmpty

lemma Network.capMax_max { G : Network V } : ∀ {u v}, G.cap u v ≤ G.capMax := (by
  have h0: ∀ t : V × V, G.cap t.1 t.2 ∈ G.capRange := by
    simp [Network.capRange]

  have h1: ∀ c ∈ G.capRange, c ≤ G.capMax := by
    simp [Network.capMax]
    apply Finset.le_max'

  intro u v
  simp_all only [Prod.forall]
)

def UndirectedNetwork.asSimpleGraph (G : UndirectedNetwork V) : SimpleGraph V where
  Adj u v := 0 < G.cap u v
  symm := by
    intro u v huv
    rw[G.symm]
    exact huv
  loopless := by
    intro v hv
    rw[G.loopless] at hv
    exact LT.lt.false hv

@[simp]
def UndirectedNetwork.bottleneck
    {G : UndirectedNetwork V}
    (P : G.asSimpleGraph.NonemptyPath s t) : ℕ
  := (P.path.val.darts.toFinset.image (λ e => G.cap e.fst e.snd)).min' (by
    apply (Finset.Nonempty.image_iff _).mpr
    exact Walk_darts_Nonempty_from_ne P.ne P.path.val
  )

lemma UndirectedNetwork.bottleneck.single_edge
    {G : UndirectedNetwork V}
    (h: G.asSimpleGraph.Adj u v) :
    G.bottleneck h.toNonemptyPath = G.cap u v := by
  simp_all only [bottleneck, SimpleGraph.Adj.toNonemptyPath, SimpleGraph.Adj.toPath, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, Finset.image_singleton, Finset.min'_singleton]

lemma UndirectedNetwork.bottleneck.cons
    {G : UndirectedNetwork V}
    (h_Adj : G.asSimpleGraph.Adj u v)
    (P : G.asSimpleGraph.NonemptyPath v w)
    (hu : u ∉ P.path.val.support) :
    G.bottleneck (SimpleGraph.NonemptyPath.cons h_Adj P hu) = min (G.cap u v) (G.bottleneck P) := by
  simp [SimpleGraph.NonemptyPath.cons.darts]
  rw[min_comm]
  apply Finset.min'_insert

@[simp]
lemma UndirectedNetwork.bottleneck.le_dart
    {G : UndirectedNetwork V}
    (P : G.asSimpleGraph.NonemptyPath s t)
    {d : G.asSimpleGraph.Dart}
    (hd : d ∈ P.path.val.darts) :
    G.bottleneck P ≤ G.cap d.toProd.fst d.toProd.snd := by sorry

lemma UndirectedNetwork.exists_bottleneck_dart
    {N : UndirectedNetwork V}
    (P : N.asSimpleGraph.NonemptyPath s t) :
    ∃ d ∈ P.path.val.darts, N.cap d.fst d.snd = N.bottleneck P := sorry

end
