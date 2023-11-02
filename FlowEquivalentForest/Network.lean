import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice

section

variable ( V : Type* ) [Fintype V] [DecidableEq V] [Nonempty V]

structure Network where
  cap : V → V → ℕ
  loopless: ∀ v, cap v v = 0

structure UndirectedNetwork extends Network V where
  symm: ∀ {u v}, cap u v = cap v u

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

end
