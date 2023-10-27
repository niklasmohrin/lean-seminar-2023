import Mathlib.Tactic.Ring
import Mathlib.Computability.PartrecCode
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Card

open Set
open BigOperators

section

variable ( V : Type* ) [Fintype V] [DecidableEq V] [Nonempty V]

structure Network where
  cap : V → V → ℕ
  loopLess: ∀ v, cap v v = 0


structure UndirectedNetwork extends Network V where
  symm: ∀ {u v}, cap u v = cap v u

end

section

variable { V : Type* } [Fintype V] [DecidableEq V] [Nonempty V]

def Network.capRange (G : Network V): Finset ℕ := Finset.image (λ t ↦ G.cap t.1 t.2) (@Finset.univ (V × V) _) -- (Finset.product Finset.univ Finset.univ)

instance { G: Network V } : Finset.Nonempty (Network.capRange G) := by simp[Network.capRange, Finset.univ_nonempty]

structure FlowProblem { V : Type* } (G : Network V) where
  s : V
  t : V

variable { G : Network V }

def flowIn (f : V → V → ℤ) (v : V) := ∑ u, (f u v).toNat
def flowOut (f : V → V → ℤ) (v : V) := ∑ u, (f v u).toNat

@[ext]
structure Flow (P : FlowProblem G) where
  f : V → V → ℤ
  skewSymmetry : ∀ {u v}, f u v = -f v u
  conservation : ∀ v, v ≠ s ∧ v ≠ t → flowOut f v = flowIn f u
  capacity : ∀ {u v}, f u v ≤ G.cap u v

def FlowProblem.nullFlow (P : FlowProblem G) : Flow P where
  f _ _ := 0
  skewSymmetry := by simp
  conservation := by aesop
  capacity := by simp

def Flow.value { P : FlowProblem G } (flow : Flow P) := flowOut flow.f P.s

def Flow.isMaximal { P : FlowProblem G } (F : Flow P) := ∀ F' : Flow P, F'.value ≤ F.value

def FlowProblem.maxFlow (P : FlowProblem G) : ℕ := 0
def Network.maxFlowValue (G : Network V) (u v : V) := { s := u, t := v : FlowProblem G}.maxFlow

def UndirectedNetwork.asSimpleGraph (G : UndirectedNetwork V) : SimpleGraph V where
  Adj u v := 0 < G.cap u v
  symm := by
    intro u v huv
    rw[G.symm]
    exact huv
  loopless := by
    intro v hv
    rw[G.loopLess] at hv
    exact LT.lt.false hv

def Network.matrix (G : Network V) := G.maxFlowValue

def ZeroDiagonal (M : α → α → β) [Zero β] := ∀ a, M a a = 0

theorem flowMatrixCharacterization (M : V → V → ℕ) :
  (∃ G : Network V, M = G.matrix) ↔ (ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) := sorry

open SimpleGraph

theorem flowEquivalentTree (M : V → V → ℕ) (hM : ZeroDiagonal M ∧ ∀ {u v w}, min (M u v) (M v w) ≤ M u w) :
  ∃ T : UndirectedNetwork V, M = T.matrix ∧ IsAcyclic T.asSimpleGraph :=
  sorry
