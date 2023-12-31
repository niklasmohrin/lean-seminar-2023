import FlowEquivalentForest.Flow

open BigOperators

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {N : UndirectedNetwork V} {Pr : FlowProblem N.toNetwork}

def SimpleGraph.Walk.dart_counts {G : SimpleGraph V} (p : G.Walk u v) : Multiset (G.Dart) := Multiset.ofList p.darts

def IsFlowWalk (F : Flow Pr) (p : N.asSimpleGraph.Walk u v) :=
  ∀ d, p.dart_counts.count d ≤ F.f d.fst d.snd

-- Could be untied from N and be a Walk in the clique instead to loose the
-- UndirectedNetwork requirement. For us, it might be nicer to not involve
-- another graph here since we are working on an undirected network anyways.
abbrev Flow.Walk (F : Flow Pr) (u v : V) :=
  {p : N.asSimpleGraph.Walk u v // IsFlowWalk F p}

abbrev Flow.Path (F : Flow Pr) (u v : V) := {p : F.Walk u v // p.val.IsPath}
def Flow.Path.path {F : Flow Pr} (p : F.Path u v) : N.asSimpleGraph.Path u v where
  val := p.val.val
  property := p.prop

abbrev Flow.Cycle (F : Flow Pr) (v : V) := {p : F.Walk v v // p.val.IsCycle}
def Flow.CycleFree (F : Flow Pr) := ∀ v, IsEmpty (F.Cycle v)

def Flow.remove_cycle (F : Flow Pr) (C : F.Cycle v) : Flow Pr := sorry
theorem Flow.remove_cycle.value (F : Flow Pr) (C : F.Cycle v) : (F.remove_cycle C).value = F.value := sorry
def Flow.remove_all_cycles (F : Flow Pr) : Flow Pr := sorry
theorem Flow.remove_all_cycles.CycleFree (F : Flow Pr) : F.remove_all_cycles.CycleFree := sorry
theorem Flow.remove_all_cycles.value (F : Flow Pr) : F.remove_all_cycles.value = F.value := sorry

theorem Flow.exists_path_of_value_nonzero (F : Flow Pr) (hF : F.value ≠ 0) : F.Path Pr.s Pr.t := sorry

-- For definition of Flow.remove_path
noncomputable instance {F : Flow Pr} {p : F.Path s t} {u v : V} : Decidable (contains_edge p.path u v) := Classical.dec _

@[simp]
noncomputable def Flow.remove_path (F : Flow Pr) (p : F.Path Pr.s Pr.t) : Flow Pr where
  f u v := F.f u v - (if contains_edge p.path u v then 1 else 0)
  conservation := sorry
  capacity := sorry

theorem Flow.remove_path.value (F : Flow Pr) (p : F.Path Pr.s Pr.t) : (F.remove_path p).value + 1 = F.value := sorry

-- Not needed for our theorem
def Flow.path_decomposition (F : Flow Pr) : Multiset (F.Path Pr.s Pr.t) := sorry
theorem Flow.path_decomposition.f_eq_path_count (F : Flow Pr) :
    ∀ d : N.asSimpleGraph.Dart, F.f d.fst d.snd = Multiset.countP (d ∈ ·.val.val.darts) F.path_decomposition := sorry

-- lemma bottleneck_edge
--     (G : SimpleGraph V)
--     (hG : G.IsAcyclic)
--     (p : G.Path s t)
--     (p' : G.Walk s t)
--     (d : G.Dart)
--     (hd : d ∈ p.val.darts) :
--     d ∈ p'.darts := sorry
--
-- lemma bottleneck_edge'
--     (N : UndirectedNetwork V)
--     (hN : N.asSimpleGraph.IsAcyclic)
--     (p : N.asSimpleGraph.NonemptyPath s t) :
--     ∃ d ∈ p.path.val.darts, N.cap d.fst d.snd = N.bottleneck p ∧ ∀ p' : N.asSimpleGraph.Walk s t, d ∈ p'.darts := sorry

-- Using it for our proof (would still need to construct hd, but should be fine):
theorem Flow.value_le_cap
    (F : Flow Pr)
    (d : N.asSimpleGraph.Dart)
    (hd : ∀ p : N.asSimpleGraph.Walk Pr.s Pr.t, d ∈ p.darts):
    F.value ≤ N.cap d.fst d.snd := by
  wlog hC : F.CycleFree
  · exact (Flow.remove_all_cycles.value F).symm ▸ this F.remove_all_cycles d hd (Flow.remove_all_cycles.CycleFree F)

  suffices ∀ n, ∀ F : Flow Pr, F.value = n → F.value = F.f d.fst d.snd from
    this F.value F rfl ▸ F.capacity _ _
  intro n
  induction n with
  | zero => sorry -- cycle free and value zero => must be null flow
  | succ n ih =>
    intro F hF
    obtain p := F.exists_path_of_value_nonzero (by linarith)
    let F' := F.remove_path p
    have hF' : F'.value = n := by linarith[Flow.remove_path.value F p, hF]
    rw[←Flow.remove_path.value F p]
    rw[ih F' hF']

    have hp : contains_edge p.path d.fst d.snd := ⟨d.is_adj, List.elem_iff.mpr (hd p.path)⟩

    simp only [Flow.remove_path, hp, ite_true]
    have : F.f d.fst d.snd ≠ 0 := sorry -- because p uses this edge
    exact Nat.succ_pred this
