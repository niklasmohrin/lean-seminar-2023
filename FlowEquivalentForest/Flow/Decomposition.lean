import FlowEquivalentForest.Flow.Basic

open BigOperators

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {N : UndirectedNetwork V} {Pr : FlowProblem N.toNetwork}

def SimpleGraph.Walk.dart_counts {G : SimpleGraph V} (p : G.Walk u v) : Multiset (G.Dart) := Multiset.ofList p.darts

-- A FlowWalk can only visit each dart of the network as many times as the flow
-- value on this dart.
def IsFlowWalk (F : Flow Pr) (p : N.asSimpleGraph.Walk u v) :=
  ∀ d, p.dart_counts.count d ≤ F.f d.fst d.snd

-- Could be untied from N and be a Walk in the clique instead to loose the
-- UndirectedNetwork requirement. For us, it might be nicer to not involve
-- another graph here since we are working on an undirected network anyways.
abbrev Flow.Walk (F : Flow Pr) (u v : V) :=
  {p : N.asSimpleGraph.Walk u v // IsFlowWalk F p}

def Flow.Walk.nil {F : Flow Pr} : F.Walk v v where
  val := SimpleGraph.Walk.nil
  property := sorry

abbrev Flow.Path (F : Flow Pr) (u v : V) := {p : F.Walk u v // p.val.IsPath}
def Flow.Path.path {F : Flow Pr} (p : F.Path u v) : N.asSimpleGraph.Path u v where
  val := p.val.val
  property := p.prop
def Flow.Path.nil (F : Flow Pr) : F.Path v v where
  val := Flow.Walk.nil
  property := sorry

-- Probably makes constructing the path a lot nicer, but maybe we can also manage without these definitions.
abbrev Flow.Cycle (F : Flow Pr) (v : V) := {p : F.Walk v v // p.val.IsCycle}
def Flow.CycleFree (F : Flow Pr) := ∀ v, IsEmpty (F.Cycle v)

def Flow.remove_cycle (F : Flow Pr) (C : F.Cycle v) : Flow Pr := sorry
theorem Flow.remove_cycle.value (F : Flow Pr) (C : F.Cycle v) : (F.remove_cycle C).value = F.value := sorry
def Flow.remove_all_cycles (F : Flow Pr) : Flow Pr := sorry
theorem Flow.remove_all_cycles.CycleFree (F : Flow Pr) : F.remove_all_cycles.CycleFree := sorry
theorem Flow.remove_all_cycles.value (F : Flow Pr) : F.remove_all_cycles.value = F.value := sorry
theorem Flow.remove_all_cycles.subset (F : Flow Pr) : F.remove_all_cycles ⊆ F := sorry

def Flow.Walk.transfer {F F' : Flow Pr} (p : F.Walk s t) (h : F ⊆ F') : F'.Walk s t where
  val := p.val
  property := by
    intro d
    calc
      Multiset.count d p.val.dart_counts ≤ F.f d.fst d.snd  := p.prop d
      _                                  ≤ F'.f d.fst d.snd := h

def Flow.Walk.transfer.val {F F' : Flow Pr} (p : F.Walk s t) (h : F ⊆ F') : (p.transfer h).val = p.val := rfl

def Flow.Path.transfer {F F' : Flow Pr} (p : F.Path s t) (h : F ⊆ F') : F'.Path s t where
  val := p.val.transfer h
  property := Flow.Walk.transfer.val p.val h ▸ p.property

theorem Flow.exists_path_of_value_nonzero_of_cycleFree
    (F : Flow Pr)
    (hF : F.value ≠ 0)
    (hC : F.CycleFree) :
    F.Path Pr.s Pr.t :=
  build_path (Flow.Path.nil F)
where
  -- Recursive definition of the path: Given a path from some vertex u to the
  -- sink, we pick the next vertex v, add it to the front of the path and
  -- recurse until we arrive at the source.
  build_path {v} (path_so_far : F.Path v Pr.t) : F.Path Pr.s Pr.t :=
    if hvs : v = Pr.s then
      hvs ▸ path_so_far
    else
      let valid_us := {u : V // F.f u v ≠ 0 }
      have : Nonempty valid_us := sorry -- By hF, if v = t, otherwise by flow conservation.

      let u := Classical.choice this
      have : u.val ∉ path_so_far.val.val.support := sorry -- Otherwise, we would have constructed a cycle!
      let path_with_u : F.Path u Pr.t := sorry -- Add u to the front of the path.

      -- Proof for termination (the path got longer):
      have : Fintype.card V - path_with_u.val.val.length < Fintype.card V - path_so_far.val.val.length := sorry

      build_path path_with_u
termination_by build_path p => Fintype.card V - p.val.val.length

theorem Flow.exists_path_of_value_nonzero (F : Flow Pr) (hF : F.value ≠ 0) : F.Path Pr.s Pr.t :=
  let p := Flow.exists_path_of_value_nonzero_of_cycleFree
    F.remove_all_cycles
    (remove_all_cycles.value F ▸ hF)
    (remove_all_cycles.CycleFree F)
  p.transfer $ remove_all_cycles.subset _

-- For definition of Flow.remove_path
noncomputable instance {F : Flow Pr} {p : F.Path s t} {u v : V} : Decidable (contains_edge p.path u v) := Classical.dec _

@[simp]
noncomputable def Flow.remove_path (F : Flow Pr) (p : F.Path Pr.s Pr.t) : Flow Pr where
  f u v := F.f u v - (if contains_edge p.path u v then 1 else 0)
  conservation := sorry
  capacity := sorry

theorem Flow.remove_path.value (F : Flow Pr) (p : F.Path Pr.s Pr.t) : (F.remove_path p).value + 1 = F.value := sorry

-- Not needed for our theorem, but maybe fun
-- def Flow.path_decomposition (F : Flow Pr) : Multiset (F.Path Pr.s Pr.t) := sorry
-- theorem Flow.path_decomposition.f_eq_path_count (F : Flow Pr) :
--     ∀ d : N.asSimpleGraph.Dart, F.f d.fst d.snd = Multiset.countP (d ∈ ·.val.val.darts) F.path_decomposition := sorry

-- Using it for our proof (would still need to construct hd, but should be fine):
theorem Flow.value_le_f
    (F : Flow Pr)
    (d : N.asSimpleGraph.Dart)
    (hd : ∀ p : N.asSimpleGraph.Walk Pr.s Pr.t, d ∈ p.darts):
    F.value ≤ F.f d.fst d.snd := by
  let u := d.fst
  let v := d.snd

  suffices ∀ n, ∀ F : Flow Pr, F.value = n → F.value ≤ F.f u v from this F.value F rfl

  intro n
  induction n with
  | zero => intro F hF; linarith[hF]
  | succ n ih =>
    intro F hF
    obtain p := F.exists_path_of_value_nonzero (by linarith)
    let F' := F.remove_path p
    have hF' : F'.value = n := by linarith[Flow.remove_path.value F p, hF]
    have hf : F'.f u v + 1 = F.f u v := by
      have hp : contains_edge p.path u v := ⟨d.is_adj, List.elem_iff.mpr (hd p.path)⟩
      simp only [Flow.remove_path, hp, ite_true]
      have : F.f u v ≠ 0 := by
        by_contra h₀
        have h := h₀ ▸ p.val.prop d
        simp[SimpleGraph.Walk.dart_counts] at h
        exact List.not_mem_of_count_eq_zero h $ hd p

      exact Nat.succ_pred this

    calc
      F.value = F'.value + 1 := (Flow.remove_path.value F p).symm
      _       ≤ F'.f u v + 1 := Nat.add_le_add_right (ih F' hF') 1
      _       = F.f u v      := hf
