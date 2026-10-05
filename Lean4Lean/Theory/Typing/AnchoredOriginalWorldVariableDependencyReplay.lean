import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeVariableBodyCompile

/-! Finite substitution of variable programs, retaining every actual leaf and
its resource predicate. Normalization produces only a finite adapter; it does
not interpret a query or assume a semantic answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

structure VariableDependencyProgram (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (Fits : Nat → Need → Prop) (index : Nat) (requested : Profile n) where
  rank : Nat
  bound : n ≤ rank
  raw : Profile rank
  footprint : Footprint
  trace : SortableVariableTrace env U registry target index raw footprint
  resources : ∀ i need, (i, need) ∈ footprint → Fits i need
  adapter : GeneralNormalProfileAdapter env U registry target raw (raiseProfile rank bound requested)

variable {Fits : Nat → Need → Prop}

private noncomputable def raiseTrace
    (trace : SortableVariableTrace env U registry target index (profile : Profile n) footprint)
    (N : Nat) (bound : n ≤ N) :
    SortableVariableTrace env U registry target index (raiseProfile N bound profile) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := Nat.eq_zero_of_le_zero bound
    subst n
    simpa only [raiseProfile_self] using trace
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using trace
    · have previous : n ≤ N := by omega
      rw [raiseProfile_step previous]
      exact .pad (ih previous)

noncomputable def VariableDependencyProgram.empty :
    VariableDependencyProgram env U registry target Fits index (.empty : Profile n) where
  rank := n
  bound := Nat.le_refl n
  raw := .empty
  footprint := []
  trace := .legacy .empty
  resources := by intro i need member; cases member
  adapter := by rw [raiseProfile_self]; exact .refl _

noncomputable def VariableDependencyProgram.map
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (program : VariableDependencyProgram env U registry target Fits index (p : Profile n))
    (adapter : GeneralNormalProfileAdapter env U registry target p q) :
    VariableDependencyProgram env U registry target Fits index q := {
  rank := program.rank, bound := program.bound, raw := program.raw
  footprint := program.footprint, trace := program.trace, resources := program.resources
  adapter := program.adapter.comp (GeneralNormalProfileAdapter.raise henv hscoped formed program.bound adapter) }

noncomputable def VariableDependencyProgram.union
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (left : VariableDependencyProgram env U registry target Fits index (p : Profile n))
    (right : VariableDependencyProgram env U registry target Fits index (q : Profile n)) :
    VariableDependencyProgram env U registry target Fits index (p.union q) := by
  let N := max left.rank right.rank
  have leftBound : left.rank ≤ N := Nat.le_max_left _ _
  have rightBound : right.rank ≤ N := Nat.le_max_right _ _
  refine {
    rank := N, bound := Nat.le_trans left.bound leftBound
    raw := (raiseProfile N leftBound left.raw).union (raiseProfile N rightBound right.raw)
    footprint := left.footprint ++ right.footprint
    trace := .union (raiseTrace left.trace N leftBound) (raiseTrace right.trace N rightBound)
    resources := fun i need member => (List.mem_append.mp member).elim (left.resources i need) (right.resources i need)
    adapter := ?_ }
  simpa only [raiseProfile_union, raiseProfile_trans] using
    GeneralNormalProfileAdapter.union
      (GeneralNormalProfileAdapter.raise henv hscoped formed leftBound left.adapter)
      (GeneralNormalProfileAdapter.raise henv hscoped formed rightBound right.adapter)

noncomputable def VariableDependencyProgram.raiseRequested
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (program : VariableDependencyProgram env U registry target Fits index (profile : Profile n))
    {N : Nat} (bound : n ≤ N) :
    VariableDependencyProgram env U registry target Fits index (raiseProfile N bound profile) := by
  let M := max program.rank N
  have sourceBound : program.rank ≤ M := Nat.le_max_left _ _
  have targetBound : N ≤ M := Nat.le_max_right _ _
  refine {
    rank := M, bound := targetBound
    raw := raiseProfile M sourceBound program.raw
    footprint := program.footprint
    trace := raiseTrace program.trace M sourceBound
    resources := program.resources
    adapter := ?_ }
  simpa only [raiseProfile_trans] using
    GeneralNormalProfileAdapter.raise henv hscoped formed sourceBound program.adapter

noncomputable def VariableDependencyProgram.lowerRequested
    {profile : Profile n} {N : Nat} (bound : n ≤ N)
    (program : VariableDependencyProgram env U registry target Fits index (raiseProfile N bound profile)) :
    VariableDependencyProgram env U registry target Fits index profile := {
  rank := program.rank, bound := Nat.le_trans bound program.bound, raw := program.raw
  footprint := program.footprint, trace := program.trace, resources := program.resources
  adapter := by simpa only [raiseProfile_trans] using program.adapter }

private noncomputable def aggregatePrograms
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (footprint : Footprint) (N : Nat)
    (bounded : ∀ i need, (i, need) ∈ footprint → need.rank ≤ N)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      VariableDependencyProgram env U registry target Fits index need.profile) :
    VariableDependencyProgram env U registry target Fits index (footprint.atGrade N) := by
  match footprint with
  | [] => exact .empty
  | (i, need) :: rest =>
    have bound := bounded i need List.mem_cons_self
    let head := (supplied i need List.mem_cons_self).raiseRequested henv hscoped formed bound
    let tail := aggregatePrograms henv hscoped formed rest N
      (fun i need member => bounded i need (List.mem_cons_of_mem _ member))
      (fun i need member => supplied i need (List.mem_cons_of_mem _ member))
    simpa only [Footprint.atGrade, List.flatMap_cons, Need.atGrade, dif_pos bound, Profile.union, Profile.mk, Profile.atoms] using
      head.union henv hscoped formed tail

/-- Compile exact finite leaf replacements under one source trace. The output
index may differ from the source index, and every retained leaf satisfies the
supplied resource predicate. In particular, that predicate may be the fixed
common caps rather than membership in a currently selected table. -/
noncomputable def SortableVariableTrace.replayPrograms
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (trace : SortableVariableTrace env U registry target sourceIndex (profile : Profile n) footprint)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      VariableDependencyProgram env U registry target Fits index need.profile) :
    VariableDependencyProgram env U registry target Fits index profile := by
  let combined := aggregatePrograms henv hscoped formed footprint trace.height
    (fun _ _ member => trace.leaf_bound member) supplied
  exact VariableDependencyProgram.lowerRequested trace.output_bound
    (combined.map henv hscoped formed (trace.normalize henv hscoped formed trace.height (Nat.le_refl _)))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
