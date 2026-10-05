import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandPrograms
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableCommonDependency

/-! A retained source table is interpreted by actual finite caller programs.
The partial index map records fixed private binders explicitly. Resource
transfers preserve source-variable indices, so they compose with this table
without inventing caller membership or a program for a skipped binder. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

variable {Fits : Nat → Need → Prop}

abbrev MappedVariableProgram (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (Fits : Nat → Need → Prop) (index : Option Nat) (profile : Profile n) :=
  ∀ callerIndex, index = some callerIndex →
    VariableDependencyProgram env U registry target Fits callerIndex profile

noncomputable def MappedVariableProgram.toSlot
    {key : Key n} {index : Option Nat}
    (program : MappedVariableProgram env U registry target Fits index key.input) :
    CallerBinderProgram env U registry target Fits key :=
  match index with
  | none => none
  | some callerIndex => some ⟨callerIndex, program callerIndex rfl⟩

structure CallerVariableProgramScope (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (Fits : Nat → Need → Prop) (available : Valuation) where
  index : Nat → Option Nat
  program : ∀ sourceIndex need, need ∈ available sourceIndex →
    MappedVariableProgram env U registry target Fits (index sourceIndex) need.profile

noncomputable def CallerVariableProgramScope.initial (available : Valuation) :
    CallerVariableProgramScope env U registry target (fun i need => need ∈ available i) available where
  index := fun i => some i
  program := by
    intro i need member j same
    cases Option.some.inj same
    exact .leaf member

noncomputable def CallerVariableProgramScope.empty :
    CallerVariableProgramScope env U registry target Fits (fun _ => []) where
  index := fun _ => none
  program := by intro _ _ member; exact False.elim (List.not_mem_nil member)

/-- The actual native input program pays each retained head Need via the
original BinderPack's grade/coverage facts. Fixed slots retain no caller index. -/
noncomputable def CallerVariableProgramScope.push
    (scope : CallerVariableProgramScope env U registry target Fits available)
    {key : Key n} (slot : CallerBinderProgram env U registry target Fits key)
    (needs : List Need) (fits : ∀ need ∈ needs, Need.Fits key.input need) :
    CallerVariableProgramScope env U registry target Fits (available.push needs) where
  index := fun i => match i with
    | 0 => slot.map Sigma.fst
    | i+1 => scope.index i
  program := by
    intro i need member j same
    cases i with
    | zero =>
      cases slot with
      | none => cases same
      | some selected =>
        cases selected with
        | mk index program =>
          cases Option.some.inj same
          exact program.localDemand need (fits need member).1 (fits need member).2
    | succ i => exact scope.program i need member j same

noncomputable def RecipeResourceTransfer.replayMappedVariablePrograms
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (mapping : Nat → Option Nat)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      MappedVariableProgram env U registry target Fits (mapping i) need.profile) :
    ∀ i need, (i, need) ∈ required →
      MappedVariableProgram env U registry target Fits (mapping i) need.profile := by
  classical
  induction transfer with
  | nil => intro _ _ member; exact False.elim (List.not_mem_nil member)
  | @cons index used needed rest need query tail ih =>
    intro i requested member j same
    by_cases equal : (i, requested) = (index, need)
    · cases equal
      let trace : SortableVariableTrace env U registry target index need.profile used := .legacy query.variableTrace
      exact SortableVariableTrace.replayPrograms henv hscoped formed trace (fun i requested member =>
        supplied i requested (List.mem_append_left _ member) j (by rw [trace.indices member]; exact same))
    · exact ih (fun i requested selected => supplied i requested (List.mem_append_right _ selected))
        i requested ((List.mem_cons.mp member).resolve_left equal) j same

noncomputable def RichRecipeContext.MappedBinderPrograms
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (Fits : Nat → Need → Prop) (mapping : Nat → Option Nat) : Type := by
  induction pending generalizing mapping with
  | root => exact PUnit
  | domain pending ih | fixedBody pending selected admitted ih
      | resources pending transfer ih | action pending change ih => exact ih mapping
  | @body source locals A B relevant prototypeDomain prototypeBody footprint σ n support result key rows
      parent pending selected anchor ih =>
    exact MappedVariableProgram env U registry target Fits (mapping 0) key.input ×
      ih (fun index => mapping (index + 1))

noncomputable def RichRecipeContext.mappedBinderPrograms
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (mapping : Nat → Option Nat)
    (supplied : ∀ i need, (i, need) ∈ footprint →
      MappedVariableProgram env U registry target Fits (mapping i) need.profile) :
    pending.MappedBinderPrograms Fits mapping := by
  induction pending generalizing mapping with
  | root => exact PUnit.unit
  | domain pending ih | action pending change ih | fixedBody pending selected admitted ih =>
    exact ih mapping supplied
  | body pending selected anchor ih =>
    exact ⟨supplied 0 _ List.mem_cons_self,
      ih (fun index => mapping (index + 1)) (fun i need member => supplied (i + 1) need
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(i, need), member, rfl⟩)))⟩
  | resources pending transfer ih =>
    exact ih mapping (transfer.replayMappedVariablePrograms henv hscoped formed mapping supplied)

private def transportMappedDemandPrograms (same : expression = next)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (programs : demand.InputPrograms Fits) : (same ▸ demand).InputPrograms Fits := by
  cases same
  exact programs

noncomputable def RetainedRecipeDemandPush.mappedInputPrograms
    {goalRank n : Nat} {goalOutput : Atom goalRank} {profile : Profile n} {atom : Atom n}
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    {pending : RichRecipeContext input recipe}
    {demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom}
    {rootAtom : Atom input.rank}
    {output : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom}
    (pushed : RetainedRecipeDemandPush input pending τ demand output)
    (mapping : Nat → Option Nat)
    (context : pending.MappedBinderPrograms Fits mapping)
    (programs : demand.InputPrograms Fits) : output.InputPrograms Fits := by
  induction pushed generalizing mapping with
  | root => exact programs
  | domain pending member demand previous ih => exact ih mapping context programs
  | body pending selected anchor member admitted demand previous ih =>
    exact ih (fun index => mapping (index + 1)) context.2
      ⟨MappedVariableProgram.toSlot context.1, programs⟩
  | fixedBody pending selected admitted member demand previous ih =>
    exact ih mapping context ⟨none, transportMappedDemandPrograms _ _ programs⟩
  | resources pending transfer demand previous ih => exact ih mapping context programs
  | action pending change member originalMember selectedAction demand previous ih =>
    exact ih mapping context programs

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
