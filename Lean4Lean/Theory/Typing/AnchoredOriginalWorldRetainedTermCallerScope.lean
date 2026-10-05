import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedCallerScope
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandPrograms

/-! Compose the existing caller scope through the exact generic-term recipe
push. All finite resource replay is shared with the application interpreter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
variable {Fits : Nat → Need → Prop}
private def transportMappedDemandPrograms (same : expression = next)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) : (same ▸ demand).InputPrograms Fits := by
  cases same
  exact programs

noncomputable def RetainedRecipeTermDemandPush.mappedInputPrograms
    {goalRank n : Nat} {goalOutput : Atom goalRank} {profile : Profile n} {atom : Atom n}
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    {pending : RichRecipeContext input recipe}
    {demand : RetainedTermDemand env U registry target goal goalOutput expression atom}
    {rootAtom : Atom input.rank}
    {output : RetainedTermDemand env U registry target goal goalOutput input.canonicalExpression rootAtom}
    (pushed : RetainedRecipeTermDemandPush input pending τ demand output)
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
