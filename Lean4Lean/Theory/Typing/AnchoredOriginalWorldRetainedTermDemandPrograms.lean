import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandPrograms
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedRecipeTermDemandTrace
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead

/-! Carry the computed caller input programs through the exact generic term
recipe demand and its exact head normalization. A fixed body records an
absent caller slot; ordinary bodies retain the selected key and actual finite
caller program, including all intervening resource transfers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private RetainedTermDemandHead.output RetainedTermDemandHead.rename
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

variable {Fits : Nat → Need → Prop}

noncomputable def RetainedTermDemand.InputPrograms
    {goalRank n : Nat} {goalOutput : Atom goalRank} {atom : Atom n}
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (Fits : Nat → Need → Prop) : Type := by
  induction demand with
  | terminal => exact PUnit
  | output path continuation ih | domain member continuation ih
      | levels equal continuation ih | rename rename continuation ih => exact ih
  | @body n key atom B A prototypeDomain prototypeBody support result rows selected member anchor admitted continuation ih =>
    exact CallerBinderProgram env U registry target Fits key × ih

noncomputable def RetainedTermDemandHead.InputPrograms
    {goalRank n : Nat} {goalOutput : Atom goalRank} {atom : Atom n}
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom)
    (Fits : Nat → Need → Prop) : Type := by
  cases head with
  | terminal => exact PUnit
  | domain path member continuation => exact continuation.InputPrograms Fits
  | @body n x input prototypeDomain prototypeBody key atom B A support result rows path selected member anchor admitted continuation =>
    exact CallerBinderProgram env U registry target Fits key × continuation.InputPrograms Fits

private def transportPrograms (same : expression = next)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) :
    (same ▸ demand).InputPrograms Fits := by
  cases same
  exact programs

/-- The full push relation associates every generated body instruction with
its exact context key. This uses the stored selected singleton action, not a
fresh action selection or an equality inferred from operand readback. -/
noncomputable def RetainedRecipeTermDemandPush.inputPrograms
    {goalRank n : Nat} {goalOutput : Atom goalRank} {profile : Profile n} {atom : Atom n}
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    {pending : RichRecipeContext input recipe}
    {demand : RetainedTermDemand env U registry target goal goalOutput expression atom}
    {rootAtom : Atom input.rank}
    {output : RetainedTermDemand env U registry target goal goalOutput input.canonicalExpression rootAtom}
    (pushed : RetainedRecipeTermDemandPush input pending τ demand output)
    (rename : Nat → Nat)
    (context : pending.BinderPrograms Fits rename)
    (programs : demand.InputPrograms Fits) : output.InputPrograms Fits := by
  induction pushed generalizing rename with
  | root => exact programs
  | domain pending member demand previous ih => exact ih rename context programs
  | body pending selected anchor member admitted demand previous ih =>
    exact ih (fun index => rename (index + 1)) context.2 ⟨some ⟨rename 0, context.1⟩, programs⟩
  | fixedBody pending selected admitted member demand previous ih =>
    exact ih rename context ⟨none, transportPrograms _ _ programs⟩
  | resources pending transfer demand previous ih => exact ih rename context programs
  | action pending change member originalMember selectedAction demand previous ih =>
    exact ih rename context programs

/-- Exact head normalization retains the actual key's program and the
continuation programs through every output, universe and renaming step. -/
noncomputable def RetainedTermHeadNormalization.inputPrograms
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput demand head)
    (programs : demand.InputPrograms Fits) : head.InputPrograms Fits := by
  induction normalized with
  | terminal => exact programs
  | output path prior ih =>
    cases ‹RetainedTermDemandHead ..› <;> exact ih programs
  | domain | body => exact programs
  | levelsTerminal | levelsDomain | levelsBody => exact ‹_ → _› programs
  | rename rename prior ih =>
    cases ‹RetainedTermDemandHead ..› <;> exact ih programs

/-- Consume the selected native row at exactly the normalized body key.
The optional result distinguishes a genuine caller body from a fixed skipped
body; no literal Need membership is required for the genuine branch. -/
noncomputable def RetainedTermHeadNormalization.nativeInputProgram
    {goalRank r : Nat} {goalOutput : Atom goalRank} {inputAtom : Atom r}
    {support result : Profile m} {selectedTable : List (Key m × Profile m)}
    {key : Key m} {atom : Atom m}
    {path : GeneralOutputPath env U registry target inputAtom
      (show Atom (m+1) from .pi prototypeDomain prototypeBody support selectedTable)}
    {selected : (key, result) ∈ selectedTable} {member : atom ∈ result.atoms}
    {admitted : Admitted env U registry target key anchor anchor}
    {continuation : RetainedTermDemand env U registry target goal goalOutput B atom}
    {demand : RetainedTermDemand env U registry target goal goalOutput (.forallE A B) inputAtom}
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
      demand (.body (A := A) path selected member anchor admitted continuation))
    (programs : demand.InputPrograms Fits)
    (row : RankedPendingNativeRow env U registry target table relevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) :
    CallerBinderProgram env U registry target Fits row.oldKey :=
  (normalized.inputPrograms programs).1.map (fun ⟨index, program⟩ =>
    ⟨index, row.replayInput henv hscoped formed program⟩)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
