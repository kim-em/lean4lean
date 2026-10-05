import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedSymbolicIndices
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermCallerScope

/-! Symbolic term correspondence through the exact retained demand.
Private fixed binders receive a closed sentinel, never a fabricated caller
variable. The sentinel is eliminated by the actual skipped-binder renaming. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private levelsSubstitutionKernel from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

variable {Fits : Nat → Need → Prop}

noncomputable def RetainedTermDemand.symbolicReadback
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) (mapping : Subst) : VExpr := by
  induction demand generalizing mapping with
  | terminal => exact goal.subst mapping
  | output path continuation ih | domain member continuation ih | levels equal continuation ih =>
    exact ih programs mapping
  | body selected member anchor admitted continuation ih =>
    exact ih programs.2 (mapping.cons (callerIndexExpression (programs.1.map Sigma.fst)))
  | rename rename continuation ih => exact ih programs (Subst.lift_l rename mapping)

private def symbolicTransportPrograms (same : expression = next)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) : (same ▸ demand).InputPrograms Fits := by
  cases same
  exact programs

private theorem symbolic_transport (same : expression = next)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) (mapping : Subst) :
    (same ▸ demand).symbolicReadback (symbolicTransportPrograms same demand programs) mapping = demand.symbolicReadback programs mapping := by
  cases same
  rfl

/-- Only source variables actually present in the retained expression affect
the symbolic final term; selected body slots come from the exact program. -/
theorem RetainedTermDemand.symbolicReadback_congr
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits)
    (same : expression.subst σ = expression.subst τ) :
    demand.symbolicReadback programs σ = demand.symbolicReadback programs τ := by
  induction demand generalizing σ τ with
  | terminal => exact same
  | output path continuation ih => exact ih programs same
  | domain member continuation ih => exact ih programs (VExpr.forallE.inj same).1
  | body selected member anchor admitted continuation ih =>
    apply ih programs.2
    have body := congrArg (fun e : VExpr => e.inst (callerIndexExpression (programs.1.map Sigma.fst)))
      (VExpr.forallE.inj same).2
    simpa only [inst_lift_cons] using body
  | levels equal continuation ih => exact ih programs (levelsSubstitutionKernel equal same)
  | rename rename continuation ih =>
    apply ih programs
    simpa only [subst_lift'] using same

theorem RetainedTermDemand.symbolicReadback_closed
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (programs : demand.InputPrograms Fits) (closed : expression.Closed) :
    demand.symbolicReadback programs σ = demand.symbolicReadback programs τ := by
  apply demand.symbolicReadback_congr programs
  exact (closed.subst_eq Subst.Fixes.zero).trans (closed.subst_eq Subst.Fixes.zero).symm

open private RetainedTermDemandHead.output RetainedTermDemandHead.rename
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead

noncomputable def RetainedTermDemandHead.symbolicReadback
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom)
    (programs : head.InputPrograms Fits) (mapping : Subst) : VExpr := by
  cases head with
  | terminal rename _ _ =>
    exact goal.subst (Subst.lift_l rename mapping)
  | domain path member continuation => exact continuation.symbolicReadback programs mapping
  | body path selected member anchor admitted continuation =>
    exact continuation.symbolicReadback programs.2
      (mapping.cons (callerIndexExpression (programs.1.map Sigma.fst)))

theorem RetainedTermHeadNormalization.symbolicReadback
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput demand head)
    (programs : demand.InputPrograms Fits) (mapping : Subst) :
    head.symbolicReadback (normalized.inputPrograms programs) mapping =
      demand.symbolicReadback programs mapping := by
  induction normalized generalizing mapping with
  | terminal => rfl
  | output path prior ih =>
    cases ‹RetainedTermDemandHead ..› <;> exact ih programs mapping
  | domain | body => rfl
  | levelsTerminal _ _ _ _ ih => exact ih programs mapping
  | levelsDomain _ _ _ _ _ _ ih => exact ih programs mapping
  | levelsBody _ _ _ _ _ _ _ _ _ ih => exact ih programs mapping
  | rename rename prior ih =>
    cases ‹RetainedTermDemandHead ..› with
    | terminal previous levels path =>
      have commute : Subst.lift_l (previous.comp rename) mapping =
          Subst.lift_l previous (Subst.lift_l rename mapping) := by
        funext i
        simp only [Subst.lift_l, Lift.liftVar_comp]
      change goal.subst (Subst.lift_l (previous.comp rename) mapping) = _
      rw [commute]
      exact ih programs (Subst.lift_l rename mapping)
    | domain path member continuation => exact ih programs (Subst.lift_l rename mapping)
    | body path selected member anchor admitted continuation =>
      have result := ih programs (Subst.lift_l rename mapping)
      have commute : Subst.lift_l rename.cons (mapping.cons (callerIndexExpression ((prior.inputPrograms programs).1.map Sigma.fst))) =
          (Subst.lift_l rename mapping).cons (callerIndexExpression ((prior.inputPrograms programs).1.map Sigma.fst)) := by
        funext i
        cases i <;> rfl
      change continuation.symbolicReadback (prior.inputPrograms programs).2
        (Subst.lift_l rename.cons (mapping.cons
          (callerIndexExpression ((prior.inputPrograms programs).1.map Sigma.fst)))) = _
      rw [commute]
      exact result

private theorem mappedSlot_index {key : Key n} {index : Option Nat}
    (program : MappedVariableProgram env U registry target Fits index key.input) :
    (MappedVariableProgram.toSlot program).map Sigma.fst = index := by
  cases index <;> rfl

open private transportMappedDemandPrograms
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermCallerScope

/-- The actual charged push preserves the symbolic caller term even though
its new canonical frame has an empty source table. In particular a fixed
body is skipped syntactically; it cannot become a caller variable. -/
theorem RetainedRecipeTermDemandPush.symbolicReadback
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
    (programs : demand.InputPrograms Fits) :
    output.symbolicReadback (pushed.mappedInputPrograms mapping context programs)
      (callerIndexSubst (fun _ => none)) = demand.symbolicReadback programs (callerIndexSubst mapping) := by
  induction pushed generalizing mapping with
  | root member demand =>
    exact (RetainedTermDemand.levels input.expressionEq demand).symbolicReadback_closed
      programs input.closed
  | domain pending member demand previous ih => exact ih mapping context programs
  | body pending selected anchor member admitted demand previous ih =>
    have result := ih (fun i => mapping (i+1)) context.2
      ⟨MappedVariableProgram.toSlot context.1, programs⟩
    change _ = demand.symbolicReadback programs (callerIndexSubst mapping)
    have consEq : (callerIndexSubst (fun i => mapping (i+1))).cons
        (callerIndexExpression ((MappedVariableProgram.toSlot context.1).map Sigma.fst)) =
        callerIndexSubst mapping := by
      rw [mappedSlot_index]
      funext i
      cases i <;> rfl
    change _ = demand.symbolicReadback programs
      ((callerIndexSubst (fun i => mapping (i+1))).cons
        (callerIndexExpression ((MappedVariableProgram.toSlot context.1).map Sigma.fst))) at result
    exact result.trans (congrArg (demand.symbolicReadback programs) consEq)
  | fixedBody pending selected admitted member demand previous ih =>
    have result := ih mapping context ⟨none, transportMappedDemandPrograms _ _ programs⟩
    exact result.trans (symbolic_transport _ (.rename (.skip .refl) demand) programs _)
  | resources pending transfer demand previous ih => exact ih mapping context programs
  | action pending change member originalMember selectedAction demand previous ih =>
    exact ih mapping context programs

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
