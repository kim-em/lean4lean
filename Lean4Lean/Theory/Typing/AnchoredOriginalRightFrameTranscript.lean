import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance

/-! A structural transcript of one selected right frame. The transcript keeps
the actual original domains, argument locations and owner occurrences. Queries
and certificates may be replaced by their computed right-side outputs, while
the resource table and every corresponding subframe remain fixed. It supplies
no reconstruction procedure or semantic answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

mutual
inductive RawFrameRightRebuilt (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    {sourceEnv : VEnv} → {source : List VExpr} →
    {context : ContextDerivation sourceEnv U source} →
    {locals : List Nat} → {σ τ : Subst} → {available : Valuation} →
    RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available →
    RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available → Type where
  | nil : RawFrameRightRebuilt env U registry target .nil .nil
  | diagonal (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ σ available) :
      RawFrameRightRebuilt env U registry target frame frame
  | reserve (tail : RawFrameRightRebuilt env U registry target old next) (closures : List Closure) :
      RawFrameRightRebuilt env U registry target (.reserve old closures) (.reserve next closures)
  | merge (left : RawFrameRightRebuilt env U registry target oldLeft nextLeft)
      (right : RawFrameRightRebuilt env U registry target oldRight nextRight) :
      RawFrameRightRebuilt env U registry target (.merge oldLeft oldRight) (.merge nextLeft nextRight)
  | bind
      {context : ContextDerivation sourceEnv U source}
      {old : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      {next : RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available}
      (tail : RawFrameRightRebuilt env U registry target old next)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (oldCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) oldFootprint)
      (oldResources : oldFootprint.Available available)
      (newCode : RichCert sourceEnv env U registry target (.ref domain) locals τ true support newFootprint)
      (newResources : newFootprint.Available available)
      (typed : input.HasType support)
      (oldArguments : Related env U registry target x y (A.subst σ) input support)
      (newArguments : Related env U registry target y y (A.subst τ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      RawFrameRightRebuilt env U registry target
        (.bind old domain oldCode oldResources typed oldArguments needs bounded covered)
        (.bind next domain newCode newResources typed newArguments needs bounded covered)
  | capture
      {context : ContextDerivation sourceEnv U source}
      {old : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
      {next : RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available}
      (tail : RawFrameRightRebuilt env U registry target old next)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
      (initial : ContextDerivation sourceEnv U rootSource)
      (argument : EndpointState sourceEnv U source a A)
      (location : Located root argument) (lineage : location.contextDerivation initial = context)
      (oldQuery : RichObs sourceEnv env U registry target argument locals σ
        (oldInput : Profile k) oldQueryFootprint)
      (oldAvailable : oldQueryFootprint.Available available)
      (newQuery : RichObs sourceEnv env U registry target argument locals τ
        (newInput : Profile j) newQueryFootprint)
      (newAvailable : newQueryFootprint.Available available)
      (oldCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) oldFootprint)
      (oldResources : oldFootprint.Available available)
      (newCode : RichCert sourceEnv env U registry target (.ref domain) locals τ true support newFootprint)
      (newResources : newFootprint.Available available)
      (typed : input.HasType support)
      (oldArguments : Related env U registry target x y (A.subst σ) input support)
      (newArguments : Related env U registry target y y (A.subst τ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      RawFrameRightRebuilt env U registry target
        (.capture old domain initial argument location lineage oldQuery oldAvailable
          oldCode oldResources typed oldArguments needs bounded covered)
        (.capture next domain initial argument location lineage newQuery newAvailable
          newCode newResources typed newArguments needs bounded covered)
  | group
      {context : ContextDerivation headerEnv U headerSource}
      {field : EndpointRef sourceEnv U source fieldExpression fieldType}
      {major : EndpointRef sourceEnv U source majorExpression majorType}
      {old : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available}
      {next : RawOriginalRichFrame headerEnv env U registry target context locals τ τ available}
      (tail : RawFrameRightRebuilt env U registry target old next)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      (ordered : sourceEnv.Ordered) (initial : List Closure)
      {oldEntries : RawRichGroupEntries (field := field) (major := major) domain env registry target
        locals σ available initial rawCapture leftValue rightValue needs}
      {newEntries : RawRichGroupEntries (field := field) (major := major) domain env registry target
        locals τ available initial rawCapture rightValue rightValue needs}
      (entries : RawEntriesRightRebuilt env U registry target oldEntries newEntries) :
      RawFrameRightRebuilt env U registry target
        (.group old domain ordered initial oldEntries) (.group next domain ordered initial newEntries)

inductive RawEntryRightRebuilt (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    {sourceEnv headerEnv : VEnv} → {source headerSource : List VExpr} →
    {fieldExpression fieldType majorExpression majorType A : VExpr} → {level : VLevel} →
    {field : EndpointRef sourceEnv U source fieldExpression fieldType} →
    {major : EndpointRef sourceEnv U source majorExpression majorType} →
    {domain : EndpointRef headerEnv U headerSource A (.sort level)} →
    {headerLocals : List Nat} → {declaredLeft declaredRight : Subst} → {headerAvailable : Valuation} →
    {ownerInitial : List Closure} → {rawCapture leftValue rightValue : VExpr} →
    {n : Nat} → {input : Profile n} →
    RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input →
    RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue n input → Type where
  | mk
      {field : EndpointRef sourceEnv U source fieldExpression fieldType}
      {major : EndpointRef sourceEnv U source majorExpression majorType}
      {domain : EndpointRef headerEnv U headerSource A (.sort level)}
      (owner : HeaderOwner field major)
      (initial : ContextDerivation sourceEnv U source)
      {oldFrame : RawOriginalRichFrame sourceEnv env U registry target (owner.context initial)
        ownerLocals ownerLeft ownerRight ownerAvailable}
      {newFrame : RawOriginalRichFrame sourceEnv env U registry target (owner.context initial)
        ownerLocals ownerRight ownerRight ownerAvailable}
      (frame : RawFrameRightRebuilt env U registry target oldFrame newFrame)
      (substitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source)
      (rightSubstitutions : Ctx.SubstEq env U target ownerRight ownerRight owner.source)
      {rawCapture : VExpr}
      (depth : Nat) (sourcePrefix : List VExpr)
      (sourceEq : owner.source = sourcePrefix ++ source) (depthEq : depth = sourcePrefix.length)
      (expressionEq : owner.expression = rawCapture.lift' (.skipN .refl depth))
      (leftEq : owner.expression.subst ownerLeft = leftValue)
      (rightEq : owner.expression.subst ownerRight = rightValue)
      (oldBound : n ≤ oldRank)
      (oldAdapter : GeneralNormalProfileAdapter env U registry target (oldInput : Profile oldRank)
        (raiseProfile oldRank oldBound (input : Profile n)))
      (oldQuery : RichObs sourceEnv env U registry target owner.node ownerLocals ownerLeft oldInput oldFootprint)
      (oldResources : oldFootprint.Available ownerAvailable)
      (oldAnswer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
        ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input)
      (newBound : n ≤ newRank)
      (newAdapter : GeneralNormalProfileAdapter env U registry target (newInput : Profile newRank)
        (raiseProfile newRank newBound input))
      (newQuery : RichObs sourceEnv env U registry target owner.node ownerLocals ownerRight newInput newFootprint)
      (newResources : newFootprint.Available ownerAvailable)
      (newAnswer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
        ownerRight ownerRight declaredRight ownerAvailable headerAvailable input) :
      RawEntryRightRebuilt env U registry target
        (.mk owner ownerLocals ownerLeft ownerRight ownerAvailable initial oldFrame substitutions depth sourcePrefix
          sourceEq depthEq expressionEq leftEq rightEq oldRank oldInput oldBound oldAdapter oldFootprint
          oldQuery oldResources oldAnswer)
        (.mk owner ownerLocals ownerRight ownerRight ownerAvailable initial newFrame rightSubstitutions depth sourcePrefix
          sourceEq depthEq expressionEq rightEq rightEq newRank newInput newBound newAdapter newFootprint
          newQuery newResources newAnswer)

inductive RawEntriesRightRebuilt (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    {sourceEnv headerEnv : VEnv} → {source headerSource : List VExpr} →
    {fieldExpression fieldType majorExpression majorType A : VExpr} → {level : VLevel} →
    {field : EndpointRef sourceEnv U source fieldExpression fieldType} →
    {major : EndpointRef sourceEnv U source majorExpression majorType} →
    {domain : EndpointRef headerEnv U headerSource A (.sort level)} →
    {headerLocals : List Nat} → {declaredLeft declaredRight : Subst} → {headerAvailable : Valuation} →
    {ownerInitial : List Closure} → {rawCapture leftValue rightValue : VExpr} → {needs : List Need} →
    RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs →
    RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue needs → Type where
  | nil : RawEntriesRightRebuilt env U registry target .nil .nil
  | cons (head : RawEntryRightRebuilt env U registry target oldHead newHead)
      (tail : RawEntriesRightRebuilt env U registry target oldTail newTail) :
      RawEntriesRightRebuilt env U registry target (.cons oldHead oldTail) (.cons newHead newTail)
end

theorem RawEntriesRightRebuilt.ownerClosures
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {old : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs}
    {next : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue needs}
    (transcript : RawEntriesRightRebuilt env U registry target old next)
    (ordered : sourceEnv.Ordered) (declared : Closure) :
    next.ownerClosures ordered declared = old.ownerClosures ordered declared := by
  match transcript with
  | .nil => rfl
  | .cons head tail =>
    cases head
    simp only [RawRichGroupEntries.ownerClosures, RawRichGroupEntry.owner,
      tail.ownerClosures ordered declared]
termination_by structural transcript

/-- Every occurrence may transport its own annotation along this exact
equality. No equality of scalar budgets is used to identify annotations. -/
theorem RawFrameRightRebuilt.environment
    {context : ContextDerivation sourceEnv U source}
    {old : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {next : RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available}
    (transcript : RawFrameRightRebuilt env U registry target old next)
    (ordered : sourceEnv.Ordered) :
    next.dependencyEnvironment ordered = old.dependencyEnvironment ordered := by
  match transcript with
  | .nil => rfl
  | .diagonal _ => rfl
  | .reserve tail closures =>
    simp only [RawOriginalRichFrame.dependencyEnvironment, tail.environment ordered]
  | .merge left right =>
    simp only [RawOriginalRichFrame.dependencyEnvironment, left.environment ordered, right.environment ordered]
  | .bind tail .. | .capture tail .. =>
    simp only [RawOriginalRichFrame.dependencyEnvironment, tail.environment ordered]
  | .group tail domain capturedOrdered initial entries =>
    simp only [RawOriginalRichFrame.dependencyEnvironment, tail.environment ordered, entries.ownerClosures]
termination_by structural transcript

mutual
/-- Validity includes every selected owner frame, not only the visible tail. -/
theorem RawFrameRightRebuilt.valid
    {context : ContextDerivation sourceEnv U source}
    {old : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {next : RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available}
    (transcript : RawFrameRightRebuilt env U registry target old next)
    (valid : old.Valid) : next.Valid := by
  match transcript with
  | .nil => simp only [RawOriginalRichFrame.Valid]
  | .diagonal _ => exact valid
  | .reserve tail _ | .bind tail .. | .capture tail .. =>
    simp only [RawOriginalRichFrame.Valid] at valid ⊢
    exact tail.valid valid
  | .merge left right =>
    simp only [RawOriginalRichFrame.Valid] at valid ⊢
    exact ⟨left.valid valid.1, right.valid valid.2⟩
  | .group tail _ _ _ entries =>
    simp only [RawOriginalRichFrame.Valid] at valid ⊢
    exact ⟨tail.valid valid.1, entries.valid valid.2⟩
termination_by structural transcript

theorem RawEntryRightRebuilt.valid
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {old : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input}
    {next : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue n input}
    (transcript : RawEntryRightRebuilt env U registry target old next)
    (valid : old.frame.Valid)
    (bound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (old.frame.dependencyEnvironment ordered) ≤
        environmentCost (old.owner.dependencyEnvironment ordered ownerInitial)) :
    next.frame.Valid ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (next.frame.dependencyEnvironment ordered) ≤
          environmentCost (next.owner.dependencyEnvironment ordered ownerInitial)) := by
  match transcript with
  | .mk owner initial frame substitutions rightSubstitutions depth sourcePrefix sourceEq depthEq
      expressionEq leftEq rightEq oldBound oldAdapter oldQuery oldResources oldAnswer newBound
      newAdapter newQuery newResources newAnswer =>
    exact ⟨frame.valid valid, fun ordered => by
      simpa only [RawRichGroupEntry.frame, RawRichGroupEntry.owner, frame.environment ordered] using bound ordered⟩
termination_by structural transcript

theorem RawEntriesRightRebuilt.valid
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {old : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs}
    {next : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue needs}
    (transcript : RawEntriesRightRebuilt env U registry target old next)
    (valid : old.Valid) : next.Valid := by
  match transcript with
  | .nil => simp only [RawRichGroupEntries.Valid]
  | .cons head tail =>
    simp only [RawRichGroupEntries.Valid] at valid ⊢
    have actual := head.valid valid.1 valid.2.1
    exact ⟨actual.1, actual.2, tail.valid valid.2.2⟩
termination_by structural transcript
end

private theorem transportWorlds
    {strata : EquationStratification env} {old next : List Closure}
    (same : old = next) (annotation : WorldEnvironmentProvenance strata U old) :
    (same ▸ annotation : WorldEnvironmentProvenance strata U next).worlds = annotation.worlds := by
  cases same
  rfl

/-- Different uses of one shared base keep their own full annotations while
pointing to the same selected right raw frame. -/
noncomputable def RawFrameRightRebuilt.world
    {strata : EquationStratification env}
    {context : ContextDerivation sourceEnv U source}
    {old : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {next : RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available}
    (transcript : RawFrameRightRebuilt env U registry target old next)
    (controls : OriginalWorldControls strata sourceEnv)
    (annotation : WorldEnvironmentProvenance strata U (old.dependencyEnvironment controls.ordered)) :
    WorldEnvironmentProvenance strata U (next.dependencyEnvironment controls.ordered) :=
  (transcript.environment controls.ordered).symm ▸ annotation

theorem RawFrameRightRebuilt.world_worlds
    {strata : EquationStratification env}
    {context : ContextDerivation sourceEnv U source}
    {old : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {next : RawOriginalRichFrame sourceEnv env U registry target context locals τ τ available}
    (transcript : RawFrameRightRebuilt env U registry target old next)
    (controls : OriginalWorldControls strata sourceEnv)
    (annotation : WorldEnvironmentProvenance strata U (old.dependencyEnvironment controls.ordered)) :
    (transcript.world controls annotation).worlds = annotation.worlds :=
  transportWorlds _ annotation

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
