import Lean4Lean.Theory.Typing.AnchoredOriginalTailConstant
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplayTransport

/-! Constant coherence passes through the literal declaration header at the
displayed universe levels. Inward and outward conversions use only the
finite original equality children retained by the two endpoint packets.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Restore a primitive constant endpoint from its displayed header. The
left endpoint consumes the incoming answer unchanged; the right endpoint
uses the original ambient header equality in the reverse direction. -/
theorem EndpointRef.restoreConstant
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel} {assigned : VExpr} {info : VConstant}
    (lookup : env.constants name = some info)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) (calls : ConstantCall.Fundamentals env registry reference initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : CodeTransferResult env U registry target locals leftSubst σ available
      inputType (info.type.instL levels) profile) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst σ available
      inputType assigned profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    case constDF actualLookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      cases expressionEq
      have same := Option.some.inj (lookup.symm.trans (below.constants actualLookup))
      cases same
      exact ⟨incoming⟩
    all_goals cases expressionEq
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    case constDF actualLookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      cases expressionEq
      have same := Option.some.inj (lookup.symm.trans (below.constants actualLookup))
      cases same
      have answerPair := calls .right target locals σ σ available closed hTarget substitutions
        (TailPairedFits.diagonal initial fits)
      obtain ⟨answer⟩ := incoming.certificate.transfer_graded henv hscoped hTarget closed
        answerPair.2.1 incoming.available
      exact ⟨⟨answer.footprint, answer.certificate, answer.available,
        incoming.related.trans henv answer.related⟩⟩
    all_goals cases expressionEq

/-- The primitive constant restoration is followed by the actual finite
outward conversion route to the caller's assigned source type. -/
theorem ConstantPrefix.restore
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel} {info : VConstant}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) (lookup : env.constants name = some info)
    (calls : ConstantPrefixCall.Fundamentals env registry packet initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : CodeTransferResult env U registry target locals leftSubst σ available
      inputType (info.type.instL levels) profile) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst σ available
      inputType assigned profile) := by
  obtain ⟨natural⟩ := EndpointRef.restoreConstant henv hscoped below initial closed hTarget
    substitutions fits lookup packet.reference rfl packet.primitive
    (fun call => calls (.ambient call)) incoming
  exact packet.route.restoreOriginal henv hscoped below initial closed hTarget substitutions fits
    (fun call => calls (.conversion call)) natural


/-- Compare two actual constant endpoints through their common declaration
header. Source certificate transport uses only the existing common display;
its header is closed by the actual declaration's formation theorem. -/
theorem ConstantPrefix.compare
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    {leftSource rightSource target : List VExpr} {leftLocals rightLocals : List Nat}
    {σ τ : Subst} {leftAvailable rightAvailable commonAvailable : Valuation}
    (leftInitial : ContextDerivation leftEnv U leftSource)
    (rightInitial : ContextDerivation rightEnv U rightSource)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (leftFits : TailFits leftEnv env U registry target leftSource leftLocals σ σ leftAvailable)
    (rightFits : TailFits rightEnv env U registry target rightSource rightLocals τ τ rightAvailable)
    {name : Name} {levels : List VLevel}
    {left : EndpointState leftEnv U leftSource (.const name levels) leftAssigned}
    {right : EndpointState rightEnv U rightSource (.const name levels) rightAssigned}
    (leftPacket : ConstantPrefix left) (rightPacket : ConstantPrefix right)
    (leftCalls : ConstantPrefixCall.Fundamentals env registry leftPacket leftInitial)
    (rightCalls : ConstantPrefixCall.Fundamentals env registry rightPacket rightInitial)
    (leftMap rightMap : Lift) (common : Subst) (commonLocals : List Nat)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index))
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target leftLocals σ leftAssigned profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned rightAssigned profile) := by
  obtain ⟨header⟩ := leftPacket.replayOriginal henv hscoped leftBelow leftInitial leftClosed hTarget
    leftSubstitutions leftFits leftCalls certificate resources
  have lookup := leftBelow.constants header.lookup
  have headerClosed : (header.info.type.instL levels).Closed := by
    obtain ⟨level, formation⟩ := henv.constWF lookup
    exact (VExpr.WF.closedN henv ⟨_, formation⟩ trivial).instL
  obtain ⟨required, ⟨transported⟩, available⟩ := OriginalFactorCut.CodeCert.betweenDisplays
    header.transfer.certificate leftMap rightMap common leftRealization rightRealization
    (show (header.info.type.instL levels).lift' leftMap =
      (header.info.type.instL levels).lift' rightMap from by
        rw [headerClosed.lift'_eq .zero, headerClosed.lift'_eq .zero])
    commonLocals rightLocals header.transfer.available leftAvailableEq rightAvailableEq
  have incoming : CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned (header.info.type.instL levels) profile := {
    footprint := required, certificate := transported, available := available
    related := by
      simpa only [headerClosed.subst_eq (σ := σ) .zero,
        headerClosed.subst_eq (σ := τ) .zero] using header.transfer.related }
  exact rightPacket.restore henv hscoped rightBelow rightInitial rightClosed hTarget
    rightSubstitutions rightFits lookup rightCalls incoming


/-- Recover the actual declaration lookup from the original primitive rule. -/
theorem EndpointRef.constantLookup
    (reference : EndpointRef sourceEnv U source expression assigned)
    {name : Name} {levels : List VLevel}
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) :
    ∃ info, sourceEnv.constants name = some info := by
  cases reference <;> rename_i original <;>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
  all_goals try contradiction
  all_goals cases expressionEq
  all_goals exact ⟨_, by assumption⟩

/-- Raw header alignment uses the retained ambient equality directly. It
requires no semantic query, including at an empty requested support. -/
theorem EndpointRef.constantTargetPath
    {sourceEnv env : VEnv} {U : Nat}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    {source target : List VExpr} {σ : Subst}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    {name : Name} {levels : List VLevel} {assigned : VExpr} {info : VConstant}
    (lookup : env.constants name = some info)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) :
    TypeConversion env U target (assigned.subst σ) ((info.type.instL levels).subst σ) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    case constDF actualLookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      cases expressionEq
      have same := Option.some.inj (lookup.symm.trans (below.constants actualLookup))
      cases same
      exact .refl
    all_goals cases expressionEq
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    case constDF actualLookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      cases expressionEq
      have same := Option.some.inj (lookup.symm.trans (below.constants actualLookup))
      cases same
      exact .single ((ambient.forget.defeq.mono below).substDF henv
        substitutions.wf hTarget substitutions)
    all_goals cases expressionEq

/-- Follow all actual original conversion nodes and the primitive ambient
header equality from the assigned type to the canonical displayed header. -/
theorem ConstantPrefix.targetPath
    {sourceEnv env : VEnv} {U : Nat}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    {source target : List VExpr} {σ : Subst}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    {name : Name} {levels : List VLevel} {info : VConstant}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) (lookup : env.constants name = some info) :
    TypeConversion env U target (assigned.subst σ) ((info.type.instL levels).subst σ) :=
  (packet.route.targetPath henv below hTarget substitutions).trans
    (EndpointRef.constantTargetPath henv below hTarget substitutions lookup
      packet.reference rfl packet.primitive)

/-- Both original assigned types convert to the same closed literal header.
This path is independent of support, source footprints and semantic answers. -/
theorem ConstantPrefix.comparePath
    {leftEnv rightEnv env : VEnv} {U : Nat}
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    {leftSource rightSource target : List VExpr} {σ τ : Subst}
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    {name : Name} {levels : List VLevel}
    {left : EndpointState leftEnv U leftSource (.const name levels) leftAssigned}
    {right : EndpointState rightEnv U rightSource (.const name levels) rightAssigned}
    (leftPacket : ConstantPrefix left) (rightPacket : ConstantPrefix right) :
    TypeConversion env U target (leftAssigned.subst σ) (rightAssigned.subst τ) := by
  obtain ⟨info, sourceLookup⟩ := EndpointRef.constantLookup
    leftPacket.reference rfl leftPacket.primitive
  have lookup := leftBelow.constants sourceLookup
  have headerClosed : (info.type.instL levels).Closed := by
    obtain ⟨level, formation⟩ := henv.constWF lookup
    exact (VExpr.WF.closedN henv ⟨_, formation⟩ trivial).instL
  have forward := leftPacket.targetPath henv leftBelow hTarget leftSubstitutions lookup
  have backward := rightPacket.targetPath henv rightBelow hTarget rightSubstitutions lookup
  rw [headerClosed.subst_eq .zero] at forward backward
  exact forward.trans backward.symm

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
