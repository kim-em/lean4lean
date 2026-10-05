import Lean4Lean.Theory.Typing.AnchoredRecordConstructorPacket
import Lean4Lean.Theory.Typing.AnchoredFamilyLiteralArguments
import Lean4Lean.Theory.Typing.AnchoredConstructorRegisteredResult
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope

/-! Recover the directed eta packet from the actual constructor witness.
Only the new field observations and their original dependent declaration
substitution remain source inputs; all parameter and family guards are
extracted from the existing witness at its real display world. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature
open AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

namespace RankedData

theorem Arguments.take
    (arguments : Arguments env U lower Γ requests left right) (count : Nat) :
    Arguments env U lower Γ (requests.take count) (left.take count) (right.take count) := by
  induction arguments generalizing count with
  | nil => simp only [List.take_nil]; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons head (ih count)

end RankedData

private theorem headerArguments
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    {name family : Name} {levels : List VLevel} {arguments left right : List VExpr}
    (header : ConstructorResultHeader env name family levels arguments)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = header.info.uvars)
    (leftLength : left.length = arguments.length) (rightLength : right.length = arguments.length)
    (raw : Ctx.SubstEq env U Γ (nativeCaptureSubst left)
      (nativeCaptureSubst right) header.domains.reverse) :
    env.IsDefEq U Γ (mkApps (.const name levels) left) (mkApps (.const name levels) right)
      (instantiateParams (mkApps (.const family header.familyLevels) header.familyArguments) left) := by
  let signature : ConstantTelescope (header.info.type.instL levels) :=
    ⟨header.domains, _, header.telescope⟩
  have pair := (signature.prefixArgumentsEqual henv formed
    (.const header.lookup levelsWF levelCount) (Nat.le_refl _)
    (leftLength.trans header.saturated.symm) (rightLength.trans header.saturated.symm)
    (by simpa only [signature, List.take_length] using raw)).1
  simpa only [signature, List.drop_length, wrapForalls, List.foldr_nil, nativeCaptureSubst_spec] using pair

namespace RankedData

/-- The remaining raw tuple is the original declared argument substitution
for the projected fields. Source captures retain its domain alignments;
arbitrary target request domains alone do not determine it. -/
theorem ConstructorWitness.recordPacket
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {sourceLeft sourceRight type : VExpr}
    {demand : ConstructorData (Profile n)}
    (witness : ConstructorWitness env U registry (relations env U registry n)
      Γ sourceLeft sourceRight type demand)
    {info : VProjectionInfo} (registered : env.projections demand.family.name info)
    (constructorName : demand.name = info.ctorName) (unindexed : info.nindices = 0)
    {left right : VExpr}
    (fields : Arguments env U (relations env U registry n) witness.context
      ((demand.arguments.map (DataRequest.rename witness.map)).drop info.nparams)
      (etaFields demand.family.name info.numFields left)
      (etaFields demand.family.name info.numFields right))
    (raw : Ctx.SubstEq env U witness.context
      (nativeCaptureSubst (witness.leftArguments.take info.nparams ++
        etaFields demand.family.name info.numFields left))
      (nativeCaptureSubst (witness.leftArguments.take info.nparams ++
        etaFields demand.family.name info.numFields right)) witness.leftHeader.domains.reverse) :
    Nonempty (RecordConstructorPacket env U registry witness.context
      left right (type.lift' witness.map) (demand.rename witness.map)) := by
  have formed := witness.leftExposure.targetWF henv
  have headTyped := (VExpr.WF.of_mkApps henv formed
    ⟨_, witness.leftExposure.sound.hasType.2⟩).const_inv henv formed
  obtain ⟨constant, lookup, levelsWF, levelCount⟩ := headTyped
  have constantEq : constant = witness.leftHeader.info :=
    Option.some.inj (lookup.symm.trans witness.leftHeader.lookup)
  have registeredConstant := henv.projectionConstructor registered
  rw [← constructorName] at registeredConstant
  have projectionConstant : constant = { uvars := info.uvars, type := info.ctorType } :=
    Option.some.inj (lookup.symm.trans registeredConstant)
  have actualCount : witness.leftLevels.length = info.uvars := by
    simpa only [projectionConstant] using levelCount
  obtain ⟨argumentCount, result⟩ := witness.leftHeader.registered_result_of_name
    henv registered unindexed actualCount constructorName
  have bridge := witness.leftBridge
  rw [result] at bridge
  obtain ⟨level, relevant, familyTyped, familyPacket⟩ :=
    FamilyRelation.literalFormation henv hscoped formed (family := demand.family.rename witness.map) bridge
  have familyArgs := FamilyRelation.literalArguments henv hscoped formed
    (family := demand.family.rename witness.map) bridge
  have familyPath := bridge.typeConversion henv formed
  obtain ⟨familyWitness⟩ := bridge.atBase formed
  have parameterCount : (witness.leftArguments.take info.nparams).length = info.nparams := by
    simp only [List.length_take, Nat.min_eq_left (show info.nparams ≤ witness.leftArguments.length by omega)]
  have expansionCount (major : VExpr) :
      (witness.leftArguments.take info.nparams ++ etaFields demand.family.name info.numFields major).length =
        witness.leftArguments.length := by
    simp only [List.length_append, parameterCount, etaFields, List.length_map, List.length_range]
    exact argumentCount.symm
  let leftHeader : ConstructorResultHeader env demand.name demand.family.name witness.leftLevels
      (witness.leftArguments.take info.nparams ++ etaFields demand.family.name info.numFields left) :=
    { witness.leftHeader with saturated := witness.leftHeader.saturated.trans (expansionCount left).symm }
  let rightHeader : ConstructorResultHeader env demand.name demand.family.name witness.leftLevels
      (witness.leftArguments.take info.nparams ++ etaFields demand.family.name info.numFields right) :=
    { witness.leftHeader with saturated := witness.leftHeader.saturated.trans (expansionCount right).symm }
  have leftResult : leftHeader.result = mkApps (.const demand.family.name witness.leftLevels)
      (witness.leftArguments.take info.nparams) := by
    have equality := (leftHeader.registered_result_of_name henv registered unindexed actualCount constructorName).2
    rw [List.take_append_of_le_length (show info.nparams ≤ (witness.leftArguments.take info.nparams).length by omega),
      List.take_take, Nat.min_self] at equality
    exact equality
  have rightResult : rightHeader.result = mkApps (.const demand.family.name witness.leftLevels)
      (witness.leftArguments.take info.nparams) := by
    have equality := (rightHeader.registered_result_of_name henv registered unindexed actualCount constructorName).2
    rw [List.take_append_of_le_length (show info.nparams ≤ (witness.leftArguments.take info.nparams).length by omega),
      List.take_take, Nat.min_self] at equality
    exact equality
  have pair := headerArguments henv formed witness.leftHeader levelsWF
    (by simpa only [← constantEq] using levelCount) (expansionCount left) (expansionCount right) raw
  change env.IsDefEq U witness.context _ _ leftHeader.result at pair
  rw [leftResult] at pair
  refine ⟨{
    info := info, registered := registered, constructorName := constructorName
    unindexed := unindexed, levels := witness.leftLevels, constructorPacket := witness.leftUniverses
    parameterRequests := (demand.arguments.map (DataRequest.rename witness.map)).take info.nparams
    fieldRequests := (demand.arguments.map (DataRequest.rename witness.map)).drop info.nparams
    parameters := witness.leftArguments.take info.nparams
    parameterCount := parameterCount, argumentShape := ?_
    parameterAdmissions := (witness.arguments.left_diagonal
      (fun _ _ _ _ _ _ related => Related.left_diagonal related)).take info.nparams
    fieldAdmissions := fields
    familyDefinitions := familyWitness.headInert.definition
    familyNatives := familyWitness.headInert.native
    familyQuotient := familyWitness.headInert.quotient
    familyPacket := familyPacket, familyLevel := level, familyTyped := familyTyped
    familyRelevant := relevant, familyAdmissions := familyArgs, assignedFamily := familyPath.symm
    leftExpansionTyped := pair.hasType.1, rightExpansionTyped := pair.hasType.2
    leftHeader := leftHeader, rightHeader := rightHeader
    leftResult := leftResult, rightResult := rightResult }⟩
  exact (List.take_append_drop info.nparams _).symm

end RankedData
end Lean4Lean.AnchoredSemantics
