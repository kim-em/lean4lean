import Lean4Lean.Theory.Typing.AnchoredConstructorConsumedCaptures
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginReduction
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureSubstitution

/-! Raw eta tuple replay follows each original declaration-domain alignment.
Projection congruence changes the major at an unchanged frozen field domain;
no source semantic theorem for a synthesized projection is required. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private substitution_of_lookups from Lean4Lean.Theory.Typing.AnchoredFamilyCaptureSubstitution
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

inductive RequestPairs (env : VEnv) (U : Nat) (target : List VExpr) :
    List (DataRequest (Profile n)) → List VExpr → List VExpr → Prop where
  | nil : RequestPairs env U target [] [] []
  | cons (pair : env.IsDefEq U target left right request.domain)
      (tail : RequestPairs env U target requests lefts rights) :
      RequestPairs env U target (request :: requests) (left :: lefts) (right :: rights)

theorem RequestPairs.append
    (first : RequestPairs env U target requests left right)
    (second : RequestPairs env U target requests' left' right') :
    RequestPairs env U target (requests ++ requests') (left ++ left') (right ++ right') := by
  induction first with
  | nil => exact second
  | cons pair _ ih => exact .cons pair (ih second)

theorem RequestPairs.length
    (pairs : RequestPairs env U target requests left right) : left.length = right.length := by
  induction pairs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem RequestPairs.take
    (pairs : RequestPairs env U target requests left right) (count : Nat) :
    RequestPairs env U target (requests.take count) (left.take count) (right.take count) := by
  induction pairs generalizing count with
  | nil => simp only [List.take_nil]; exact .nil
  | cons pair _ ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons pair (ih count)

theorem RequestPairs.ofArguments
    (arguments : RankedData.Arguments env U lower target requests left right) :
    RequestPairs env U target requests left right := by
  induction arguments with
  | nil => exact .nil
  | cons first _ ih => exact .cons first.2.1 ih

/-- Every field keeps its own literal projection typing origin; this covers
fields with empty computational requests as well as observed data fields. -/
theorem RequestPairs.projections
    {requests : List (DataRequest (Profile n))} {indices : List Nat}
    (origins : List.Forall₂ (fun index request => Nonempty
      (RankedData.ProjectionOrigin env U target info name index left assignedType request.domain))
      indices requests)
    (majorPair : env.IsDefEq U target left right assignedType) :
    RequestPairs env U target requests (indices.map (fun index => .proj name index left))
      (indices.map (fun index => .proj name index right)) := by
  induction origins with
  | nil => exact .nil
  | cons origin _ ih =>
    obtain ⟨origin⟩ := origin
    exact .cons (origin.congr majorPair) ih

theorem ConstructorSourceCaptures.actualPairs
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))}
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available expressions requests) :
    RequestPairs env U target requests
      (expressions.map (·.subst (replacement.comp realization)))
      (expressions.map (·.subst (replacement.comp realization))) := by
  induction captures with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.pair.hasType.2 ih

theorem ConstructorConsumedCaptures.actualPairs
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    {consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments requested}
    (packet : ConstructorConsumedCaptures consumed) :
    RequestPairs env U target packet.requests (arguments.map (·.subst σ)) (arguments.map (·.subst σ)) := by
  have pairs := packet.sourceCaptures.actualPairs
  rw [consumed.length] at pairs
  have original : (constantCaptureVariables arguments.length).map
      (·.subst (nativeCaptureSubst arguments)) = arguments := by
    simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
  have exactArguments : (constantCaptureVariables arguments.length).map
      (·.subst ((nativeCaptureSubst arguments).comp σ)) = arguments.map (·.subst σ) := by
    simpa only [List.map_map, Function.comp_def, subst_subst] using
      congrArg (List.map (·.subst σ)) original
  rwa [exactArguments] at pairs

private theorem ConstructorSourceCaptures.rawLookup
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))}
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available expressions requests)
    (pairs : RequestPairs env U target requests
      (expressions.map (·.subst (replacement.comp realization))) (expressions.map (·.subst next)))
    (member : .bvar index ∈ expressions) (lookup : Lookup source index type) :
    env.IsDefEq U target (seed index) (next index) (type.subst seed) := by
  match captures with
  | .nil => cases member
  | .cons head tail =>
    cases pairs with
    | cons pair rest =>
      rcases List.mem_cons.mp member with same | later
      · cases same
        cases head.lookup.uniq lookup
        exact head.alignment.path.cast (head.pair.trans pair)
      · exact tail.rawLookup rest later lookup
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

/-- Reconstruct the declaration substitution using the original finite
capture ledger. The pair at a frozen field domain is cast only along its
retained declaration DomainChain. -/
theorem ConstructorSourceCaptures.rawSubstitution
    {requests : List (DataRequest (Profile n))}
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available (constantCaptureVariables source.length) requests)
    (formed : OnCtx source (env.IsType U))
    (pairs : RequestPairs env U target requests
      ((constantCaptureVariables source.length).map (·.subst (replacement.comp realization)))
      ((constantCaptureVariables source.length).map (·.subst next))) :
    Ctx.SubstEq env U target seed next source := by
  apply substitution_of_lookups formed
  intro index type lookup
  apply captures.rawLookup pairs ?_ lookup
  simp only [constantCaptureVariables, List.mem_map, List.mem_reverse, List.mem_range]
  exact ⟨index, lookup.lt, rfl⟩

/-- Right expansion typing follows from actual left expansion arguments,
the original declaration substitution, and the finitely aligned field pairs.
The result conversion is explicit; no equality of independently assigned
constructor or projection types is inferred. -/
theorem ConstructorConsumedCaptures.expansionPair
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    {consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments requested}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (packet : ConstructorConsumedCaptures consumed)
    (lookup : env.constants name = some info)
    (full : arguments.length = consumed.signature.domains.length)
    {newValues : List VExpr} (length : newValues.length = arguments.length)
    (pairs : RequestPairs env U target packet.requests (arguments.map (·.subst σ)) newValues)
    {assigned : VExpr}
    (resultPath : TypeConversion env U target
      (consumed.signature.result.subst (nativeCaptureSubst (arguments.map (·.subst σ)))) assigned) :
    env.IsDefEq U target (mkApps (.const name consumed.seedLevels) (arguments.map (·.subst σ)))
      (mkApps (.const name consumed.seedLevels) newValues) assigned := by
  have captures := packet.sourceCaptures
  have count : consumed.anchors.length = consumed.signature.domains.reverse.length := by
    rw [List.length_reverse, consumed.length, full]
  rw [count] at captures
  have before := consumed.raw
  rw [full, List.take_length] at before
  have leftVars :
      (constantCaptureVariables consumed.signature.domains.reverse.length).map
        (·.subst ((nativeCaptureSubst arguments).comp σ)) = arguments.map (·.subst σ) := by
    rw [List.length_reverse, ← full]
    have original : (constantCaptureVariables arguments.length).map
        (·.subst (nativeCaptureSubst arguments)) = arguments := by
      simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
    simpa only [List.map_map, Function.comp_def, subst_subst] using congrArg (List.map (·.subst σ)) original
  have rightVars :
      (constantCaptureVariables consumed.signature.domains.reverse.length).map
        (·.subst (nativeCaptureSubst newValues)) = newValues := by
    rw [List.length_reverse, ← full, ← length]
    simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars newValues
  have after := captures.rawSubstitution (next := nativeCaptureSubst newValues) before.wf (by rwa [leftVars, rightVars])
  have constant : env.HasType U [] (.const name consumed.seedLevels)
      (info.type.instL consumed.seedLevels) := .const lookup consumed.seedWF consumed.seedLength
  have old := consumed.signature.prefixArgumentsEqual
    (left := consumed.anchors) (right := arguments.map (·.subst σ)) henv hTarget constant (Nat.le_refl _)
    (consumed.length.trans full) (by simpa only [List.length_map] using full)
    (by simpa only [List.take_length] using before)
  have new := consumed.signature.prefixArgumentsEqual
    (left := consumed.anchors) (right := newValues) henv hTarget constant (Nat.le_refl _)
    (consumed.length.trans full) (length.trans full)
    (by simpa only [List.take_length] using after)
  simp only [List.drop_length, wrapForalls, List.foldr_nil] at old new
  exact resultPath.cast (old.2.cast (old.1.symm.trans new.1))

/-- The right eta tuple uses the same original parameters and the actual
projections of the new major. Empty field inputs still retain their raw
projection origins, so every declared argument remains well typed. -/
theorem ConstructorConsumedCaptures.projectedExpansionPair
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {constantInfo : VConstant} {constructorName : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : ConstructorData (Profile n)}
    {consumed : ConstructorPlanConsumption env U registry target locals σ available constantInfo constructorName levels
      arguments (n := n + 1) (.ctor demand)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (packet : ConstructorConsumedCaptures consumed)
    (lookup : env.constants constructorName = some constantInfo)
    {projectionInfo : VProjectionInfo} {familyName : Name} {left right assignedType : VExpr}
    {parameters : List VExpr}
    (leftShape : arguments.map (·.subst σ) = parameters ++
      (List.range projectionInfo.numFields).map (fun index => .proj familyName index left))
    (origins : List.Forall₂ (fun index request => Nonempty
      (RankedData.ProjectionOrigin env U target projectionInfo familyName index left assignedType request.domain))
      (List.range projectionInfo.numFields) (packet.requests.drop parameters.length))
    (majorPair : env.IsDefEq U target left right assignedType)
    {resultType : VExpr}
    (resultPath : TypeConversion env U target
      (consumed.signature.result.subst (nativeCaptureSubst (arguments.map (·.subst σ)))) resultType) :
    env.IsDefEq U target
      (mkApps (.const constructorName consumed.seedLevels)
        (parameters ++ (List.range projectionInfo.numFields).map (fun index => .proj familyName index left)))
      (mkApps (.const constructorName consumed.seedLevels)
        (parameters ++ (List.range projectionInfo.numFields).map (fun index => .proj familyName index right)))
      resultType := by
  have parameterPairs := packet.actualPairs.take parameters.length
  rw [leftShape] at parameterPairs
  simp only [List.take_left] at parameterPairs
  have fieldPairs := RequestPairs.projections origins majorPair
  have pairs := parameterPairs.append fieldPairs
  rw [List.take_append_drop, ← leftShape] at pairs
  have pair := packet.expansionPair henv hTarget lookup
    (consumed.saturated henv hscoped hTarget)
    (by simpa only [List.length_map] using pairs.length.symm) pairs resultPath
  simpa only [leftShape] using pair

end Lean4Lean.AnchoredSource.Adapted
