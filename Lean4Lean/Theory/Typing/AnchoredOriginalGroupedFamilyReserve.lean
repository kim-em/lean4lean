import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedHeaderReserve
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture

/-! Separate reserves for the family declaration followed through an actual
major. The constructor telescope and family telescope are distinct original
headers. This bound uses the actual family header's retained dependency in
the major, while preserving the constructor-prefix reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- Every captured family slot is charged before interpreting its owners.
The selected family's original header need only be a retained dependency of
the actual major; it need not equal the constructor header. -/
theorem grouped_projection_family_prefix_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (headerFormed : headerEnv.Ordered)
    (header : EndpointRef headerEnv U [] headerExpression headerType)
    (headerBound : (header.dependencyOrigin headerFormed).weight ≤ (major.dependencyOrigin formed).weight)
    (steps : List (GroupedHeaderStep headerFormed formed header field (.left major)))
    (lengthBound : steps.length ≤ (params ++ indices).length)
    (selectedHeader : LocatedOrigin headerFormed header)
    (selectedOwner : Sum (LocatedOrigin formed field) (LocatedOrigin formed (.left major)))
    (initial : List Closure) :
    richSchedule .expressionReindex
      ((groupedOwnerClosure selectedOwner initial).cost +
       (Closure.close (selectedHeader.node.dependencyOrigin headerFormed)
         (groupedHeaderEnvironment steps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (grouped_header_pair_bound steps selectedHeader selectedOwner initial)
  have headerBound' : (header.dependencyOrigin headerFormed).weight ≤
      (field.dependencyOrigin formed).weight + (major.dependencyOrigin formed).weight := by omega
  have countBound : steps.length ≤ info.nparams + info.nindices := by
    simpa only [List.length_append, parameterCount, indexCount] using lengthBound
  have powerBound : ((header.dependencyOrigin headerFormed).weight + 2) ^ steps.length ≤
      ((field.dependencyOrigin formed).weight + (major.dependencyOrigin formed).weight + 2) ^
        (info.nparams + info.nindices) :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega) steps.length)
      (Nat.pow_le_pow_right (by omega) countBound)
  have reserveBound : (header.dependencyOrigin headerFormed).weight *
      headerCaptureReserve (header.dependencyOrigin headerFormed).weight
        (field.dependencyOrigin formed).weight (major.dependencyOrigin formed).weight steps.length ≤
      projectionFamilyReserve (info.nparams + info.nindices)
        (field.dependencyOrigin formed).weight (major.dependencyOrigin formed).weight :=
    Nat.mul_le_mul headerBound' (Nat.mul_le_mul_right _ powerBound)
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    projectionDependencyReserve]
  simp only [EndpointRef.dependencyOrigin] at reserveBound
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A semantic capture group has a pre-answer ledger containing exactly
its original domain and owner locations. No certificate size enters it. -/
noncomputable def RichGroupedCapture.ledgerStep
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (location : Located header (.ref domain))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    Dependency.GroupedHeaderStep headerOrdered ordered header field major := {
  domain := ⟨headerSource, A, .sort level, .ref domain, location⟩
  owners := .inl ⟨_, _, _, .ref field, .here⟩ :: .inr ⟨_, _, _, .ref major, .here⟩ ::
    entries.map (fun entry => entry.owner.map (Dependency.measureLocated ordered)
    (Dependency.measureLocated ordered)) }

/-- Extending an actual frame extends the exact ledger by one declared slot,
regardless of the number of queries retained in that slot. -/
theorem OriginalRichFrame.group_ledger
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (location : Located header (.ref domain))
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (steps : List (Dependency.GroupedHeaderStep headerOrdered ordered header field major))
    (ledger : tail.dependencyEnvironment headerOrdered = Dependency.groupedHeaderEnvironment steps ownerInitial) :
    (tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered =
      Dependency.groupedHeaderEnvironment (entries.ledgerStep ordered headerOrdered location :: steps) ownerInitial := by
  rw [OriginalRichFrame.group_environment, ledger]
  have owners : ∀ declared : Closure,
      entries.map (fun entry => Closure.bundle (entry.owner.dependencyClosure ordered ownerInitial) declared) =
      entries.map (fun entry => Closure.bundle
        (Dependency.groupedOwnerClosure (entry.owner.map (Dependency.measureLocated ordered)
          (Dependency.measureLocated ordered)) ownerInitial) declared) := by
    intro declared
    apply List.map_congr_left
    intro entry _
    cases entry.owner <;> rfl
  simp only [RichGroupedCapture.environment, Dependency.groupedHeaderEnvironment,
    RichGroupedCapture.ledgerStep, List.map_cons, List.map_map, Function.comp_def, EndpointState.dependencyOrigin]
  rw [← owners]
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
