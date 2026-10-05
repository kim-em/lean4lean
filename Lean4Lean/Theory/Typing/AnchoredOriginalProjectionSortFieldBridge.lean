import Lean4Lean.Theory.Typing.AnchoredOriginalRichSortTransfer
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaSortNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalDirectionalTrans
import Lean4Lean.Theory.Typing.AnchoredRecordTrace
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! A productive dependent-record base case.  The prior field has a literal
universe as its declared type.  Its two actual projection occurrences may
retain unrelated hidden source majors.  The assigned certificate is rebuilt
from the actual input certificate; no assigned-comparison answer is assumed.

The five ordinary F/R clauses remain explicit lower-induction obligations.
Their computed endpoint-world funding does not itself prove preservation of
query-owned foreign-world sponsors.  Nor does this native leaf theorem claim
to factor every wrapper of an arbitrary incoming rich certificate.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private def castCertificate
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (same : expression = other) :
    RichCert sourceEnv env U registry target (node.cast same rfl) locals σ relevant profile footprint := by
  cases same
  exact certificate

theorem ProjectionHead.sortFieldReply
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (leftLiteral : leftHead.fieldType = .sort leftLevel)
    (rightLiteral : rightHead.fieldType = .sort rightLevel)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : leftAvailable.AtomClosed)
    (leftWF : leftLevel.WF U) (rightWF : rightLevel.WF U)
    (levels : leftLevel ≈ rightLevel)
    (certificate : RichCert leftEnv env U registry target leftHead.field leftLocals σ
      true (support : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    ∃ answer : RichProjectionAssignedReply leftHead rightHead env registry target
        rightLocals σ τ rightAvailable support,
      answer.code.footprint = [] ∧ ∀ policy, answer.code.certificate.headDepth policy = 0 := by
  have source : RichCert leftEnv env U registry target
      (leftHead.field.cast leftLiteral rfl) leftLocals σ true support footprint := castCertificate certificate leftLiteral
  obtain ⟨answer⟩ := RichCodeTransfer.literalSort
    (left := leftHead.field.cast leftLiteral rfl)
    (right := rightHead.field.cast rightLiteral rfl)
    (rightLocals := rightLocals) (τ := τ) (rightAvailable := rightAvailable)
    henv hscoped formed closed leftWF rightWF levels source resources
  have rightCode : TypeRelated env U registry target (.sort rightLevel) (.sort rightLevel) support := by
    exact (answer.related.symm henv certificate.formed.wf_value).left_diagonal
  obtain ⟨query, depth⟩ := TypeRelated.literalSortCertificateAt
    (node := rightHead.field) (locals := rightLocals) (σ := τ)
    rightLiteral formed rightCode certificate.formed
  refine ⟨{
    path := ?_
    code := {
      footprint := []
      certificate := query
      resources := fun _ _ member => nomatch member
      related := ?_ } }, rfl, depth⟩
  · simpa only [leftLiteral, rightLiteral, subst_sort] using
      (show TypeConversion env U target (.sort leftLevel) (.sort rightLevel) from
        .single (.sortDF leftWF rightWF levels))
  · simpa only [leftLiteral, rightLiteral, subst_sort] using answer.related

open private MixedInsertion.eqBack from Lean4Lean.Theory.Typing.AnchoredRecordTrace

private theorem recordProjectionRaw
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (related : Related env U registry target left right assigned
      (Profile.singleton (n := n + 1) (.record record)) support)
    (member : (index, request) ∈ record.fields) :
    env.IsDefEq U target (.proj record.family.name index left)
      (.proj record.family.name index right) request.domain := by
  obtain ⟨witness⟩ := related.recordRelation henv hscoped formed target .refl (.refl formed)
  have rename : record.rename .refl = record := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  have admitted := witness.fields.map_member member
  apply MixedInsertion.eqBack henv witness.insertion
  exact admitted.2.1

/-- The semantic five-leg bridge transports the entire frozen record,
including all of its support requests.  The R inputs and outputs are the
actual retained major occurrences, and the two F calls use the original
outer equalities in opposite directions.  World funding is supplied by the
concrete outer-projection caller; this lemma does not assert a sum-cost bound.
-/
theorem ProjectionHead.recordMajorBridge
    {left : EndpointState leftEnv U leftSource (.proj name index displayedLeft) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index displayedRight) rightType}
    (outerLeft : ProjectionHead left) (outerRight : ProjectionHead right)
    {leftHole : EndpointState leftEnv U leftSource (.proj name prior leftMajor) leftHoleType}
    {rightHole : EndpointState rightEnv U rightSource (.proj name prior rightMajor) rightHoleType}
    (holeLeft : ProjectionHead leftHole) (holeRight : ProjectionHead rightHole)
    (leftMajorEq : leftMajor = outerLeft.sourceMajor)
    (rightMajorEq : rightMajor = outerRight.sourceMajor)
    (displayedEq : displayedLeft.subst σ = displayedRight.subst τ)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (prior, request) ∈ record.fields)
    (query : RichObs leftEnv env U registry target (.ref (.right holeLeft.major))
      leftLocals σ (Profile.singleton (n := n + 1) (.record record)) footprint)
    (resources : footprint.Available leftAvailable)
    (firstR : ∀ {fp},
      RichObs leftEnv env U registry target (.ref (.right holeLeft.major))
        leftLocals σ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available leftAvailable →
      Nonempty (RichGradedResult leftEnv env U registry target (.ref (.left outerLeft.major))
        leftLocals σ leftAvailable (Profile.singleton (n := n + 1) (.record record))))
    (forwardF : ∀ {fp},
      RichObs leftEnv env U registry target (.ref (.left outerLeft.major))
        leftLocals σ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available leftAvailable →
      Nonempty (OriginalDirectionalEqualityResult outerLeft.major true env registry target
        leftLocals σ σ leftAvailable (Profile.singleton (n := n + 1) (.record record))))
    (middleR : ∀ {fp},
      RichObs leftEnv env U registry target (.ref (.right outerLeft.major))
        leftLocals σ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target (.ref (.right outerRight.major))
        rightLocals τ rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (backwardF : ∀ {fp},
      RichObs rightEnv env U registry target (.ref (.right outerRight.major))
        rightLocals τ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available rightAvailable →
      Nonempty (OriginalDirectionalEqualityResult outerRight.major false env registry target
        rightLocals τ τ rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (lastR : ∀ {fp},
      RichObs rightEnv env U registry target (.ref (.left outerRight.major))
        rightLocals τ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available rightAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target (.ref (.right holeRight.major))
        rightLocals τ rightAvailable (Profile.singleton (n := n + 1) (.record record)))) :
    ∃ fp, ∃ _output : RichObs rightEnv env U registry target (.ref (.right holeRight.major))
        rightLocals τ (Profile.singleton (n := n + 1) (.record record)) fp,
      fp.Available rightAvailable ∧
      Related env U registry target ((VExpr.proj name prior leftMajor).subst σ)
        ((VExpr.proj name prior rightMajor).subst τ) request.domain request.input request.support ∧
      env.IsDefEq U target ((VExpr.proj name prior leftMajor).subst σ)
        ((VExpr.proj name prior rightMajor).subst τ) request.domain := by
  obtain ⟨first⟩ := firstR query resources
  obtain ⟨_, ⟨firstQuery⟩, firstResources⟩ := first.recordObservation henv
  obtain ⟨forward⟩ := forwardF firstQuery firstResources
  obtain ⟨_, ⟨forwardQuery⟩, forwardResources⟩ := forward.rightQuery.recordObservation henv
  obtain ⟨middle⟩ := middleR forwardQuery forwardResources
  obtain ⟨_, ⟨middleQuery⟩, middleResources⟩ := middle.recordObservation henv
  obtain ⟨backward⟩ := backwardF middleQuery middleResources
  obtain ⟨_, ⟨backwardQuery⟩, backwardResources⟩ := backward.rightQuery.recordObservation henv
  obtain ⟨last⟩ := lastR backwardQuery backwardResources
  obtain ⟨fp, ⟨output⟩, available⟩ := last.recordObservation henv
  have firstRelated := forward.related.projectRecord henv hscoped formed member
  have lastRelated := backward.related.projectRecord henv hscoped formed member
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, nameEq] at firstRelated lastRelated
  have combined := firstRelated.trans henv hscoped (by
    simpa only [displayedEq] using lastRelated)
  have firstRaw := recordProjectionRaw henv hscoped formed forward.related member
  have lastRaw := recordProjectionRaw henv hscoped formed backward.related member
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, nameEq]
    at firstRaw lastRaw
  have combinedRaw := firstRaw.trans (by simpa only [displayedEq] using lastRaw)
  exact ⟨fp, output, available, by
    simpa only [subst_proj, leftMajorEq, rightMajorEq] using combined, by
    simpa only [subst_proj, leftMajorEq, rightMajorEq] using combinedRaw⟩


private theorem ofCast_depth
    {node : EndpointState sourceEnv U source expression assigned}
    (equal : expression = nextExpression)
    (query : RichCert sourceEnv env U registry target (node.cast equal rfl)
      locals σ relevant profile footprint) (policy : Name → Nat → Nat) :
    (RichCert.ofCast equal rfl query).headDepth policy = query.headDepth policy := by
  cases equal
  rfl

/-- A dependent Pack field whose instantiated type is the prior projected
universe. The five recursive clauses are guarded by the actual world
frontiers proved from these very outer/inner originals. The requested
support can be nonempty and is kept verbatim. No assigned-C result occurs
among the premises. The output has exactly the final major query's
footprint and head depth, so the sort-field transfer introduces no capture.
-/
theorem ProjectionHead.packCodeBridge
    {env : VEnv} {strata : EquationStratification env}
    {left : EndpointState leftEnv U leftSource (.proj name index displayedLeft) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index displayedRight) rightType}
    (outerLeft : ProjectionHead left) (outerRight : ProjectionHead right)
    (leftDisplay : outerLeft.fieldType = .proj name prior leftMajor)
    (rightDisplay : outerRight.fieldType = .proj name prior rightMajor)
    (leftInner : ProjectionHead (outerLeft.field.cast leftDisplay rfl))
    (rightInner : ProjectionHead (outerRight.field.cast rightDisplay rfl))
    (leftMajorEq : leftMajor = outerLeft.sourceMajor)
    (rightMajorEq : rightMajor = outerRight.sourceMajor)
    (displayedEq : displayedLeft.subst σ = displayedRight.subst τ)
    (leftLiteral : leftInner.fieldType = .sort leftLevel)
    (rightLiteral : rightInner.fieldType = .sort rightLevel)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (leftCaptured : WorldEnvironmentProvenance strata U
      (leftFrame.dependencyEnvironment leftControls.ordered))
    (rightCaptured : WorldEnvironmentProvenance strata U
      (rightFrame.dependencyEnvironment rightControls.ordered))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : leftAvailable.AtomClosed)
    (levels : leftLevel ≈ rightLevel)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (prior, request) ∈ record.fields)
    (query : RichObs leftEnv env U registry target (.ref (.right leftInner.major))
      leftLocals σ (Profile.singleton (n := n + 1) (.record record)) footprint)
    (resources : footprint.Available leftAvailable)
    (fieldCode : RichCert leftEnv env U registry target leftInner.field leftLocals σ true support fieldFootprint)
    (fieldResources : fieldFootprint.Available leftAvailable)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (leftInner.fieldType.subst σ))
    (sorted : request.input.HasType (.sort relevant))
    (firstR : EquationWorldClosureOrder.CallBelow strata.rules.length
      [originalCallWorld leftControls .expressionReindex (.ref (.right leftInner.major)) leftCaptured,
        originalCallWorld leftControls .expressionReindex (.ref (.left outerLeft.major)) leftCaptured]
      [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] → ∀ {fp},
      RichObs leftEnv env U registry target (.ref (.right leftInner.major))
        leftLocals σ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available leftAvailable →
      Nonempty (RichGradedResult leftEnv env U registry target (.ref (.left outerLeft.major))
        leftLocals σ leftAvailable (Profile.singleton (n := n + 1) (.record record))))
    (forwardF : EquationWorldClosureOrder.CallBelow strata.rules.length
      [originalCallWorld leftControls .fundamental (.ref (.left outerLeft.major)) leftCaptured]
      [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] → ∀ {fp},
      RichObs leftEnv env U registry target (.ref (.left outerLeft.major))
        leftLocals σ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available leftAvailable →
      Nonempty (OriginalDirectionalEqualityResult outerLeft.major true env registry target
        leftLocals σ σ leftAvailable (Profile.singleton (n := n + 1) (.record record))))
    (middleR : EquationWorldClosureOrder.CallBelow strata.rules.length
      [originalCallWorld leftControls .expressionReindex (.ref (.right outerLeft.major)) leftCaptured,
        originalCallWorld rightControls .expressionReindex (.ref (.right outerRight.major)) rightCaptured]
      [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] → ∀ {fp},
      RichObs leftEnv env U registry target (.ref (.right outerLeft.major))
        leftLocals σ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target (.ref (.right outerRight.major))
        rightLocals τ rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (backwardF : EquationWorldClosureOrder.CallBelow strata.rules.length
      [originalCallWorld rightControls .fundamental (.ref (.right outerRight.major)) rightCaptured]
      [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] → ∀ {fp},
      RichObs rightEnv env U registry target (.ref (.right outerRight.major))
        rightLocals τ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available rightAvailable →
      Nonempty (OriginalDirectionalEqualityResult outerRight.major false env registry target
        rightLocals τ τ rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (lastR : EquationWorldClosureOrder.CallBelow strata.rules.length
      [originalCallWorld rightControls .expressionReindex (.ref (.left outerRight.major)) rightCaptured,
        originalCallWorld rightControls .expressionReindex (.ref (.right rightInner.major)) rightCaptured]
      [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] → ∀ {fp},
      RichObs rightEnv env U registry target (.ref (.left outerRight.major))
        rightLocals τ (Profile.singleton (n := n + 1) (.record record)) fp → fp.Available rightAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target (.ref (.right rightInner.major))
        rightLocals τ rightAvailable (Profile.singleton (n := n + 1) (.record record)))) :
    ∃ fp, ∃ majorQuery : RichObs rightEnv env U registry target (.ref (.right rightInner.major))
        rightLocals τ (Profile.singleton (n := n + 1) (.record record)) fp,
      ∃ certificate : RichCert rightEnv env U registry target outerRight.field rightLocals τ
          relevant request.input fp,
        fp.Available rightAvailable ∧
        TypeRelated env U registry target (outerLeft.fieldType.subst σ)
          (outerRight.fieldType.subst τ) request.input ∧
        TypeConversion env U target (outerLeft.fieldType.subst σ) (outerRight.fieldType.subst τ) ∧
        ∀ policy, certificate.headDepth policy = majorQuery.headDepth policy := by
  have leftWF : leftLevel.WF U :=
    (leftInner.field.cast leftLiteral rfl).sound.defeq.sort_inv_l leftControls.ordered
  have rightWF : rightLevel.WF U :=
    (rightInner.field.cast rightLiteral rfl).sound.defeq.sort_inv_l rightControls.ordered
  obtain ⟨paidFirst, paidForward, paidMiddle, paidBackward, paidLast⟩ :=
    projectionTemplateBridgeFunding outerLeft outerRight leftDisplay rightDisplay leftInner rightInner
      leftControls rightControls leftCaptured rightCaptured
  obtain ⟨fp, majorQuery, majorResources, projected, raw⟩ :=
    ProjectionHead.recordMajorBridge outerLeft outerRight leftInner rightInner leftMajorEq rightMajorEq displayedEq
      henv hscoped formed nameEq member query resources
      (firstR paidFirst) (forwardF paidForward) (middleR paidMiddle)
      (backwardF paidBackward) (lastR paidLast)
  obtain ⟨answer, footprintEq, depth⟩ := ProjectionHead.sortFieldReply (rightAvailable := rightAvailable) leftInner rightInner leftLiteral rightLiteral
    henv hscoped formed closed leftWF rightWF levels fieldCode fieldResources
  rcases answer with ⟨fieldPath, answer⟩
  rcases answer with ⟨fieldFp, fieldQuery, fieldAvailable, fieldRelated⟩
  dsimp only at footprintEq depth
  subst fieldFp
  let chain : DomainChain env U registry target request.input request.domain (rightInner.fieldType.subst τ) :=
    alignment.trans (.step fieldPath typed fieldCode.formed fieldRelated (.refl _))
  let observation : RichObs rightEnv env U registry target (outerRight.field.cast rightDisplay rfl)
      rightLocals τ request.input fp := by
    simpa only [List.append_nil] using
      RichObs.projection rightInner nameEq member majorQuery fieldQuery typed chain
  let certificate := RichCert.ofCast rightDisplay rfl (.observe observation sorted)
  have related := alignment.related henv typed fieldRelated.left_diagonal projected
  have rawSorted : env.IsDefEq U target ((VExpr.proj name prior leftMajor).subst σ)
      ((VExpr.proj name prior rightMajor).subst τ) (.sort leftLevel) := by
    simpa only [leftLiteral, subst_sort] using alignment.path.cast raw
  refine ⟨fp, majorQuery, certificate, majorResources, ?_, ?_, ?_⟩
  · simpa only [leftDisplay, rightDisplay] using related.code_of_sortable henv hscoped formed sorted
  · simpa only [leftDisplay, rightDisplay] using TypeConversion.single rawSorted
  · intro policy
    rw [ofCast_depth]
    simp only [RichCert.headDepth]
    dsimp only [observation]
    rw [RichObs.headDepth_mp policy rfl rfl rfl (List.append_nil fp)]
    simp only [RichObs.headDepth, depth, Nat.max_zero]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
