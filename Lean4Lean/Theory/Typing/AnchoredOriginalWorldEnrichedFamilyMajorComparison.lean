import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterFamily
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateProjectionAssigned
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-! Attach an enriched two-parameter descriptor to an independent original
major by the actual proper-major assigned comparison. The right certificate,
its selected frame, and its paired requests all come from that SAME reply.
No destination field query or parameter-query extractor is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private relabel from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

/-- The actual last application prefix of a two-argument assigned family. -/
noncomputable def twoParameterFormationRoute
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) [a,p])) :
    let application := assignedFamilyApplication major 1 rfl
    PrefixRoute sourceEnv U source (.app (.app (.const name levels) a) p)
      major.typeFormation.node
      (.app application.view.domainWF application.view.bodyWF application.view.domain
        application.view.codomain application.view.function application.view.argument application.view.result) :=
  (assignedFamilyApplication major 1 rfl).selected.route

/-- Restore the actual prefix without changing the chosen certificate,
resource footprint, controls, or query-owned history. -/
theorem twoParameterFamilyAssignedCode
    {strata : EquationStratification env}
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) [a,p]))
    (domain : EndpointRef sourceEnv U source
      (assignedFamilyApplication major 1 rfl).view.domainExpression
      (.sort (assignedFamilyApplication major 1 rfl).view.domainLevel))
    (domainEq : (assignedFamilyApplication major 1 rfl).view.domain = .ref domain)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {certificate : RichCert sourceEnv env U registry target
      (.app (assignedFamilyApplication major 1 rfl).view.domainWF
        (assignedFamilyApplication major 1 rfl).view.bodyWF (.ref domain)
        (assignedFamilyApplication major 1 rfl).view.codomain
        (assignedFamilyApplication major 1 rfl).view.function
        (assignedFamilyApplication major 1 rfl).view.argument
        (assignedFamilyApplication major 1 rfl).view.result)
      locals σ relevant (profile : Profile n) footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ restored : RichCert sourceEnv env U registry target major.typeFormation.node locals σ relevant profile footprint,
    ∃ output : ControlledStoredQuery controls frontier (.certificate restored),
      output.annotation.worlds = ready.annotation.worlds ∧
      ∀ policy, restored.headDepth policy = certificate.headDepth policy := by
  have route := twoParameterFormationRoute major
  dsimp only at route
  rw [domainEq] at route
  let restored := RichCert.route route certificate
  refine ⟨restored, ⟨.route route ready.annotation, ?_, ready.sponsored⟩, ?_, ?_⟩
  · intro control active
    simpa only [restored, StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within control active
  · rfl
  · intro policy
    simp only [restored, RichCert.headDepth]

private theorem pairedTwoArguments
    (arguments : RankedData.Arguments env U (relations env U registry n) target
      [first,second] [leftA,leftP] (values.map (VExpr.subst · σ))) :
    ∃ rightA rightP, values = [rightA,rightP] ∧
      RankedData.RequestAdmission env U (relations env U registry n) target first leftA (rightA.subst σ) ∧
      RankedData.RequestAdmission env U (relations env U registry n) target second leftP (rightP.subst σ) := by
  cases values with
  | nil => cases arguments
  | cons rightA values =>
    cases values with
    | nil => cases arguments with | cons first rest => cases rest
    | cons rightP rest =>
      cases arguments with
      | cons first remaining =>
        cases remaining with
        | cons second empty =>
          have restEmpty : rest = [] := by
            have nil_right {rights : List VExpr}
                (proof : RankedData.Arguments env U (relations env U registry n) target [] [] rights) : rights = [] := by
              cases proof
              rfl
            have mapped : rest.map (VExpr.subst · σ) = [] := nil_right empty
            exact List.map_eq_nil_iff.mp mapped
          subst rest
          exact ⟨rightA,rightP,rfl,first,second⟩

section
variable
  {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftAssigned}
  {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
  (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
  {leftContext : ContextDerivation leftEnv U leftSource}
  {rightContext : ContextDerivation rightEnv U rightSource}
  (leftGraph : OriginalCaptureMap (common := common) leftContext leftRaw)
  (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
  (sameExpression : leftValue.subst leftRaw = rightValue.subst rightRaw)

local notation "leftMajor" => OriginalNestedDisplay.recordBridgeReference leftGraph (EndpointRef.right leftHead.major) rfl
local notation "rightMajor" => OriginalNestedDisplay.recordBridgeReference rightGraph (EndpointRef.right rightHead.major) sameExpression

/-- The source is the real enriched formation certificate. This executes C
at the two proper major originals, then reads the two declared admissions
from its exact family relation. The destination selected frame is preserved. -/
theorem ProjectionHead.compareEnrichedFamilyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [originalCallWorld leftControls .assignedComparison left leftWorld,
      originalCallWorld rightControls .assignedComparison right rightWorld])
    (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := leftMajor)
      leftControls leftWorld frontier leftFrame)
    (rightFrame : OriginalCaptureRealization rightGraph env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) rfl)
      rightControls rightWorld frontier rightFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {first second : DataRequest (Profile n)}
    (leftArguments : leftHead.parameters ++ leftHead.indices = [leftA,leftP])
    (certificate : RichCert leftEnv env U registry target (EndpointState.ref (EndpointRef.right leftHead.major)).typeFormation.node
      leftLocals (leftRaw.comp commonLeft) familyRelevant
      (.singleton (n := n+1) (.family ⟨name,seed,familyRelevant,[first,second]⟩)) footprint)
    (resources : footprint.Available leftAvailable)
    (ready : ControlledStoredQuery leftControls frontier (.certificate certificate))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    ∃ answer : WorldTemplateAssignedReply (P := P) base caps leftMajor rightMajor commonLeft commonRight
        rightControls rightWorld frontier
        (.singleton (n := n+1) (.family ⟨name,seed,familyRelevant,[first,second]⟩)),
    ∃ code : TemplateAssignedResult env U registry target (.ref (.right leftHead.major)) (.ref (.right rightHead.major))
        answer.reply.reply.answer.reply.locals (leftRaw.comp commonLeft) (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available familyRelevant
        (.singleton (n := n+1) (.family ⟨name,seed,familyRelevant,[first,second]⟩)),
    ∃ output : ControlledStoredQuery rightControls frontier (.certificate code.certificate),
      output.annotation.worlds ⊆ answer.data.query.annotation.worlds ∧
      (∀ policy, code.certificate.headDepth policy ≤ answer.reply.reply.answer.reply.query.observation.headDepth policy) ∧
      List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels ∧
      ∃ rightA rightP, rightHead.parameters ++ rightHead.indices = [rightA,rightP] ∧
        RankedData.RequestAdmission env U (relations env U registry n) target first
          (leftA.subst (leftRaw.comp commonLeft)) (rightA.subst (rightRaw.comp commonLeft)) ∧
        RankedData.RequestAdmission env U (relations env U registry n) target second
          (leftP.subst (leftRaw.comp commonLeft)) (rightP.subst (rightRaw.comp commonLeft)) := by
  obtain ⟨smaller, sponsored⟩ := projectionTemplateMajorFunding leftHead rightHead
    leftControls rightControls leftWorld rightWorld frontier paid
  obtain ⟨reply, ⟨data⟩⟩ := bank.assigned _ smaller base caps leftMajor rightMajor commonLeft commonRight
    leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier rfl sponsored
    leftFrame leftData rightFrame (relabel rightData) certificate resources ready
  let answer : WorldTemplateAssignedReply (P := P) base caps leftMajor rightMajor commonLeft commonRight
      rightControls rightWorld frontier
      (.singleton (n := n+1) (.family ⟨name,seed,familyRelevant,[first,second]⟩)) := ⟨reply,data⟩
  obtain ⟨code, output, worlds, depth⟩ := answer.code henv certificate.formed
  have related : TypeRelated env U registry target
      (mkApps (.const name leftHead.levels)
        ((leftHead.parameters ++ leftHead.indices).map (VExpr.subst · (leftRaw.comp commonLeft))))
      (mkApps (.const name rightHead.levels)
        ((rightHead.parameters ++ rightHead.indices).map (VExpr.subst · (rightRaw.comp commonLeft))))
      (.singleton (n := n+1) (.family ⟨name,seed,familyRelevant,[first,second]⟩)) := by
    simpa only [OriginalNestedDisplay.recordBridgeReference, subst_mkApps, subst_const] using code.related
  have firstRelation := related.familyRelation (List.mem_singleton_self _)
  have secondRelation := (related.symm henv certificate.formed.wf_value).familyRelation (List.mem_singleton_self _)
  obtain ⟨_, _, _, firstLevels⟩ := firstRelation.literalFormation (family := ⟨name,seed,familyRelevant,[first,second]⟩) henv hscoped formed
  obtain ⟨_, _, _, secondLevels⟩ := secondRelation.literalFormation (family := ⟨name,seed,familyRelevant,[first,second]⟩) henv hscoped formed
  have levels : List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      (Lean4Lean.List.Forall₂.imp (fun _ _ equal => equal.symm) (Lean4Lean.List.Forall₂.flip firstLevels)) secondLevels
  have arguments := (firstRelation.literalArguments (family := ⟨name,seed,familyRelevant,[first,second]⟩) henv hscoped formed).joinAnchors
    ((rankLaws henv n).lowerEquality henv) hscoped (secondRelation.literalArguments (family := ⟨name,seed,familyRelevant,[first,second]⟩) henv hscoped formed)
  rw [leftArguments] at arguments
  change RankedData.Arguments env U (relations env U registry n) target [first,second]
    [leftA.subst (leftRaw.comp commonLeft),leftP.subst (leftRaw.comp commonLeft)]
    ((rightHead.parameters ++ rightHead.indices).map (VExpr.subst · (rightRaw.comp commonLeft))) at arguments
  obtain ⟨rightA,rightP,rightArguments,firstAdmitted,secondAdmitted⟩ := pairedTwoArguments arguments
  exact ⟨answer,code,output,worlds,depth,levels,rightA,rightP,rightArguments,firstAdmitted,secondAdmitted⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
