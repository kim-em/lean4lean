import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEnrichedFamilyMajorComparison

/-! Consume the actual enriched two-parameter producer in the proper-major C
clause. Only its retained original application prefix is restored. The
resulting right certificate and both parameter admissions come from the same
lower comparison reply, with the original finite P demand still included. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

private theorem restoreCastCode
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned}
    (equal : expression = next)
    (route : PrefixRoute sourceEnv U source next (node.cast equal rfl) last)
    (certificate : RichCert sourceEnv env U registry target last locals σ relevant profile footprint)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ restored : RichCert sourceEnv env U registry target node locals σ relevant profile footprint,
    ∃ output : ControlledStoredQuery controls frontier (.certificate restored),
      output.annotation.worlds = ready.annotation.worlds ∧
      ∀ policy, restored.headDepth policy = certificate.headDepth policy := by
  cases equal
  let restored := RichCert.route route certificate
  refine ⟨restored, ⟨.route route ready.annotation, ?_, ready.sponsored⟩, ?_, ?_⟩
  · intro control active
    simpa only [restored, StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within control active
  · rfl
  · intro policy
    simp only [restored, RichCert.headDepth]

section
variable
  {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftAssigned}
  {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
  (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
  {root : EndpointRef leftEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation leftEnv U rootSource}
  {domain : EndpointRef leftEnv U leftSource E (.sort u)}
  {body : EndpointState leftEnv U (E :: leftSource) F (.sort v)}
  {function : EndpointState leftEnv U leftSource (.app (.const name leftHead.levels) a) (.forallE E F)}
  {argument : EndpointState leftEnv U leftSource p E}
  {result : EndpointState leftEnv U leftSource (F.inst p) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {rightContext : ContextDerivation rightEnv U rightSource}
  (leftGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) leftRaw)
  (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
  (sameExpression : leftValue.subst leftRaw = rightValue.subst rightRaw)
  {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  (leftControls : OriginalWorldControls strata leftEnv)
  (rightControls : OriginalWorldControls strata rightEnv)
  (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
  (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
  (frontier : List (World strata.rules.length))
  (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals commonLeft commonRight leftAvailable)
  (rightFrame : OriginalCaptureRealization rightGraph env registry target rightLocals commonLeft commonRight rightAvailable)
  {substitutions : Ctx.SubstEq env U target (leftRaw.comp commonLeft) (leftRaw.comp commonRight) leftSource}
  {extraQuery : RichGradedResult leftEnv env U registry target argument leftLocals
    (leftRaw.comp commonLeft) leftAvailable (extra : Profile m)}
  {queryLevels : List VLevel} {queryWF : ∀ level ∈ queryLevels, level.WF U}
  (packet : WorldTwoParameterBackward initial domain body function argument result hu hv location
    leftFrame.frame substitutions P leftControls leftWorld frontier (profile : Profile n)
    relevant extraQuery info queryWF)

local notation "leftMajor" => OriginalNestedDisplay.recordBridgeReference leftGraph (EndpointRef.right leftHead.major) rfl
local notation "rightMajor" => OriginalNestedDisplay.recordBridgeReference rightGraph (EndpointRef.right rightHead.major) sameExpression

/-- Actual source descriptor to an independent destination major. The
source prefix is original syntax retained by application exposure. No right
family query, right field answer, or parameter extractor is an input. -/
theorem WorldTwoParameterFamilyResult.compareIndependentMajorWorld
    (signature : ConstantTelescope (info.type.instL queryLevels))
    (enriched : WorldTwoParameterFamilyResult packet signature C D familyRelevant)
    (leftArguments : leftHead.parameters ++ leftHead.indices = [a,p])
    (route : PrefixRoute leftEnv U leftSource (.app (.app (.const name leftHead.levels) a) p)
      ((EndpointState.ref (EndpointRef.right leftHead.major)).typeFormation.node.cast
        (congrArg (mkApps (.const name leftHead.levels)) leftArguments) rfl)
      (.app hu hv (.ref domain) body function argument result))
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (paid : Sponsored frontier [originalCallWorld leftControls .assignedComparison left leftWorld,
      originalCallWorld rightControls .assignedComparison right rightWorld])
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := leftMajor)
      leftControls leftWorld frontier leftFrame)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.recordBridgeReference rightGraph (EndpointRef.right rightHead.major) rfl)
      rightControls rightWorld frontier rightFrame)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld])) :
    ∃ answer : WorldTemplateAssignedReply (P := P) base caps leftMajor rightMajor commonLeft commonRight
        rightControls rightWorld frontier
        (.singleton (n := packet.first.request.rank+1)
          (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared C,packet.secondDeclared D]⟩)),
    ∃ code : TemplateAssignedResult env U registry target (EndpointState.ref (EndpointRef.right leftHead.major))
        (EndpointState.ref (EndpointRef.right rightHead.major))
        answer.reply.reply.answer.reply.locals (leftRaw.comp commonLeft) (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available familyRelevant
        (.singleton (n := packet.first.request.rank+1)
          (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared C,packet.secondDeclared D]⟩)),
    ∃ output : ControlledStoredQuery rightControls frontier (.certificate code.certificate),
      output.annotation.worlds ⊆ answer.data.query.annotation.worlds ∧
      (∀ policy, code.certificate.headDepth policy ≤ answer.reply.reply.answer.reply.query.observation.headDepth policy) ∧
      List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels ∧
      (∃ rightA rightP, rightHead.parameters ++ rightHead.indices = [rightA,rightP] ∧
        RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
          (packet.firstDeclared C) (a.subst (leftRaw.comp commonLeft)) (rightA.subst (rightRaw.comp commonLeft)) ∧
        RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
          (packet.secondDeclared D) (p.subst (leftRaw.comp commonLeft)) (rightP.subst (rightRaw.comp commonLeft))) ∧
      ∃ bound : extraQuery.rank ≤ packet.first.request.rank,
        ∀ atom ∈ (raiseProfile packet.first.request.rank bound extraQuery.raw).atoms,
          atom ∈ (packet.secondDeclared D).input.atoms := by
  obtain ⟨certificate, ready, _, _⟩ := restoreCastCode
    (congrArg (mkApps (.const name leftHead.levels)) leftArguments)
    route enriched.certificate enriched.certificateReady
  obtain ⟨answer, code, output, worlds, depth, levels, rightA, rightP, rightArguments, firstAdmitted, secondAdmitted⟩ :=
    ProjectionHead.compareEnrichedFamilyWorld leftHead rightHead leftGraph rightGraph sameExpression
      leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier paid
      leftFrame leftData rightFrame rightData henv hscoped formed leftArguments
      certificate enriched.resources ready bank
  exact ⟨answer, code, output, worlds, depth, levels,
    ⟨rightA, rightP, rightArguments, firstAdmitted, secondAdmitted⟩, packet.extraInSecond D⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
