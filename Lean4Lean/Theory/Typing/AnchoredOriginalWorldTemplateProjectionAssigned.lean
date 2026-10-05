import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateAssigned
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionFieldTemplate
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
import Lean4Lean.Theory.Typing.AnchoredFamilyLiteralArguments
import Lean4Lean.Theory.Typing.AnchoredDataAnchors

/-! Proper-major assigned mode of the binary projection-template clause.
The original displayed majors may differ syntactically. A local template
comparison must produce the actual child reply; this module preserves its
selected world evidence and extracts only its genuinely frozen requests.
No ordinary same-expression C call is used for the heterogeneous pair. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private major_below from_both from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Select the actual displayed major from this original projection's
retained exposure/conversion path, keeping its source graph unchanged. -/
noncomputable def ProjectionHead.templateMajorDisplay
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node)
    (context : ContextDerivation sourceEnv U source)
    (provenance : EndpointProvenance context node)
    (graph : OriginalCaptureMap (common := common) context raw) :
    OriginalNestedDisplay U common (value.subst raw)
      ((mkApps (.const name head.levels) (head.parameters ++ head.indices)).subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := value
  sourceType := mkApps (.const name head.levels) (head.parameters ++ head.indices)
  context := context
  node := .ref (.right head.major)
  provenance := {
    rootSource := provenance.rootSource
    rootExpression := provenance.rootExpression
    rootType := provenance.rootType
    root := provenance.root
    initial := provenance.initial
    location := .projMajor (head.route.locate provenance.location)
    context_eq := by
      change context = (head.route.locate provenance.location).contextDerivation provenance.initial
      rw [PrefixRoute.locate_contextDerivation]
      exact provenance.context_eq }
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl

/-- The finite local clause may use the fixed outer original bank. Each
actual major is strictly below its own projection, including when the two
original source worlds and major expressions differ. -/
theorem projectionTemplateMajorFunding
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftAssigned}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [originalCallWorld leftControls .assignedComparison left leftWorld,
      originalCallWorld rightControls .assignedComparison right rightWorld]) :
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .assignedComparison (.ref (.right leftHead.major)) leftWorld,
        originalCallWorld rightControls .assignedComparison (.ref (.right rightHead.major)) rightWorld])
      (frontier ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
        originalCallWorld rightControls .assignedComparison right rightWorld]) ∧
    Sponsored frontier
      [originalCallWorld leftControls .assignedComparison (.ref (.right leftHead.major)) leftWorld,
        originalCallWorld rightControls .assignedComparison (.ref (.right rightHead.major)) rightWorld] := by
  have leftLower := major_below leftHead leftControls leftWorld .assignedComparison .assignedComparison
  have rightLower := major_below rightHead rightControls rightWorld .assignedComparison .assignedComparison
  constructor
  · have smaller := from_both leftLower rightLower
    have appendSmaller : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length
          (inherited ++ [originalCallWorld leftControls .assignedComparison (.ref (.right leftHead.major)) leftWorld,
            originalCallWorld rightControls .assignedComparison (.ref (.right rightHead.major)) rightWorld])
          (inherited ++ [originalCallWorld leftControls .assignedComparison left leftWorld,
            originalCallWorld rightControls .assignedComparison right rightWorld]) := by
      intro inherited
      induction inherited with
      | nil => exact smaller
      | cons world tail ih => exact ih.cons world
    exact appendSmaller frontier
  · intro world member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨sponsor, present, lower⟩ := paid _ List.mem_cons_self
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans leftLower lower⟩
    · cases List.mem_singleton.mp member
      obtain ⟨sponsor, present, lower⟩ := paid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans rightLower lower⟩

section Family
variable
  {common : List VExpr}
  {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftAssigned}
  {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
  (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
  (leftContext : ContextDerivation leftEnv U leftSource)
  (rightContext : ContextDerivation rightEnv U rightSource)
  (leftProvenance : EndpointProvenance leftContext left)
  (rightProvenance : EndpointProvenance rightContext right)
  (leftGraph : OriginalCaptureMap (common := common) leftContext leftRaw)
  (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)

local notation "leftMajor" => ProjectionHead.templateMajorDisplay leftHead leftContext leftProvenance leftGraph
local notation "rightMajor" => ProjectionHead.templateMajorDisplay rightHead rightContext rightProvenance rightGraph

/-- Consume the actual local child C reply, retaining its selected frame.
The extracted paired requests are exactly the descriptor in that reply;
this does not enlarge their inputs or infer arbitrary-demand availability. -/
theorem WorldTemplateAssignedReply.projectionFamily
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {controls : OriginalWorldControls strata rightEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {family : FamilyData (Profile n)}
    (answer : WorldTemplateAssignedReply (P := P) base caps leftMajor rightMajor commonLeft commonRight
      controls baseline frontier (.singleton (n := n+1) (.family family)))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftSubstitutions : Ctx.SubstEq env U target (leftRaw.comp commonLeft) (leftRaw.comp commonLeft) leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) rightSource)
    (majorAnswer : TemplateComparisonResult env U registry target
      (.ref (.right leftHead.major)) (.ref (.right rightHead.major)) leftLocals rightLocals
      (leftRaw.comp commonLeft) (rightRaw.comp commonLeft) leftAvailable rightAvailable valueProfile)
    (nameEq : family.name = name)
    (sorted : (Profile.singleton (n := n+1) (.family family)).HasType (.sort family.relevant)) :
    ∃ code : TemplateAssignedResult env U registry target (.ref (.right leftHead.major)) (.ref (.right rightHead.major))
        answer.reply.reply.answer.reply.locals (leftRaw.comp commonLeft) (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available family.relevant (.singleton (n := n+1) (.family family)),
      ∃ ready : ControlledStoredQuery controls frontier (.certificate code.certificate),
        ready.annotation.worlds ⊆ answer.data.query.annotation.worlds ∧
        (∀ policy, code.certificate.headDepth policy ≤ answer.reply.reply.answer.reply.query.observation.headDepth policy) ∧
        List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels ∧
        RankedData.Arguments env U (relations env U registry n) target family.arguments
          ((leftHead.parameters ++ leftHead.indices).map (VExpr.subst · (leftRaw.comp commonLeft)))
          ((rightHead.parameters ++ rightHead.indices).map (VExpr.subst · (rightRaw.comp commonLeft))) ∧
        env.IsDefEq U target (leftHead.sourceMajor.subst (leftRaw.comp commonLeft))
          (rightHead.sourceMajor.subst (rightRaw.comp commonLeft))
          ((mkApps (.const name leftHead.levels) (leftHead.parameters ++ leftHead.indices)).subst
            (leftRaw.comp commonLeft)) := by
  obtain ⟨code, ready, worlds, depth⟩ := answer.code henv sorted
  have related : TypeRelated env U registry target
      (mkApps (.const family.name leftHead.levels)
        ((leftHead.parameters ++ leftHead.indices).map (VExpr.subst · (leftRaw.comp commonLeft))))
      (mkApps (.const family.name rightHead.levels)
        ((rightHead.parameters ++ rightHead.indices).map (VExpr.subst · (rightRaw.comp commonLeft))))
      (Profile.singleton (n := n+1) (.family family)) := by
    simpa only [ProjectionHead.templateMajorDisplay, nameEq, subst_mkApps, subst_const] using code.related
  have leftRelation := related.familyRelation (List.mem_singleton_self _)
  have rightRelation := (related.symm henv sorted.wf_value).familyRelation (List.mem_singleton_self _)
  obtain ⟨_, _, _, leftLevels⟩ := leftRelation.literalFormation henv hscoped formed
  obtain ⟨_, _, _, rightLevels⟩ := rightRelation.literalFormation henv hscoped formed
  have universes : List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      (Lean4Lean.List.Forall₂.imp (fun _ _ equal => equal.symm) (Lean4Lean.List.Forall₂.flip leftLevels)) rightLevels
  have arguments := (leftRelation.literalArguments henv hscoped formed).joinAnchors
    ((rankLaws henv n).lowerEquality henv) hscoped
    (rightRelation.literalArguments henv hscoped formed)
  have leftRaw := (leftHead.major.forget.defeq.mono leftBelow).substDF henv
    leftSubstitutions.wf formed leftSubstitutions
  have rightRaw := (rightHead.major.forget.defeq.mono rightBelow).substDF henv
    rightSubstitutions.wf formed rightSubstitutions
  have hiddenMajors := (leftRaw.trans majorAnswer.raw).trans (code.path.symm.cast rightRaw.symm)
  exact ⟨code, ready, worlds, depth, universes, arguments, hiddenMajors⟩

end Family
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
