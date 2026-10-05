import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterMajorAttachment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySourceRequests
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyRequestReplay

/-! Recover the original finite P demand from the actual destination
family requests. Packing covers the source observer's raw profile; both its
grade bound and general adapter are therefore retained in this extraction.
No restriction to sortable or singleton profiles is made. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private sourceProvenance from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyRequestReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The original major location constructs the exact selected node's
provenance in its caller context; no independently supplied occurrence is
needed when this demanded observer is used by the next lower call. -/
noncomputable def RichFamilyArgumentQuery.provenanceAt
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (answer : RichFamilyArgumentQuery root env registry target source locals σ available expression profile)
    (context : ContextDerivation sourceEnv U source) : EndpointProvenance context answer.node :=
  sourceProvenance answer.location context

/-- The selected request and the demanded observer share exactly the same
original node and stored query. Only the finite requested-profile adapter
changes; controls and captured query worlds are not reselected. -/
theorem WorldFamilyRequestProperty.secondExtraQueryWorld
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata rightEnv}
    {frontier : List (World strata.rules.length)}
    {root : EndpointRef rightEnv U rightSource rootExpression rootType}
    {N : Nat} {firstRequest secondRequest : DataRequest (Profile N)}
    (property : WorldFamilyRequestProperty controls frontier root registry target rightLocals rightSubst
      rightAvailable name levels [rightA,rightP]
      ⟨familyName,familyLevels,familyRelevant,[firstRequest,secondRequest]⟩)
    (extraQuery : RichGradedResult leftEnv env U registry target leftNode leftLocals leftSubst
      leftAvailable (extra : Profile m))
    (bound : extraQuery.rank ≤ N)
    (included : ∀ atom ∈ (raiseProfile N bound extraQuery.raw).atoms,
      atom ∈ (secondRequest : DataRequest (Profile N)).input.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ nominal : WorldRichFamilySourceRequest controls frontier root registry target rightLocals rightSubst
        rightAvailable rightP secondRequest,
    ∃ answer : RichFamilyArgumentQuery root env registry target rightSource rightLocals rightSubst
        rightAvailable rightP extra,
    ∃ ready : ControlledStoredQuery controls frontier (.observation answer.query.observation),
      answer.assigned = nominal.argument.assigned ∧
      HEq answer.node nominal.argument.node ∧ HEq answer.location nominal.argument.location ∧
      answer.query.rank = nominal.argument.query.rank ∧
      answer.query.footprint = nominal.argument.query.footprint ∧
      ready.annotation.worlds = nominal.controlled.annotation.worlds ∧
      (∀ policy, answer.query.observation.headDepth policy = nominal.argument.query.observation.headDepth policy) := by
  obtain ⟨_, _, requests⟩ := property
  cases requests with
  | cons first rest =>
    cases rest with
    | cons second rest =>
      obtain ⟨nominal⟩ := second
      let selected := nominal.argument.query.localDemand ⟨extraQuery.rank, extraQuery.raw⟩ bound (by
        simpa only [Need.atGrade, dif_pos bound] using included)
      let query := selected.adaptRequest henv hscoped formed extraQuery.bound extraQuery.adapter
      let answer : RichFamilyArgumentQuery root env registry target rightSource rightLocals rightSubst
          rightAvailable rightP extra := { nominal.argument with query := query }
      let ready : ControlledStoredQuery controls frontier (.observation answer.query.observation) := nominal.controlled
      exact ⟨nominal, answer, ready, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, fun _ => rfl⟩

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source E (.sort u)}
  {body : EndpointState sourceEnv U (E :: source) F (.sort v)}
  {function : EndpointState sourceEnv U source (.app (.const name leftLevels) a) (.forallE E F)}
  {argument : EndpointState sourceEnv U source p E}
  {result : EndpointState sourceEnv U source (F.inst p) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {strata : EquationStratification env} {P : VEnv → Prop}
  {leftControls : OriginalWorldControls strata sourceEnv}
  {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
  {leftFrontier : List (World strata.rules.length)}
  {extraQuery : RichGradedResult sourceEnv env U registry target argument locals σ available (extra : Profile m)}
  {queryLevels : List VLevel}
  {queryWF : ∀ level ∈ queryLevels, level.WF U}
  (packet : WorldTwoParameterBackward initial domain body function argument result hu hv location frame substitutions
    P leftControls baseline leftFrontier (profile : Profile n) relevant extraQuery info queryWF)

/-- The bound and raw inclusion are computed from the SAME backward packet
used by `compareIndependentMajorWorld`. The second observer is selected
internally from the caller requests reconstructed for that returned family. -/
theorem WorldTwoParameterBackward.rightExtraQueryWorld
    (C D : VExpr)
    {rightRoot : EndpointRef rightEnv U rightSource rightExpression rightType}
    (rightControls : OriginalWorldControls strata rightEnv)
    (frontier : List (World strata.rules.length))
    (property : WorldFamilyRequestProperty rightControls frontier rightRoot registry target
      rightLocals rightSubst rightAvailable name rightLevels [rightA,rightP]
      ⟨name,queryLevels,familyRelevant,[packet.firstDeclared C,packet.secondDeclared D]⟩)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ nominal : WorldRichFamilySourceRequest rightControls frontier rightRoot registry target
        rightLocals rightSubst rightAvailable rightP (packet.secondDeclared D),
    ∃ answer : RichFamilyArgumentQuery rightRoot env registry target rightSource rightLocals rightSubst
        rightAvailable rightP extra,
    ∃ ready : ControlledStoredQuery rightControls frontier (.observation answer.query.observation),
      answer.assigned = nominal.argument.assigned ∧
      HEq answer.node nominal.argument.node ∧ HEq answer.location nominal.argument.location ∧
      answer.query.rank = nominal.argument.query.rank ∧
      answer.query.footprint = nominal.argument.query.footprint ∧
      ready.annotation.worlds = nominal.controlled.annotation.worlds ∧
      (∀ policy, answer.query.observation.headDepth policy = nominal.argument.query.observation.headDepth policy) := by
  obtain ⟨bound, included⟩ := packet.extraInSecond D
  exact WorldFamilyRequestProperty.secondExtraQueryWorld property extraQuery bound included henv hscoped formed

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
