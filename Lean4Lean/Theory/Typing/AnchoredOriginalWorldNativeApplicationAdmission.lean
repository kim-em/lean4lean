import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure

/-! Reanchor a retained native application by interpreting its two actual
original children. The outer row's guard constructs the paired binder frame;
no whole-body answer or inner admission is supplied by the caller. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private piRowWorldChildren from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- These are the exact answers at the retained variable and function
children, in the same newly realized binder table. -/
structure NativeApplicationAdmissionResult
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    {function : EndpointState sourceEnv U (D :: source) f (.forallE A B)}
    {argument : EndpointState sourceEnv U (D :: source) (.bvar 0) A}
    (locals : List Nat) (σ : Subst) (oldAnchor newAnchor : VExpr)
    (available : Valuation) (needs : List Need)
    (key : Key n) (output : Atom n) (rawInput : Profile n) where
  functionValue : RichComputationalValue sourceEnv env U registry target function (Locals.push locals)
    (σ.cons oldAnchor) (σ.cons newAnchor) (Valuation.push needs available) (Profile.fn key output)
  argumentValue : RichComputationalValue sourceEnv env U registry target argument (Locals.push locals)
    (σ.cons oldAnchor) (σ.cons newAnchor) (Valuation.push needs available) rawInput
  functionCertificate : ControlledStoredQuery controls frontier (.certificate functionValue.certificate)
  functionQuery : ControlledStoredQuery controls frontier (.observation functionValue.rightQuery.observation)
  argumentCertificate : ControlledStoredQuery controls frontier (.certificate argumentValue.certificate)
  argumentQuery : ControlledStoredQuery controls frontier (.observation argumentValue.rightQuery.observation)
  paired : Admitted env U registry target key oldAnchor newAnchor
  admitted : Admitted env U registry target key newAnchor newAnchor

/-- The application code relation follows from the same two answers and
computed paired admission, without a whole application F call. -/
theorem NativeApplicationAdmissionResult.applicationCode
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {function : EndpointState sourceEnv U (D :: source) f (.forallE A B)}
    {argument : EndpointState sourceEnv U (D :: source) (.bvar 0) A}
    (answer : NativeApplicationAdmissionResult (registry := registry) (target := target)
      (function := function) (argument := argument) controls frontier locals σ oldAnchor newAnchor
      available needs key output rawInput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    TypeRelated env U registry target ((.app f (.bvar 0) : VExpr).subst (σ.cons oldAnchor))
      ((.app f (.bvar 0) : VExpr).subst (σ.cons newAnchor)) (.singleton output) := by
  have functionValue : Related env U registry target (f.subst (σ.cons oldAnchor))
      (f.subst (σ.cons newAnchor)) (.forallE (A.subst (σ.cons oldAnchor))
        (B.subst (σ.cons oldAnchor).lift)) (Profile.fn key output) answer.functionValue.support := by
    simpa only [subst] using answer.functionValue.related
  simpa only [subst, Subst.cons] using
    Related.applicationCode henv hscoped formed sorted functionValue answer.paired

/-- The two F calls are computed strict children of the actual Pi containing
this application row. In particular the variable child's independently
assigned type is aligned using the function answer, not inferred from the
outer raw equality or from the finite demand adapter. -/
theorem nativeApplicationAdmissionWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source D (.sort outerLevel))
    (domainLocation : Located root (.ref domain))
    {appDomain : EndpointState sourceEnv U (D :: source) A (.sort u)}
    {appBody : EndpointState sourceEnv U (A :: D :: source) B (.sort v)}
    {function : EndpointState sourceEnv U (D :: source) f (.forallE A B)}
    {argument : EndpointState sourceEnv U (D :: source) (.bvar 0) A}
    {result : EndpointState sourceEnv U (D :: source) (B.inst (.bvar 0)) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (bodyLocation : Located root (.app hu hv appDomain appBody function argument result))
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (outerWF : outerLevel.WF U)
    (frame : OriginalRichFrame sourceEnv env U registry target (domainLocation.contextDerivation initial)
      locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true (support : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ D (outerKey : Key n) support)
    (fn : RichObs sourceEnv env U registry target function (Locals.push locals)
      (σ.cons outerKey.anchor) (Profile.fn (key : Key n) output) fnFootprint)
    (arg : RichObs sourceEnv env U registry target argument (Locals.push locals)
      (σ.cons outerKey.anchor) (rawInput : Profile n) argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (oldAdmission : Admitted env U registry target key outerKey.anchor outerKey.anchor)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (coverage : packed.atoms ⊆ outerKey.input.atoms)
    (resources : outside.Available available)
    (domainReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (fnReady : ControlledStoredQuery controls frontier (.observation fn))
    (argReady : ControlledStoredQuery controls frontier (.observation arg))
    (outerAdmission : Admitted env U registry target outerKey anchor anchor)
    (piBody : EndpointState sourceEnv U (D :: source) (.app f (.bvar 0)) (.sort resultLevel))
    (bodyRoute : PrefixRoute sourceEnv U (D :: source) (.app f (.bvar 0)) piBody
      (.app hu hv appDomain appBody function argument result))
    (resultWF : resultLevel.WF U)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured]))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured]) :
    Nonempty (NativeApplicationAdmissionResult (registry := registry) (target := target) (function := function) (argument := argument)
      controls frontier locals σ outerKey.anchor anchor available
      ((fnFootprint ++ argFootprint).localNeeds ++ (fnFootprint ++ argFootprint).localNeeds.flatMap Need.singletons)
      key output rawInput) := by
  have declared := outerAdmission.rekey henv guard.path guard.inputTyped guard.formed guard.domains
  obtain ⟨raw, _, _, _, _, _, pairedArgument, _⟩ := declared
  have arguments := Related.retag henv guard.inputTyped
    (guard.domains.symm henv guard.inputTyped.wf_type).left_diagonal pairedArgument
  let needs := (fnFootprint ++ argFootprint).localNeeds ++
    (fnFootprint ++ argFootprint).localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need member => (pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ outerKey.input.atoms :=
    fun need member atom present => coverage ((pack.atomized_localNeeds need member).2 atom present)
  let bodyFrame := (OriginalRichFrame.bind frame domain certificate domainResources
    guard.inputTyped arguments needs bounded covered).reserve
      [.close (domain.dependencyOrigin controls.ordered) (frame.dependencyEnvironment controls.ordered)]
  let bodyCaptured : WorldEnvironmentProvenance strata U (bodyFrame.dependencyEnvironment controls.ordered) :=
    reservedBindWorldEnvironment controls domain captured captured
  obtain ⟨bodyData⟩ := data.bind substitutions domain certificate domainResources guard.inputTyped
    arguments needs bounded covered domainReady (atomizedNeeds_closed _)
  have paired : Ctx.SubstEq env U target (σ.cons outerKey.anchor) (σ.cons anchor) (D :: source) :=
    .cons substitutions (domain.sound.defeq.mono below) raw
  have supplied := pack.available_atomized_localNeeds resources
  have children := piRowWorldChildren controls domain piBody outerWF resultWF captured
  have bodyBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.app hu hv appDomain appBody function argument result) bodyCaptured)
      (originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured) := by
    have routeBound := bodyRoute.dependency_cost_le controls.ordered
      (bodyFrame.dependencyEnvironment controls.ordered)
    rcases Nat.eq_or_lt_of_le routeBound with sameCost | smaller
    · have same : originalCallWorld controls .fundamental
          (.app hu hv appDomain appBody function argument result) bodyCaptured =
          originalCallWorld controls .fundamental piBody bodyCaptured := by
        unfold originalCallWorld
        rw [sameCost]
      rw [same]
      exact children.2
    · exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans
        (original_child (richSchedule_strict smaller _ _) _ _ _ _ bodyCaptured.worlds) children.2
  have enlarged := application_cost_le_captured (appDomain.dependencyOrigin controls.ordered)
    (appBody.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered)
    (bodyFrame.dependencyEnvironment controls.ordered)
  have lower {expression assigned} (node : EndpointState sourceEnv U (D :: source) expression assigned)
      (member : node.dependencyOrigin controls.ordered ∈
        [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
         result.dependencyOrigin controls.ordered]) :
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental node bodyCaptured)
        (originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured) := by
    have cost := Nat.lt_of_lt_of_le (binder_other_cost (domain := appDomain.dependencyOrigin controls.ordered)
      (bodies := [appBody.dependencyOrigin controls.ordered]) member
      (bodyFrame.dependencyEnvironment controls.ordered)) enlarged
    exact EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans (original_child (richSchedule_strict cost _ _) _ _ _ _ _) bodyBelow
  have fnBelow := lower function (by simp)
  have argBelow := lower argument (by simp)
  have fund {child : World strata.rules.length}
      (smaller : WorldBelow strata.rules.length child
        (originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured)) :
      CallBelow strata.rules.length (frontier ++ [child])
        (frontier ++ [originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured]) := by
    have first := split_call (calls := [child]) (fun value member => by
      cases List.mem_singleton.mp member
      exact smaller)
    have appendFirst : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length (inherited ++ [child])
          (inherited ++ [originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured]) := by
      intro inherited
      induction inherited with
      | nil => exact first
      | cons value tail ih => exact ih.cons value
    exact appendFirst frontier
  have fnProvenance : EndpointProvenance (.cons (domainLocation.contextDerivation initial) domain) function :=
    bodyContext ▸ EndpointProvenance.ofLocation (.appFunction bodyLocation) initial
  have argProvenance : EndpointProvenance (.cons (domainLocation.contextDerivation initial) domain) argument :=
    bodyContext ▸ EndpointProvenance.ofLocation (.appArgument bodyLocation) initial
  obtain ⟨fnAnswer, ⟨fnCodeReady⟩, ⟨fnQueryReady⟩⟩ :=
    (bank _ (fund fnBelow)).computational function fnProvenance controls bodyFrame bodyCaptured bodyCaptured
      frontier (Nat.le_refl _) (Covered.refl _) rfl (singletonSponsoredBelow sponsored fnBelow)
      bodyData (Valuation.push_atomized_closed closed _) formed paired fn
      (fun index need member => supplied index need (List.mem_append_left _ member)) fnReady
  obtain ⟨argAnswer, ⟨argCodeReady⟩, ⟨argQueryReady⟩⟩ :=
    (bank _ (fund argBelow)).computational argument argProvenance controls bodyFrame bodyCaptured bodyCaptured
      frontier (Nat.le_refl _) (Covered.refl _) rfl (singletonSponsoredBelow sponsored argBelow)
      bodyData (Valuation.push_atomized_closed closed _) formed paired arg
      (fun index need member => supplied index need (List.mem_append_right _ member)) argReady
  have functionValue : Related env U registry target (f.subst (σ.cons outerKey.anchor))
      (f.subst (σ.cons anchor)) (.forallE (A.subst (σ.cons outerKey.anchor))
        (B.subst (σ.cons outerKey.anchor).lift)) (Profile.fn key output) fnAnswer.support := by
    simpa only [subst] using fnAnswer.related
  obtain ⟨innerSupport, inputTyped, supportFormed, path, bridge⟩ :=
    functionValue.fn_domain_alignment henv hscoped formed
  have sourceCode := (bridge.symm henv inputTyped.wf_type).left_diagonal
  have keyCode := bridge.left_diagonal
  have adapted := adapter.termMap henv hscoped formed inputTyped sourceCode argAnswer.related
  have converted := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  have pairedRaw := path.symm.cast
    ((argument.sound.defeq.mono below).substDF henv paired.wf formed paired)
  obtain ⟨anchorRaw, _, _, _, _, _, oldRelated, _⟩ := oldAdmission
  have oldRelated' := Related.retag henv inputTyped keyCode oldRelated
  have pairAdmission : Admitted env U registry target key outerKey.anchor anchor :=
    ⟨anchorRaw, pairedRaw, innerSupport, inputTyped, supportFormed, keyCode, oldRelated', converted⟩
  have newRelated := Related.trans henv hscoped oldRelated' converted
  have admission : Admitted env U registry target key anchor anchor :=
    ⟨anchorRaw.trans pairedRaw, pairedRaw.hasType.2, innerSupport, inputTyped, supportFormed,
      keyCode, newRelated, (newRelated.symm henv).left_diagonal⟩
  exact ⟨⟨fnAnswer, argAnswer, fnCodeReady, fnQueryReady, argCodeReady, argQueryReady, pairAdmission, admission⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
