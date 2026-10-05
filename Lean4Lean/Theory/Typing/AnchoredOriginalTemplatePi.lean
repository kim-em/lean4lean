import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiRows
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterEquality
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPi
import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaCoherence

/-! Native dependent Pi comparison over independently instantiated templates.
The fresh body comparison supplies an unconditional raw path; finite row
comparisons retain capped right frames, so their heads cannot acquire demands
outside their actual frozen keys. -/
namespace Lean4Lean.VEnv
open VExpr AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Congruence follows the explicit finite domain path, retaining every edge's
own universe. No Pi injectivity or universe uniqueness is used. -/
theorem TypeConversion.forallDomainPath
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (domains : TypeConversion env U target A C)
    (bodyTyped : env.IsType U (A :: target) B) :
    TypeConversion env U target (.forallE A B) (.forallE C B) := by
  induction domains with
  | refl => exact .refl
  | tail previous edge ih =>
    obtain ⟨level, typed⟩ := bodyTyped
    have current := (ContextChain.changeHead formed previous).eq henv typed
    exact .tail ih (.forallEDF edge current)

theorem TypeConversion.forallPair
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (leftDomain : env.HasType U target A (.sort u))
    (rightBody : env.IsType U (C :: target) D)
    (domains : TypeConversion env U target A C)
    (bodies : TypeConversion env U (A :: target) B D) :
    TypeConversion env U target (.forallE A B) (.forallE C D) := by
  obtain ⟨level, typed⟩ := rightBody
  have atLeft := (ContextChain.changeHead formed domains.symm).eq henv typed
  exact (TypeConversion.forallSameDomain leftDomain bodies).trans
    (domains.forallDomainPath henv formed ⟨level, atLeft⟩)

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The two independent Pi diagonals turn finite cross-anchor answers into
all future admitted-argument capabilities. Their original domains need not
be the same expression. -/
theorem TypeRelated.literalPiPairIndependentAnchors
    {n : Nat} {ambient : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (hA : env.IsType U target A) (hC : env.IsType U target C)
    (hB : env.IsType U (A :: target) B) (hD : env.IsType U (C :: target) D)
    (domains : TypeConversion env U target A C)
    (bodies : TypeConversion env U (A :: target) B D)
    (prototypeA : TypeConversion env U target A prototypeDomain)
    (prototypeB : TypeConversion env U (A :: target) B prototypeBody)
    (domainRelated : TypeRelated env U registry target A C ambient)
    (domainFormed : ambient.HasType (.sort true))
    (rowDomains : ∀ key result, (key, result) ∈ rows →
      key.input.HasType ambient ∧ result.HasType (.sort relevant) ∧
        TypeConversion env U target key.domain A ∧ TypeRelated env U registry target key.domain A ambient)
    (left : TypeRelated env U registry target (.forallE A B) (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (right : TypeRelated env U registry target (.forallE C D) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (anchors : ∀ key result, (key, result) ∈ rows →
      TypeRelated env U registry target (B.inst key.anchor) (D.inst key.anchor) result) :
    TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody ambient rows) := by
  apply TypeRelated.literalPiPair henv formed hA hC hB hD domains bodies prototypeA prototypeB domainRelated
  · intro key result member
    obtain ⟨typed, _, path, related⟩ := rowDomains key result member
    exact ⟨ambient, typed, domainFormed, Profile.le_refl _, path, related⟩
  · intro key result member Δ ρ future x y admitted
    have left' := left.future henv future
    have right' := right.future henv future
    change TypeRelated env U registry Δ (.forallE (A.lift' ρ) (B.lift' ρ.cons))
      (.forallE (A.lift' ρ) (B.lift' ρ.cons))
      (Profile.pi (prototypeDomain.lift' ρ) (prototypeBody.lift' ρ.cons)
        (ambient.rename ρ) (rows.map fun p => (p.1.rename ρ, p.2.rename ρ))) at left'
    change TypeRelated env U registry Δ (.forallE (C.lift' ρ) (D.lift' ρ.cons))
      (.forallE (C.lift' ρ) (D.lift' ρ.cons))
      (Profile.pi (prototypeDomain.lift' ρ) (prototypeBody.lift' ρ.cons)
        (ambient.rename ρ) (rows.map fun p => (p.1.rename ρ, p.2.rename ρ))) at right'
    have member' := List.mem_map_of_mem (f := fun p : Key _ × Profile _ =>
      (p.1.rename ρ, p.2.rename ρ)) member
    have hΔ := future.targetWF henv
    have lx := left'.literalPiDiagonalRow henv hscoped hΔ member' admitted
    have rx := right'.literalPiDiagonalRow henv hscoped hΔ member' admitted
    have fromAnchor : Admitted env U registry Δ (key.rename ρ) (key.anchor.lift' ρ) x := by
      obtain ⟨path, _, support, typed, formed, code, first, _⟩ := admitted
      exact ⟨path.hasType.1, path, support, typed, formed, code, Related.left_diagonal first, first⟩
    have la := left'.literalPiDiagonalRow henv hscoped hΔ member' fromAnchor
    have ra := right'.literalPiDiagonalRow henv hscoped hΔ member' fromAnchor
    have bridge := (anchors key result member).future henv future
    have outputWF : (result.rename ρ).WF := Profile.rename_wf_iff.mpr (rowDomains key result member).2.1.wf_value
    refine ⟨lx, rx, (la.symm henv outputWF).trans henv ?_⟩
    apply TypeRelated.trans henv _ ra
    simpa only [lift'_inst_hi] using bridge

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- A real original source frame under an independently typed neutral target
binder. Only the selected domain path is used to type the new head. -/
noncomputable def templateNeutralFrame
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (annotationTyped : env.HasType U target annotation (.sort level))
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (path : TypeConversion env U target (A.subst σ) annotation) :
    OriginalRichFrame sourceEnv env U registry (annotation :: target) (.cons context domain)
      (Locals.push locals) ((σ.lift_r (.skip .refl)).cons (.bvar 0)) ((σ.lift_r (.skip .refl)).cons (.bvar 0))
      ((available.rename (.skip .refl)).push []) := by
  let future : FutureInsertion env U target (annotation :: target) (.skip .refl) := .skip (.refl formed) annotationTyped
  let code : RichCert sourceEnv env U registry (annotation :: target) (.ref domain) locals (σ.lift_r (.skip .refl))
      true (.empty : Profile 0) [] := .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  have related : Related env U registry (annotation :: target) (.bvar 0) (.bvar 0)
      (A.subst (σ.lift_r (.skip .refl))) (.empty : Profile 0) .empty :=
    Related.of_singletons (fun _ member => nomatch member)
  exact (frame.future henv future).bind domain code (fun _ _ member => nomatch member)
    (Profile.HasType.empty Profile.WF.empty) related [] (fun _ member => nomatch member) (fun _ member => nomatch member)

theorem templateNeutralFrame_environment
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (annotationTyped : env.HasType U target annotation (.sort level))
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (path : TypeConversion env U target (A.subst σ) annotation) (ordered : sourceEnv.Ordered) :
    (templateNeutralFrame henv formed annotationTyped domain frame path).dependencyEnvironment ordered =
      .close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered) :: frame.dependencyEnvironment ordered := by
  unfold templateNeutralFrame
  change Closure.close (domain.dependencyOrigin ordered)
      ((frame.future henv _).dependencyEnvironment ordered) ::
      ((frame.future henv _).dependencyEnvironment ordered) = _
  rw [OriginalRichFrame.dependencyEnvironment_future]

theorem templateNeutralSubstitutions
    (henv : env.Ordered) (below : sourceEnv ≤ env) (formed : OnCtx target (env.IsType U))
    (annotationTyped : env.HasType U target annotation (.sort level))
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (path : TypeConversion env U target (A.subst σ) annotation) :
    Ctx.SubstEq env U (annotation :: target)
      ((σ.lift_r (.skip .refl)).cons (.bvar 0)) ((σ.lift_r (.skip .refl)).cons (.bvar 0)) (A :: source) := by
  let future : FutureInsertion env U target (annotation :: target) (.skip .refl) := .skip (.refl formed) annotationTyped
  apply Ctx.SubstEq.cons (substitutions.future henv future) (domain.sound.defeq.mono below)
  have neutral : env.HasType U (annotation :: target) (.bvar 0) annotation.lift := .bvar .zero
  have changed := (path.symm.weak' henv future.weakening).cast (by simpa only [HasType, lift_eq_lift'] using neutral)
  simpa only [lift'_subst, Subst.cons_tail, Subst.head, Subst.cons] using changed


/-- The code clause of local template recursion has unrelated displayed
expressions. Its right answer retains the actual generated frame and fixed
common-binder caps, as well as the unconditional conversion path. -/
def TemplateCappedCodeCall
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (left : EndpointState leftEnv U leftSource expression (.sort level))
    (leftContext : ContextDerivation leftEnv U leftSource) (σ : Subst)
    (right : OriginalNestedDisplay U common rightExpression (.sort rightLevel))
    (commonLeft commonRight : Subst) (lf : leftEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext
      leftLocals σ σ leftAvailable),
    leftAvailable.AtomClosed → Ctx.SubstEq env U target σ σ leftSource →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target
      rightLocals commonLeft commonRight rightAvailable),
    CappedCaptureGenerated base caps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    richSchedule .expressionReindex
      ((Closure.close (left.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit →
    ∀ {n : Nat} {relevant : Bool} {profile : Profile n} {footprint : Footprint},
    RichCert leftEnv env U registry target left leftLocals σ relevant profile footprint →
    footprint.Available leftAvailable →
    Nonempty (BoundedParameterReply base caps (expression.subst σ) right
      commonLeft commonRight profile (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

private theorem template_lift_comp (raw commonLeft : Subst) (anchor : VExpr) :
    raw.lift.comp (commonLeft.cons anchor) = (raw.comp commonLeft).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]


private theorem template_neutral_subst (σ : Subst) :
    (σ.lift_r (.skip .refl)).cons (.bvar 0) = σ.lift := by
  funext index
  cases index <;> simp [Subst.lift_r, Subst.lift, Subst.cons, lift_eq_lift']

noncomputable def templateNeutralBase
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (formed : OnCtx target (env.IsType U))
    (annotationTyped : env.HasType U target annotation (.sort level))
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (path : TypeConversion env U target (A.subst σ) annotation) :
    OriginalCaptureBase env U registry (annotation :: target) :=
  (templateNeutralFrame henv formed annotationTyped domain frame path).captureBase
    (templateNeutralSubstitutions henv below formed annotationTyped domain substitutions path)

/-- The unconditional codomain path comes from an actual empty source query
at fresh original body frames. Both original body closures strictly decrease,
including the independent-domain neutral frame on the right. -/
theorem templateEmptyBodyPath
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (leftDomain : EndpointRef leftEnv U leftSource A (.sort u))
    (rightDomain : EndpointRef rightEnv U rightSource C (.sort u'))
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
    (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
    (rightProvenance : EndpointProvenance (.cons rightContext rightDomain) rightBody)
    (lu : u.WF U) (lv : v.WF U) (ru : u'.WF U) (rv : v'.WF U)
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (hA : env.HasType U target (A.subst σ) (.sort u))
    (domains : TypeConversion env U target (A.subst σ) (C.subst τ))
    (limit : Nat)
    (parentBound : richSchedule .expressionReindex
          ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
              (leftFrame.dependencyEnvironment lf)).cost +
           (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
              (rightFrame.dependencyEnvironment rf)).cost) ≤ limit)
    (bodyC : let base := templateNeutralBase henv rightBelow formed hA rightDomain rightFrame rightSubstitutions domains.symm
      TemplateCappedCodeCall base base.initialCaps leftBody (.cons leftContext leftDomain)
        ((σ.lift_r (.skip .refl)).cons (.bvar 0))
        (OriginalNestedDisplay.identity base rightBody rightProvenance) base.left base.right lf rf
        limit) :
    TypeConversion env U (A.subst σ :: target) (B.subst σ.lift) (D.subst τ.lift) := by
  let left := templateNeutralFrame henv formed hA leftDomain leftFrame .refl
  let left' := left
  let base := templateNeutralBase henv rightBelow formed hA rightDomain rightFrame rightSubstitutions domains.symm
  have leftEnvironment : left'.dependencyEnvironment lf =
      .close (leftDomain.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf) :: leftFrame.dependencyEnvironment lf := by
    exact templateNeutralFrame_environment henv formed hA leftDomain leftFrame .refl lf
  have rightEnvironment : base.frame.dependencyEnvironment rf =
      .close (rightDomain.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf) :: rightFrame.dependencyEnvironment rf :=
    templateNeutralFrame_environment henv formed hA rightDomain rightFrame domains.symm rf
  have bound : richSchedule .expressionReindex
      ((Closure.close (leftBody.dependencyOrigin lf) (left'.dependencyEnvironment lf)).cost +
       (Closure.close (rightBody.dependencyOrigin rf) (base.frame.dependencyEnvironment rf)).cost) < limit := by
    rw [leftEnvironment, rightEnvironment]
    apply Nat.lt_of_lt_of_le _ parentBound
    exact richSchedule_strict (Nat.add_lt_add
      (binder_body_cost (by simp) _) (binder_body_cost (by simp) _)) _ _
  have emptyClosed {available : Valuation} (closed : available.AtomClosed) :
      ((available.rename (.skip .refl)).push []).AtomClosed := by
    intro index need member atom present
    cases index with
    | zero => cases member
    | succ index => exact closed.rename _ index need member atom present
  have substitutions :=
      templateNeutralSubstitutions henv leftBelow formed hA leftDomain leftSubstitutions (.refl)
  let query : RichCert leftEnv env U registry (A.subst σ :: target) leftBody
      (Locals.push leftLocals) ((σ.lift_r (.skip .refl)).cons (.bvar 0)) true (.empty : Profile 0) [] :=
    .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  obtain ⟨answer⟩ := bodyC left' (emptyClosed leftClosed) substitutions base.identityRealization
    base.identityCapped (emptyClosed rightClosed) bound query (fun _ _ member => nomatch member)
  simpa only [base, templateNeutralBase, OriginalRichFrame.captureBase, OriginalNestedDisplay.identity,
    template_neutral_subst] using answer.path

section
variable
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
  {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
  {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
  {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
  {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v)}
  {rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v')}
  {lu : u.WF U} {lv : v.WF U} {ru : u'.WF U} {rv : v'.WF U}
  (leftLocation : Located leftRoot (.pi lu lv (.ref leftDomain) leftBody))
  (rightLocation : Located rightRoot (.pi ru rv (.ref rightDomain) rightBody))
  (leftInitial : ContextDerivation leftEnv U leftRootSource)
  (rightInitial : ContextDerivation rightEnv U rightRootSource)
  (rightGraph : OriginalCaptureMap (common := common) (rightLocation.contextDerivation rightInitial) rightRaw)
  (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
  (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
  (leftFrame : OriginalRichFrame leftEnv env U registry target
    (leftLocation.contextDerivation leftInitial) leftLocals σ σ leftAvailable)
  (leftClosed : leftAvailable.AtomClosed)
  (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)

include henv leftBelow rightBelow leftClosed leftSubstitutions in
/-- Every actual source row is compared at its proper original body child.
The destination head starts empty; its cap, rather than a guessed supply,
ensures that the returned query can be packed back into the same frozen row. -/
theorem RichRows.templateCappedReplies
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      (rightGraph.locals base.locals) commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base caps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals σ
      true (ambient : Profile n) leftFootprint)
    (leftResources : leftFootprint.Available leftAvailable)
    (domainAnswer : TemplateCodeResult env U registry target (.ref leftDomain) (.ref rightDomain)
      (rightGraph.locals base.locals) σ (rightRaw.comp commonLeft) rightAvailable true ambient)
    (parentLimit : Nat)
    (parentBound : richSchedule .expressionReindex
      ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost) ≤ parentLimit)
    (bodyC : ∀ (key : Key n), TemplateCappedCodeCall base (caps.push (Need.Fits key.input))
      leftBody (.cons (leftLocation.contextDerivation leftInitial) leftDomain) (σ.cons key.anchor)
      (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rfl rfl)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf parentLimit)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals
      σ relevant ambient values footprint)
    (resources : footprint.Available leftAvailable) :
    ∃ answers : CappedPiRowAnswers (base := base) (commonCaps := caps)
      rightLocation rightInitial rightGraph rfl rfl commonLeft commonRight ambient relevant values,
      answers.Bounded rightFrame ∧
      ∀ key output, (key, output) ∈ values →
        TypeRelated env U registry target (B.subst (σ.cons key.anchor))
          (D.subst ((rightRaw.comp commonLeft).cons key.anchor)) output := by
  match rows with
  | .nil => exact ⟨.nil, True.intro, fun _ _ member => nomatch member⟩
  | .cons (key := key) (support := output) (bodyFootprint := bodyFootprint) guard certificate pack covered rest =>
    have rightGuard : LambdaGuard env U registry target (rightRaw.comp commonLeft) C key ambient := {
      inputTyped := guard.inputTyped, formed := guard.formed, anchor := guard.anchor
      path := guard.path.trans domainAnswer.path
      domains := guard.domains.trans henv domainAnswer.related }
    let needs := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have bounded := fun need member => (pack.atomized_localNeeds need member).1
    have cover := fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
    have leftArguments : Related env U registry target key.anchor key.anchor (A.subst σ) key.input ambient :=
      LambdaGuard.anchorRelated henv guard
    let leftChild := leftFrame.bind leftDomain leftCode leftResources guard.inputTyped leftArguments needs bounded cover
    have rightArguments : Related env U registry target key.anchor key.anchor
        (C.subst (rightRaw.comp commonLeft)) key.input ambient :=
      LambdaGuard.anchorRelated henv rightGuard
    obtain ⟨rightChild, rightGenerated, rightEnvironment⟩ := rightFrame.bindCapped rightCapped rightDomain
      (C.subst rightRaw) rfl rightBelow domainAnswer.certificate domainAnswer.resources rightGuard.inputTyped
      rightArguments (rightGuard.path.cast rightGuard.anchor.1) []
      (fun _ member => nomatch member) (fun _ member => nomatch member)
    have bodyResources := pack.available_atomized_localNeeds
      (fun index need member => resources index need (List.mem_append_left _ member))
    have callBound : richSchedule .expressionReindex
        ((Closure.close (leftBody.dependencyOrigin lf) (leftChild.dependencyEnvironment lf)).cost +
         (Closure.close (rightBody.dependencyOrigin rf) (rightChild.frame.dependencyEnvironment rf)).cost) < parentLimit := by
      rw [rightEnvironment rf]
      apply Nat.lt_of_lt_of_le _ parentBound
      exact richSchedule_strict (Nat.add_lt_add
        (binder_body_cost (by simp) _) (binder_body_cost (by simp) _)) _ _
    have rightClosed' : (rightAvailable.push []).AtomClosed := by
      intro index need member atom present
      cases index with
      | zero => cases member
      | succ index => exact rightClosed index need member atom present
    obtain ⟨reply⟩ := bodyC key leftChild (Valuation.push_atomized_closed leftClosed _)
      (.cons leftSubstitutions (leftDomain.sound.defeq.mono leftBelow) (guard.path.cast guard.anchor.1))
      rightChild rightGenerated rightClosed' callBound certificate bodyResources
    obtain ⟨tailAnswers, tailBound, tailAnchors⟩ := rest.templateCappedReplies rightFrame rightCapped rightClosed leftCode leftResources
      domainAnswer parentLimit parentBound bodyC
      (fun index need member => resources index need (List.mem_append_right _ member))
    refine ⟨.cons key output rightGuard certificate.formed reply.reply.answer tailAnswers,
      ⟨?_, tailBound⟩, ?_⟩
    · intro ordered
      simpa only [rightEnvironment rf, generatedBinder_environmentCost] using reply.reply.bounded ordered
    · intro requested output' member
      rcases List.mem_cons.mp member with same | member
      · cases same
        simpa only [subst_subst, template_lift_comp] using reply.related
      · exact tailAnchors requested output' member
termination_by sizeOf rows


/-- Original guards and row certificates supply the row typing data on the
same native table that was recursively reconstructed. -/
theorem RichRows.templateRowDomains
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals
      σ relevant (ambient : Profile n) values footprint) :
    ∀ key output, (key, output) ∈ values →
      key.input.HasType ambient ∧ output.HasType (.sort relevant) ∧
      TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) ambient := by
  intro key output member
  match rows with
  | .nil => cases member
  | .cons guard certificate pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨guard.inputTyped, certificate.formed, guard.path, guard.domains⟩
    · exact tail.templateRowDomains key output member
termination_by sizeOf rows

include henv leftBelow rightBelow leftClosed leftSubstitutions in
/-- Native Pi comparison after its actual domain child has returned. Finite
body replies are packed through their actual capped frames. An additional
EMPTY fresh-body request computes the unconditional raw path, and the two
strict unary original calls supply all future admitted row capabilities. -/
theorem templatePiNativeOfDomain
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      (rightGraph.locals base.locals) commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base caps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals σ
      true (ambient : Profile n) leftFootprint)
    (leftResources : leftFootprint.Available leftAvailable)
    (domainAnswer : TemplateCodeResult env U registry target (.ref leftDomain) (.ref rightDomain)
      (rightGraph.locals base.locals) σ (rightRaw.comp commonLeft) rightAvailable true ambient)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals
      σ relevant ambient values footprint)
    (resources : footprint.Available leftAvailable)
    (hA : env.HasType U target (A.subst σ) (.sort u))
    (limit : Nat)
    (parentBound : (Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost ≤ limit)
    (leftF : OriginalCodeInductionAt env registry lf leftInitial leftLocation limit)
    (rightF : OriginalCodeInductionAt env registry rf rightInitial rightLocation limit)
    (bodyC : ∀ (key : Key n), TemplateCappedCodeCall base (caps.push (Need.Fits key.input))
      leftBody (.cons (leftLocation.contextDerivation leftInitial) leftDomain) (σ.cons key.anchor)
      (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rfl rfl)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf (richSchedule .expressionReindex limit))
    (freshBodyC : let freshBase := (templateNeutralBase henv rightBelow formed hA rightDomain
        rightFrame.frame.leftDiagonal rightFrame.substitutions.left domainAnswer.path.symm)
      TemplateCappedCodeCall freshBase freshBase.initialCaps leftBody
        (.cons (leftLocation.contextDerivation leftInitial) leftDomain)
        ((σ.lift_r (.skip .refl)).cons (.bvar 0))
        (OriginalNestedDisplay.identity freshBase rightBody
          (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rfl rfl).provenance)
        freshBase.left freshBase.right lf rf (richSchedule .expressionReindex limit)) :
    Nonempty (BoundedParameterReply base caps ((VExpr.forallE A B).subst σ)
      (OriginalNestedDisplay.pi rightLocation rightInitial rightGraph rfl rfl)
      commonLeft commonRight (Profile.pi prototypeDomain prototypeBody ambient values)
      (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  have scheduled : richSchedule .expressionReindex
      ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost) ≤ richSchedule .expressionReindex limit := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 parentBound) _
  have freshBound : richSchedule .expressionReindex
      ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.leftDiagonal.dependencyEnvironment rf)).cost) ≤ richSchedule .expressionReindex limit := by
    simpa only [OriginalRichFrame.dependencyEnvironment_leftDiagonal] using scheduled
  have bodies := templateEmptyBodyPath henv leftBelow rightBelow lf rf formed leftDomain rightDomain leftBody rightBody
    (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rfl rfl).provenance
    lu lv ru rv leftFrame rightFrame.frame.leftDiagonal leftClosed rightClosed leftSubstitutions
    rightFrame.substitutions.left hA domainAnswer.path _ freshBound freshBodyC
  have hC := (rightDomain.sound.defeq.mono rightBelow).subst henv rightFrame.substitutions.left formed
  have hB := (leftBody.sound.defeq.mono leftBelow).subst henv
    (leftSubstitutions.lift henv (leftDomain.sound.defeq.mono leftBelow)) ⟨formed, _, hA⟩
  have hD := (rightBody.sound.defeq.mono rightBelow).subst henv
    (rightFrame.substitutions.left.lift henv (rightDomain.sound.defeq.mono rightBelow)) ⟨formed, _, hC⟩
  have rightGuard : PiGuard env U target (rightRaw.comp commonLeft) C D prototypeDomain prototypeBody := {
    domainPath := domainAnswer.path.symm.trans guard.domainPath
    bodyPath := TypeConversion.changeDomain henv formed hC hA domainAnswer.path.symm
      (bodies.symm.trans guard.bodyPath) }
  obtain ⟨answers, answersBound, anchors⟩ := rows.templateCappedReplies
    leftLocation rightLocation leftInitial rightInitial rightGraph henv leftBelow rightBelow lf rf
    leftFrame leftClosed leftSubstitutions rightFrame rightCapped rightClosed leftCode leftResources
    domainAnswer _ scheduled bodyC resources
  obtain ⟨finalAvailable, finalFrame, finalCapped, finalClosed, _includes, finalBound,
    finalFootprint, ⟨finalCode⟩, finalResources⟩ :=
    answers.piCode henv rightFrame rightCapped rightClosed answersBound
      domainAnswer.certificate domainAnswer.resources rightGuard
  have leftBound : (Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
      (leftFrame.dependencyEnvironment lf)).cost < limit :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Closure.cost_pos _)) parentBound
  have rightBound : (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
      (finalFrame.frame.leftDiagonal.dependencyEnvironment rf)).cost < limit := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    have actual := Nat.mul_le_mul_left
      ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf).weight
      (Nat.add_le_add_left (finalBound rf) 1)
    have smaller : (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost < limit :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (Closure.cost_pos _)) parentBound
    exact Nat.lt_of_le_of_lt actual smaller
  let leftQuery : RichCert leftEnv env U registry target (.pi lu lv (.ref leftDomain) leftBody)
      leftLocals σ relevant (Profile.pi prototypeDomain prototypeBody ambient values) (leftFootprint ++ footprint) :=
    .pi lu lv leftCode guard rows
  have leftResources' : (leftFootprint ++ footprint).Available leftAvailable := by
    intro index need member
    exact (List.mem_append.mp member).elim (leftResources index need) (resources index need)
  obtain ⟨leftAnswer⟩ := leftF target leftLocals σ σ leftAvailable leftFrame leftBound leftClosed
    formed leftSubstitutions leftQuery leftResources'
  obtain ⟨rightAnswer⟩ := rightF target (rightGraph.locals base.locals)
    (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) finalAvailable finalFrame.frame.leftDiagonal
    rightBound finalClosed formed finalFrame.substitutions.left finalCode finalResources
  have related : TypeRelated env U registry target
      (.forallE (A.subst σ) (B.subst σ.lift))
      (.forallE (C.subst (rightRaw.comp commonLeft)) (D.subst (rightRaw.comp commonLeft).lift))
      (Profile.pi prototypeDomain prototypeBody ambient values) := by
    apply TypeRelated.literalPiPairIndependentAnchors henv hscoped formed ⟨_, hA⟩ ⟨_, hC⟩
      ⟨_, hB⟩ ⟨_, hD⟩ domainAnswer.path bodies guard.domainPath guard.bodyPath domainAnswer.related
      leftCode.formed (rows.templateRowDomains) leftAnswer.related rightAnswer.related
    intro key output member
    simpa only [inst_lift_cons] using anchors key output member
  have path := TypeConversion.forallPair henv formed hA ⟨_, hD⟩ domainAnswer.path bodies
  refine ⟨⟨⟨⟨⟨_, finalAvailable, finalFrame, finalCapped.generated,
    finalCode.graded finalResources, finalClosed⟩, finalCapped⟩, finalBound⟩, ?_, ?_⟩⟩
  · simpa only [subst, subst_subst, Subst.comp_lift] using related
  · simpa only [subst, subst_subst, Subst.comp_lift] using path


include henv leftBelow rightBelow leftClosed leftSubstitutions in
/-- Productive local native Pi code comparison. The domain request selects
its real right frame; every row and the fresh empty-body request then use
that frame. All calls are paid by the two actual original Pi closures. -/
theorem templatePiStep
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base caps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals σ
      true (ambient : Profile n) leftFootprint)
    (leftResources : leftFootprint.Available leftAvailable)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals
      σ relevant ambient values footprint)
    (resources : footprint.Available leftAvailable)
    (limit : Nat)
    (limit_eq : limit =
      (Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost)
    (leftF : OriginalCodeInductionAt env registry lf leftInitial leftLocation limit)
    (rightF : OriginalCodeInductionAt env registry rf rightInitial rightLocation limit)
    (domainC : TemplateCappedCodeCall base caps (.ref leftDomain)
      (leftLocation.contextDerivation leftInitial) σ
      (OriginalNestedDisplay.piDomain rightLocation rightInitial rightGraph rfl)
      commonLeft commonRight lf rf (richSchedule .expressionReindex limit))
    (bodyC : ∀ (key : Key n), TemplateCappedCodeCall base (caps.push (Need.Fits key.input))
      leftBody (.cons (leftLocation.contextDerivation leftInitial) leftDomain) (σ.cons key.anchor)
      (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rfl rfl)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf (richSchedule .expressionReindex limit))
    (freshBodyC : ∀ {selectedAvailable}
      (selected : OriginalCaptureRealization rightGraph env registry target
        (rightGraph.locals base.locals) commonLeft commonRight selectedAvailable),
      CappedCaptureGenerated base caps commonLeft commonRight rightGraph selected.frame.raw →
      selectedAvailable.AtomClosed →
      (∀ ordered, environmentCost (selected.frame.dependencyEnvironment ordered) ≤
        environmentCost (rightFrame.frame.dependencyEnvironment rf)) →
      ∀ (hA : env.HasType U target (A.subst σ) (.sort u))
        (domains : TypeConversion env U target (A.subst σ) (C.subst (rightRaw.comp commonLeft))),
      let freshBase := (templateNeutralBase henv rightBelow formed hA rightDomain
        selected.frame.leftDiagonal selected.substitutions.left domains.symm)
      TemplateCappedCodeCall freshBase freshBase.initialCaps leftBody
        (.cons (leftLocation.contextDerivation leftInitial) leftDomain)
        ((σ.lift_r (.skip .refl)).cons (.bvar 0))
        (OriginalNestedDisplay.identity freshBase rightBody
          (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rfl rfl).provenance)
        freshBase.left freshBase.right lf rf (richSchedule .expressionReindex limit)) :
    Nonempty (BoundedParameterReply base caps ((VExpr.forallE A B).subst σ)
      (OriginalNestedDisplay.pi rightLocation rightInitial rightGraph rfl rfl)
      commonLeft commonRight (Profile.pi prototypeDomain prototypeBody ambient values)
      (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  have domainBound : richSchedule .expressionReindex
      ((Closure.close (leftDomain.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close (rightDomain.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) <
        richSchedule .expressionReindex limit := by
    rw [limit_eq]
    exact richSchedule_strict (Nat.add_lt_add (binder_domain_cost _ [_] [] _) (binder_domain_cost _ [_] [] _)) _ _
  obtain ⟨⟨⟨⟨⟨nextLocals, nextAvailable, next, _nextGenerated, query, nextClosed⟩,
    nextCapped⟩, nextBound⟩, domainRelated, domainPath⟩⟩ :=
    domainC leftFrame leftClosed leftSubstitutions rightFrame rightCapped rightClosed
      domainBound leftCode leftResources
  have sameLocals : nextLocals = rightGraph.locals base.locals := nextCapped.generated.locals_eq
  subst nextLocals
  obtain ⟨domainFootprint, ⟨domainCode⟩, domainResources⟩ := query.code henv leftCode.formed
  let domainAnswer : TemplateCodeResult env U registry target (.ref leftDomain) (.ref rightDomain)
      (rightGraph.locals base.locals) σ (rightRaw.comp commonLeft) nextAvailable true ambient := {
    footprint := domainFootprint, certificate := domainCode, resources := domainResources
    related := by simpa only [subst_subst] using domainRelated
    path := by simpa only [subst_subst] using domainPath }
  have parentBound : (Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
      (leftFrame.dependencyEnvironment lf)).cost +
      (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (next.frame.dependencyEnvironment rf)).cost ≤ limit := by
    rw [limit_eq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left (nextBound rf) 1)) _
  have hA := (leftDomain.sound.defeq.mono leftBelow).subst henv leftSubstitutions formed
  obtain ⟨answer⟩ := templatePiNativeOfDomain leftLocation rightLocation leftInitial rightInitial rightGraph
    henv leftBelow rightBelow lf rf leftFrame leftClosed leftSubstitutions hscoped formed
    next nextCapped nextClosed leftCode leftResources domainAnswer guard rows resources hA limit parentBound
    leftF rightF bodyC (freshBodyC next nextCapped nextClosed nextBound hA domainAnswer.path)
  exact ⟨{ answer with reply := { answer.reply with
    bounded := fun ordered => Nat.le_trans (answer.reply.bounded ordered) (nextBound rf) } }⟩

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
