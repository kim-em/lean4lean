import Lean4Lean.Theory.Typing.AnchoredNativeInitialGuard
import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredLiteralPi
import Lean4Lean.Theory.Typing.NativeCaptureAbstraction

/-! A demanded codomain bridge from original lambda-type conversions.
The whole Pi certificate crosses the original conversion children first.
Only then are literal target Pi components read from the resulting witness;
no raw Pi-injectivity theorem is used.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- A supported row of a binary literal Pi capability yields the exact
instantiated codomain path and code capability at the original base world. -/
theorem TypeRelated.literalPiBody
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {A C B prototypeDomain prototypeBody : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n} {argument : VExpr}
    (whole : TypeRelated env U registry Γ (.forallE A C) (.forallE A B)
      (.pi prototypeDomain prototypeBody domain rows))
    (member : (key, result) ∈ rows)
    (admitted : Admitted env U registry Γ key argument argument) :
    TypeConversion env U Γ (C.inst argument) (B.inst argument) ∧
      TypeRelated env U registry Γ (C.inst argument) (B.inst argument) result := by
  have atBase := whole Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at atBase
  obtain ⟨display⟩ := atBase (.pi prototypeDomain prototypeBody domain rows)
    (List.mem_singleton_self _)
  have insertion := display.leftExposure.insertion henv
  have hTarget := display.leftExposure.targetWF henv
  have args := insertion.admitted henv admitted
  have row := display.rowBodies key result member display.context .refl (.refl hTarget)
    (argument.lift' display.map) (argument.lift' display.map) (by
      simpa only [Lift.comp, Admitted] using args)
  have leftBody := display.leftExposure.literalPi_components |>.2
  have rightBody := display.rightExposure.literalPi_components |>.2
  have leftEq : display.leftBody.inst (argument.lift' display.map) =
      (C.inst argument).lift' display.map := by
    rw [leftBody, lift'_inst_hi]
  have rightEq : display.rightBody.inst (argument.lift' display.map) =
      (B.inst argument).lift' display.map := by
    rw [rightBody, lift'_inst_hi]
  have bodyCode : TypeRelated env U registry display.context
      ((C.inst argument).lift' display.map) ((B.inst argument).lift' display.map)
      (result.rename display.map) := by
    simpa only [TypeRelated, Lift.comp, lift'_depth_zero (l := Lift.refl.cons) rfl, leftEq, rightEq] using row.2.2
  obtain ⟨support, _, _, _, domainPath, _⟩ := display.rowDomains key result member
  have argumentTyped : env.HasType U display.context (argument.lift' display.map) display.leftDomain :=
    domainPath.cast args.2.1
  obtain ⟨level, formedDomain⟩ := display.leftDomainType
  have substitution : Ctx.SubstEq env U display.context
      (Subst.id.cons (argument.lift' display.map))
      (Subst.id.cons (argument.lift' display.map)) (display.leftDomain :: display.context) := by
    refine .cons (Ctx.SubstEq.id henv hTarget) formedDomain ?_
    simpa only [HasType, Subst.cons_tail, Subst.head, Subst.cons, subst_id] using argumentTyped
  have bodyPath := display.bodies.substTarget henv hTarget substitution
  have renamedPath : TypeConversion env U display.context
      ((C.inst argument).lift' display.map) ((B.inst argument).lift' display.map) := by
    simpa only [← inst_eq, leftEq, rightEq] using bodyPath
  exact ⟨insertion.pathBack henv renamedPath, insertion.codeBack henv hscoped bodyCode⟩


/-- The raw body path is present even in an empty-row Pi observation.
Only the actual argument typing is needed to instantiate it. -/
theorem TypeRelated.literalPiBodyPath
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {A A' C B prototypeDomain prototypeBody : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)} {argument : VExpr}
    (whole : TypeRelated env U registry Γ (.forallE A C) (.forallE A' B)
      (.pi prototypeDomain prototypeBody domain rows))
    (argumentTyped : env.HasType U Γ argument A) :
    TypeConversion env U Γ (C.inst argument) (B.inst argument) := by
  have atBase := whole Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at atBase
  obtain ⟨display⟩ := atBase (.pi prototypeDomain prototypeBody domain rows)
    (List.mem_singleton_self _)
  have insertion := display.leftExposure.insertion henv
  have hTarget := display.leftExposure.targetWF henv
  have leftComponents := display.leftExposure.literalPi_components
  have rightComponents := display.rightExposure.literalPi_components
  have argumentTyped' : env.HasType U display.context (argument.lift' display.map) display.leftDomain := by
    rw [leftComponents.1]
    simpa only [HasType, VExpr.lift'] using insertion.eq henv argumentTyped
  obtain ⟨level, formedDomain⟩ := display.leftDomainType
  have substitution : Ctx.SubstEq env U display.context
      (Subst.one (argument.lift' display.map)) (Subst.one (argument.lift' display.map))
      (display.leftDomain :: display.context) := by
    refine .cons (Ctx.SubstEq.id henv hTarget) formedDomain ?_
    simpa only [HasType, Subst.cons_tail, Subst.head, Subst.cons, subst_id] using argumentTyped'
  have renamedPath := display.bodies.substTarget henv hTarget substitution
  rw [← inst_eq, ← inst_eq, leftComponents.2, rightComponents.2, ← lift'_inst_hi,
    ← lift'_inst_hi] at renamedPath
  exact insertion.pathBack henv renamedPath

/-- Read the raw codomain conversion at a fresh neutral variable. No
inhabitant in the base world or retained Pi row is required. The two literal
domains may differ; the path lives under the actual left domain. -/
theorem TypeRelated.literalPiBodyUnderBinderPath
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {A A' B B' prototypeDomain prototypeBody : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)}
    (formed : env.IsType U Γ A)
    (whole : TypeRelated env U registry Γ (.forallE A B) (.forallE A' B')
      (.pi prototypeDomain prototypeBody domain rows)) :
    TypeConversion env U (A :: Γ) B B' := by
  obtain ⟨level, typed⟩ := formed
  let future : FutureInsertion env U Γ (A :: Γ) (.skip .refl) := .skip (.refl hΓ) typed
  have raised := whole.future henv future
  have path := TypeRelated.literalPiBodyPath henv (show OnCtx (A :: Γ) (env.IsType U) from
    ⟨hΓ, _, typed⟩) raised (show env.HasType U (A :: Γ) (.bvar 0) (A.lift' (.skip .refl)) from by
      simpa only [lift_eq_lift'] using (HasType.bvar (env := env) (U := U) (Lookup.zero (Γ := Γ) (ty := A))))
  change TypeConversion env U (A :: Γ)
    ((B.lift' (.consN (.skipN .refl 1) 1)).inst (.bvar 0))
    ((B'.lift' (.consN (.skipN .refl 1) 1)).inst (.bvar 0)) at path
  simpa only [lift'_consN_skipN, inst_liftN_bvar] using path

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- A lambda's outer type conversions, with the semantic result of each
original Strong conversion child retained at the same edge. -/
inductive OriginalLambdaTypePath (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source : List VExpr) : VExpr → VExpr → Prop
  | refl : OriginalLambdaTypePath sourceEnv env U registry source A A
  | tail : OriginalLambdaTypePath sourceEnv env U registry source A B →
      sourceEnv.IsDefEqStrong U source B C (.sort level) →
      GradedJoint env U registry source B C (.sort level) →
      OriginalLambdaTypePath sourceEnv env U registry source A C

/-- The original natural lambda typing, before its outer type conversions.
The body type is stored literally, together with its original-child semantics. -/
structure OriginalLambdaOrigin (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source : List VExpr) (A body assigned : VExpr) where
  bodyType : VExpr
  domainLevel : VLevel
  bodyLevel : VLevel
  domainStrong : sourceEnv.IsDefEqStrong U source A A (.sort domainLevel)
  bodyTypeStrong : sourceEnv.IsDefEqStrong U (A :: source) bodyType bodyType (.sort bodyLevel)
  bodyStrong : sourceEnv.IsDefEqStrong U (A :: source) body body bodyType
  bodyTyping : sourceEnv.HasTypeStrong U (A :: source) body bodyType true
  domainJoint : GradedJoint env U registry source A A (.sort domainLevel)
  bodyTypeJoint : GradedJoint env U registry (A :: source) bodyType bodyType (.sort bodyLevel)
  bodyJoint : GradedJoint env U registry (A :: source) body body bodyType
  naturalJoint : GradedJoint env U registry source (.forallE A bodyType) (.forallE A bodyType)
    (.sort (.imax domainLevel bodyLevel))
  conversions : OriginalLambdaTypePath sourceEnv env U registry source (.forallE A bodyType) assigned

/-- Only the original lam children and outer conversion children are sent to
`earlier`, the theorem at the strict predecessor declaration stage. In
particular the declared codomain is never inferred by lambda/Pi inversion. -/
theorem HasTypeStrong.originalLambdaOrigin
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source : List VExpr} {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    {A body : VExpr} (isLambda : expression = .lam A body) :
    Nonempty (OriginalLambdaOrigin sourceEnv env U registry source A body assigned) := by
  induction original generalizing A body with
  | lam hu hv domain bodyType bodyTyping natural _ _ _ _ =>
    cases isLambda
    exact ⟨{
      bodyType := _
      domainLevel := _
      bodyLevel := _
      domainStrong := domain.refl
      bodyTypeStrong := bodyType.refl
      bodyStrong := bodyTyping.refl
      bodyTyping := bodyTyping
      domainJoint := earlier domain.refl
      bodyTypeJoint := earlier bodyType.refl
      bodyJoint := earlier bodyTyping.refl
      naturalJoint := earlier natural.refl
      conversions := .refl }⟩
  | base _ ih => exact ih isLambda
  | defeq hu conversion _ _ _ _ _ ih =>
    obtain ⟨origin⟩ := ih isLambda
    exact ⟨{ origin with conversions := .tail origin.conversions conversion (earlier conversion) }⟩
  | _ => cases isLambda

/-- A concrete certificate crosses the retained conversion chain without
changing its finite profile. The returned certificate is still actual source
syntax; the semantic bridge and raw path point back to the natural Pi type. -/
theorem OriginalLambdaTypePath.transfer
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {natural assigned : VExpr}
    (path : OriginalLambdaTypePath sourceEnv env U registry source natural assigned)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ natural support footprint)
    (resources : footprint.Available available)
    (selfCode : TypeRelated env U registry target (natural.subst σ) (natural.subst σ) support) :
    Nonempty (InitialNativeAlignment env U registry target locals σ available natural assigned support) := by
  induction path with
  | refl => exact ⟨⟨footprint, certificate, resources, .refl, selfCode⟩⟩
  | tail _ conversion joint ih =>
    obtain ⟨previous⟩ := ih
    obtain ⟨next⟩ := previous.naturalCertificate.transfer_graded henv hscoped hTarget closed
      (joint target locals σ σ available closed hTarget substitutions fits).1 previous.resources
    have raw := (conversion.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
    exact ⟨{
      footprint := next.footprint
      naturalCertificate := next.certificate
      resources := next.available
      path := (TypeConversion.single raw).symm.trans previous.path
      related := TypeRelated.trans henv (next.related.symm henv certificate.formed.wf_value)
        previous.related }⟩

/-- The chain starts with the original whole natural-Pi formation child;
there is no separate caller-supplied semantic identity capability. -/
theorem OriginalLambdaOrigin.transport
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {A body assigned : VExpr}
    (origin : OriginalLambdaOrigin sourceEnv env U registry source A body assigned)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ (.forallE A origin.bodyType) support footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeAlignment env U registry target locals σ available
      (.forallE A origin.bodyType) assigned support) := by
  obtain ⟨base⟩ := certificate.transfer_graded henv hscoped hTarget closed
    (origin.naturalJoint target locals σ σ available closed hTarget substitutions fits).1 resources
  exact origin.conversions.transfer henv hscoped hle closed hTarget substitutions fits
    base.certificate base.available base.related


/-- The original conversion chain aligns one actual captured argument's
codomains while retaining the converted whole SOURCE certificate. A subsequent
source Pi-row extraction can therefore read the declared body certificate;
the bridge is not an added hypothesis on that extraction. -/
theorem OriginalLambdaOrigin.bodyAlignment
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {A body B : VExpr}
    (origin : OriginalLambdaOrigin sourceEnv env U registry source A body (.forallE A B))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {prototypeDomain prototypeBody : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    {argument : VExpr} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ (.forallE A origin.bodyType)
      (.pi prototypeDomain prototypeBody domain rows) footprint)
    (resources : footprint.Available available)
    (member : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key argument argument) :
    Nonempty (InitialNativeAlignment env U registry target locals σ available
      (.forallE A origin.bodyType) (.forallE A B) (.pi prototypeDomain prototypeBody domain rows)) ∧
    TypeConversion env U target (origin.bodyType.subst (σ.cons argument))
      (B.subst (σ.cons argument)) ∧
    TypeRelated env U registry target (origin.bodyType.subst (σ.cons argument))
      (B.subst (σ.cons argument)) result := by
  obtain ⟨aligned⟩ := origin.transport henv hscoped hle closed hTarget substitutions fits
    certificate resources
  have forward := aligned.related.symm henv certificate.formed.wf_value
  change TypeRelated env U registry target
    (.forallE (A.subst σ) (origin.bodyType.subst σ.lift))
    (.forallE (A.subst σ) (B.subst σ.lift)) _ at forward
  have bodies := forward.literalPiBody henv hscoped hTarget member admitted
  exact ⟨⟨aligned⟩, by simpa only [inst_lift_cons] using bodies.1,
    by simpa only [inst_lift_cons] using bodies.2⟩


/-- A resource-free finite natural-Pi certificate suffices for the raw
codomain conversion. Thus no caller-provided body certificate or component
conversion is needed for the typed beta-contraction step. -/
theorem OriginalLambdaOrigin.rawBodyPath
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {A body B : VExpr}
    (origin : OriginalLambdaOrigin sourceEnv env U registry source A body (.forallE A B))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {argument : VExpr} (argumentTyped : env.HasType U target argument (A.subst σ)) :
    TypeConversion env U target (origin.bodyType.subst (σ.cons argument))
      (B.subst (σ.cons argument)) := by
  let profile : Profile 1 := .pi (A.subst σ) (origin.bodyType.subst σ.lift) .empty []
  have formed : profile.HasType (.sort true) := Profile.HasType.pi_empty (.empty (.sort true)) true
  let certificate : CodeCert env U registry target locals σ (.forallE A origin.bodyType) profile [] :=
    .seed (.pi (.seed .empty (.empty (.sort true))) PiGuard.literal .nil) formed
  obtain ⟨aligned⟩ := origin.transport henv hscoped hle closed hTarget substitutions fits
    certificate (fun _ _ h => nomatch h)
  have forward := aligned.related.symm henv formed.wf_value
  change TypeRelated env U registry target
    (.forallE (A.subst σ) (origin.bodyType.subst σ.lift))
    (.forallE (A.subst σ) (B.subst σ.lift)) profile at forward
  simpa only [inst_lift_cons] using forward.literalPiBodyPath henv hTarget argumentTyped

end Lean4Lean.AnchoredSource.Adapted
