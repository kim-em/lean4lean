import Lean4Lean.Theory.Typing.AnchoredOriginalPayload
import Lean4Lean.Theory.Typing.AnchoredNativeArgumentCuts
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceInstantiation
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction

/-! The first converted dependent application in a native argument spine.
The second argument is initially typed at the application's natural domain.
Its finite demand crosses the ORIGINAL function-type conversion as a Pi row;
inverse substitution then records actual observations of the first argument.
No alignment between two independently inferred argument types is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The first argument's actual cut ledger and a certificate of the registered
second domain. The first input is chosen after collecting every cut, and may
have a larger grade than the observed second argument. -/
structure ConvertedSecondInput (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (first second naturalDomain declaredDomain : VExpr) (input : Profile n) where
  before : Footprint
  beforeAvailable : before.Available available
  required : Footprint
  cuts : InstFootprint env U registry target locals σ first 0 before required
  firstInput : FactoredArguments env U registry target locals σ available first required (n + 1)
  support : Profile n
  footprint : Footprint
  certificate : CodeCert env U registry target locals σ (declaredDomain.inst first) support footprint
  resources : footprint.Available available
  typed : input.HasType support
  alignment : DomainChain env U registry target input (naturalDomain.subst σ)
    ((declaredDomain.inst first).subst σ)
  admitted : Admitted env U registry target
    ⟨(declaredDomain.inst first).subst σ, second.subst σ, input⟩
    (second.subst σ) (second.subst σ)

private theorem one_comp (a : VExpr) (σ : Subst) :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  funext i; cases i <;> rfl

/-- A two-argument spine with an arbitrary original conversion between its
first residual and the second application's Pi type. All semantic premises
are original Strong payloads: the registered telescope formation, its first
argument, the second argument, and that conversion child. -/
theorem convertedSecondInput
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {D E R a b B C : VExpr} {conversionLevel : VLevel}
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
      source (.forallE D (.forallE E R)))
    (first : OriginalTypePayload sourceEnv env U registry source a D)
    (second : OriginalTypePayload sourceEnv env U registry source b B)
    {conversion : sourceEnv.IsDefEqStrong U source ((VExpr.forallE E R).inst a)
      (.forallE B C) (.sort conversionLevel)}
    (converted : OriginalPayload sourceEnv env U registry conversion)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ b input footprint)
    (resources : footprint.Available available) :
    Nonempty (ConvertedSecondInput env U registry target locals σ available a b B E input) := by
  obtain ⟨secondValue⟩ := (second.2 target locals σ σ available closed hTarget substitutions fits).1
    observation resources
  let d := lowerProfile n secondValue.bound secondValue.support
  let key : Key n := ⟨B.subst σ, b.subst σ, input⟩
  have typed : input.HasType d := secondValue.requestedTyped
  have domain := secondValue.requestedCertificate
  have rawSecond := (second.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have code := TypeRelated.lower henv secondValue.bound secondValue.typeCode
  have value := secondValue.requestedRelated henv hTarget
  have guard : LambdaGuard env U registry target σ B key d :=
    ⟨typed, domain.formed, .refl, code,
      ⟨rawSecond, rawSecond, d, typed, domain.formed, code, value, value⟩⟩
  let rows : List (Key n × Profile n) := [(key, .empty)]
  have bodies : PiRows env U registry target locals σ B C d rows [] :=
    .cons guard (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))) .nil
      (fun _ h => nomatch h) .nil
  have sorted : (Profile.pi (B.subst σ) (C.subst σ.lift) d rows).HasType (.sort true) := by
    apply Profile.HasType.pi_iff.mpr
    refine ⟨Profile.WF.pi_iff.mpr ⟨domain.formed, ?_⟩, ?_⟩
    · intro k output member
      cases List.mem_singleton.mp member
      exact ⟨typed, Profile.WF.empty⟩
    · intro k output member
      cases List.mem_singleton.mp member
      exact Profile.HasType.empty (Profile.WF.sort true)
  have wrapped : CodeCert env U registry target locals σ (.forallE B C)
      (Profile.pi (B.subst σ) (C.subst σ.lift) d rows) secondValue.typeFootprint := by
    simpa only [List.append_nil] using CodeCert.seed (.pi domain PiGuard.literal bodies) sorted
  obtain ⟨residual⟩ := wrapped.transfer_graded henv hscoped hTarget closed
    (converted.joint.symm target locals σ σ available closed hTarget substitutions fits).1
    secondValue.typeAvailable
  obtain ⟨required, ⟨residualOpen⟩, ⟨cuts⟩⟩ := residual.certificate.factorInst
    (.forallE E R) a 0 rfl σ rfl locals (Locals.push locals)
  simp only [Subst.liftN, one_comp] at residualOpen
  obtain ⟨packed⟩ := cuts.arguments available residual.available (n + 1)
  obtain ⟨firstValue⟩ := (first.2 target locals σ σ available closed hTarget substitutions fits).1
    packed.observation packed.argumentAvailable
  have firstDomain := firstValue.requestedCertificate
  have firstRelated := firstValue.requestedRelated henv hTarget
  let needs := required.localNeeds ++ required.localNeeds.flatMap Need.singletons
  let localAvailable := Valuation.push needs available
  have localFits := fits.pushCertificates henv hTarget firstDomain firstDomain
    firstValue.typeAvailable firstValue.typeAvailable firstValue.requestedTyped firstValue.requestedTyped
    firstRelated firstRelated needs
    (fun need hm => (packed.pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => (packed.pack.atomized_localNeeds need hm).2 atom ha)
  obtain ⟨uD, rawD, jointD⟩ := header.domain.1
  obtain ⟨uE, rawE, jointE⟩ := header.codomain.2.domain.1
  obtain ⟨uR, rawR, jointR⟩ := header.codomain.2.codomain.1
  have formedD := rawD.defeq.mono hle
  have formedE := rawE.defeq.mono hle
  have formedR := rawR.defeq.mono hle
  have rawFirst := (first.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have paired : Ctx.SubstEq env U target (σ.cons (a.subst σ)) (σ.cons (a.subst σ))
      (D :: source) := .cons substitutions formedD rawFirst
  have localClosed := Valuation.push_atomized_closed closed required.localNeeds
  have localResources := packed.pack.available_atomized_localNeeds packed.outsideAvailable
  have origins := residualOpen.piOrigins henv hscoped hTarget localClosed formedE formedR
    paired localFits jointE jointR localResources
  obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) key Profile.empty (List.mem_singleton_self _)
  obtain ⟨domainPacked, domainOutside, domainPack, domainCovered, domainAvailable⟩ :=
    Footprint.pack_available row.domainAvailable
      (fun need hm => (packed.pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => (packed.pack.atomized_localNeeds need hm).2 atom ha)
  have sourceScope := CtxWF.closed henv substitutions.wf
  have domainScope := formedE.closedN henv ⟨sourceScope, formedD.closedN henv sourceScope⟩
  have outsideScope := domainPack.scoped (row.domain.scoped domainScope)
  have outsideLive := fits.forward.leavesLive henv hscoped hTarget domainAvailable outsideScope
  let argument := GradedResult.exact packed.observation packed.argumentAvailable
    (Related.live henv hscoped hTarget firstRelated)
  obtain ⟨actualDomain⟩ := row.domain.instantiate henv hscoped hTarget closed argument
    domainPack domainCovered domainAvailable outsideLive
  refine ⟨{
    before := residual.footprint
    beforeAvailable := residual.available
    required := required
    cuts := cuts
    firstInput := packed
    support := row.domainSupport
    footprint := actualDomain.footprint
    certificate := actualDomain.certificate
    resources := actualDomain.resources
    typed := row.inputTyped
    alignment := ?_
    admitted := ?_ }⟩
  · simpa only [inst_eq, subst_subst, one_comp] using row.alignment
  · simpa only [inst_eq, subst_subst, one_comp] using row.alignment.admission henv guard.anchor

end Lean4Lean.AnchoredSource.Adapted
