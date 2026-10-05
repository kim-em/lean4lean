import Lean4Lean.Theory.Typing.AnchoredBoundedBinder
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedLambda

/-! Bounded actual lambda type certificates from the original body child. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

structure LambdaTypeResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst) (available : Valuation)
    (localNeeds : List Need)
    (A B body other : VExpr) (key : Key n) (output : Atom n) (domain : Profile n) where
  resultSupport : Profile n
  bodyFootprint : Footprint
  bodyCertificate : CodeCert env U registry target (Locals.push locals)
    (realization.cons key.anchor) B resultSupport bodyFootprint
  bodyAvailable : bodyFootprint.Available (Valuation.push localNeeds available)
  outputTyped : (Profile.singleton output).HasType resultSupport
  footprint : Footprint
  certificate : CodeCert env U registry target locals realization (.forallE A B)
    (Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, resultSupport)])
    footprint
  available : footprint.Available available
  typed : (Profile.fn key output).HasType
    (Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, resultSupport)])

  bodyBound : bodyCertificate.nativeDepth current ≤ fuel
  certificateBound : certificate.nativeDepth current ≤ fuel

theorem Obs.lambda_typeBounded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {support packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalBody : Joint current fuel env U registry (A :: source) body other B)
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : PairedFits current fuel env U registry source target locals realization realization available)
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (observation : Obs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTypeResult current fuel env U registry target locals realization available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output support) := by
  obtain ⟨raw, _, oldSupport, _, _, _, _, anchor⟩ := guard.anchor
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (realization.cons key.anchor)
      (realization.cons key.anchor) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have localFits := fits.pushCertificates henv hTarget domain domain domainBound domainBound domainAvailable domainAvailable
    guard.inputTyped guard.inputTyped arguments arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  obtain ⟨fullResult⟩ :=
    (originalBody target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons key.anchor) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
      observation observationBound (pack.available_atomized_localNeeds outsideAvailable)
  let result := fullResult.toGradedTransferResult.requested henv hTarget
  obtain ⟨packed, externalFootprint, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available result.typeAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  let rows := PiRows.cons guard result.certificate bodyPack coverage PiRows.nil
  let certificate := domain.piLiteral rows
  refine ⟨⟨result.support, result.typeFootprint, result.certificate,
    result.typeAvailable, result.typed, _, certificate, ?_, ?_, ?_, ?_⟩⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hd | hb
    · exact domainAvailable i need hd
    · exact externalAvailable i need (by simpa using hb)
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) result.typed

  · simpa only [result, GradedTransferResult.requested, GradedTransferResult.requestedCertificate,
      CodeCert.nativeDepth_lower] using fullResult.certificateBound
  · have bounded : result.certificate.nativeDepth current ≤ fuel := by
      simpa only [result, GradedTransferResult.requested, GradedTransferResult.requestedCertificate,
        CodeCert.nativeDepth_lower] using fullResult.certificateBound
    simpa only [certificate, rows, CodeCert.piLiteral, CodeCert.pi, CodeCert.nativeDepth,
      Obs.nativeDepth, PiRows.nativeDepth, Nat.max_zero] using Nat.max_le.mpr ⟨domainBound, bounded⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
