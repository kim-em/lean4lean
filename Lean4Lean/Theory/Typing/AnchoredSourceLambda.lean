import Lean4Lean.Theory.Typing.AnchoredSourceBinder

/-! The initial source lambda type certificate is constructed from the
ORIGINAL body child at the frozen anchor. This is the source-certificate part
of lambda introduction, not yet its future semantic function behavior.
-/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure LambdaTypeResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst) (available : Valuation)
    (localNeeds : List Need)
    (A B body other : VExpr) (key : Key n) (output : Atom n) (domain : Profile n) where
  resultSupport : Profile n
  bodyFootprint : Footprint
  bodyCertificate : CodeCert env U registry target (Locals.push locals)
    (realization.cons key.anchor) B resultSupport bodyFootprint
  bodyAvailable : bodyFootprint.Available (Valuation.push localNeeds available)
  otherFootprint : Footprint
  otherObservation : Obs env U registry target (Locals.push locals)
    (realization.cons key.anchor) other (.singleton output) otherFootprint
  otherAvailable : otherFootprint.Available (Valuation.push localNeeds available)
  outputTyped : (Profile.singleton output).HasType resultSupport
  anchorRelated : Related env U registry target
    (body.subst (realization.cons key.anchor)) (other.subst (realization.cons key.anchor))
    (B.subst (realization.cons key.anchor)) (.singleton output) resultSupport
  footprint : Footprint
  certificate : CodeCert env U registry target locals realization (.forallE A B)
    (Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, resultSupport)])
    footprint
  available : footprint.Available available
  typed : (Profile.fn key output).HasType
    (Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, resultSupport)])

/-- No target code is turned back into source syntax: the codomain certificate
is the actual result of the original body induction hypothesis. Its footprint
is packed using the same finite local valuation as the input observation. -/
theorem Obs.lambda_type_subset
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {support packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalBody : Joint env U registry (A :: source) body other B)
    (formedA : env.HasType U source A (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : Fits env U registry source target locals realization realization available)
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (observation : Obs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTypeResult env U registry target locals realization available
      bodyFootprint.localNeeds A B body other key output support) := by
  obtain ⟨raw, _, oldSupport, _, _, _, _, anchor⟩ := guard.anchor
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (realization.cons key.anchor)
      (realization.cons key.anchor) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have localFits := fits.push henv hTarget domain domainAvailable guard.inputTyped arguments
    bodyFootprint.localNeeds (fun need hm => (pack.localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.localNeeds need hm).2 atom ha))
  obtain ⟨result⟩ :=
    (originalBody target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons key.anchor) (Valuation.push bodyFootprint.localNeeds available)
      hTarget paired localFits).1 observation (pack.available outsideAvailable)
  obtain ⟨packed, externalFootprint, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available result.typeAvailable
      (fun need hm => (pack.localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.localNeeds need hm).2 atom ha))
  have rows := PiRows.cons guard result.certificate bodyPack coverage PiRows.nil
  have certificate := domain.piLiteral rows
  refine ⟨⟨result.support, result.typeFootprint, result.certificate,
    result.typeAvailable, result.resultFootprint, result.observation, result.resultAvailable,
    result.typed, result.related, _, certificate, ?_, ?_⟩⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hd | hb
    · exact domainAvailable i need hd
    · exact externalAvailable i need (by simpa using hb)
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) result.typed

theorem Obs.lambda_type
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {support : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalBody : Joint env U registry (A :: source) body other B)
    (formedA : env.HasType U source A (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : Fits env U registry source target locals realization realization available)
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (observation : Obs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n key.input bodyFootprint outside)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTypeResult env U registry target locals realization available
      bodyFootprint.localNeeds A B body other key output support) := by
  exact Obs.lambda_type_subset henv originalBody formedA hTarget substitutions fits domain guard observation pack (fun _ h => h) domainAvailable outsideAvailable

end Lean4Lean.AnchoredSource
