import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambda
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGrades
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaGrades

/-! Semantic lambda consumers project a graded child result to their fixed
requested grade. They never recurse on its newly returned raw observation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure RequestedResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) (demand : Profile n) where
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals leftSubst sourceType support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : demand.HasType support
  related : Related env U registry target (left.subst leftSubst) (right.subst rightSubst)
    (sourceType.subst leftSubst) demand support

noncomputable def GradedTransferResult.requested
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (result : GradedTransferResult env U registry target locals σ τ available left right sourceType demand) :
    RequestedResult env U registry target locals σ τ available left right sourceType demand :=
  ⟨_, result.typeFootprint, result.requestedCertificate, result.typeAvailable,
    result.requestedTyped, result.requestedRelated henv hTarget⟩

theorem Obs.graded_lambda_type
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {support packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalBody : GradedJoint env U registry (A :: source) body other B)
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : PairedFits env U registry source target locals realization realization available)
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (observation : Obs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTypeResult env U registry target locals realization available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output support) := by
  obtain ⟨raw, _, oldSupport, _, _, _, _, anchor⟩ := guard.anchor
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (realization.cons key.anchor)
      (realization.cons key.anchor) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have localFits := fits.pushDiagonal henv hTarget domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  obtain ⟨fullResult⟩ :=
    (originalBody target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons key.anchor) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
      observation (pack.available_atomized_localNeeds outsideAvailable)
  let result := fullResult.requested henv hTarget
  obtain ⟨packed, externalFootprint, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available result.typeAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have rows := PiRows.cons guard result.certificate bodyPack coverage PiRows.nil
  have certificate := domain.piLiteral rows
  refine ⟨⟨result.support, result.typeFootprint, result.certificate,
    result.typeAvailable, result.typed, _, certificate, ?_, ?_⟩⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hd | hb
    · exact domainAvailable i need hd
    · exact externalAvailable i need (by simpa using hb)
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) result.typed

end Lean4Lean.AnchoredSource.Adapted
