import Lean4Lean.Theory.Typing.AnchoredConstantPlanBinder

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private telescope_eq from Lean4Lean.Theory.Inductive.NativeCommonPrefix
set_option backward.isDefEq.respectTransparency false

/-- The rank-indexed native plan induction statement. The assigned type is
always the literal remaining registered telescope. -/
def NativePlanSupported (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) (n : Nat) : Prop :=
  ∀ {target arguments newValues demand footprint support available},
    NativePlan env U registry target signature arguments (demand : Profile n) footprint →
    OnCtx target (env.IsType U) → arguments.length ≤ signature.domains.length →
    newValues.length = arguments.length → available.AtomClosed →
    Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse →
    PairedFits env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) available →
    footprint.Available available → demand.HasType support →
    TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments)) support →
    Related env U registry target (mkApps (.const data.name levels) arguments)
      (mkApps (.const data.name levels) newValues)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      demand support

/-- The genuine binder induction step: original registered domain formation
extends the paired valuation, then the strict smaller-rank plan theorem
interprets the actual future child tree. -/
theorem NativePlan.binderSupported
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (typeClosed : signature.type.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (signature.type.instL levels)
      (signature.type.instL levels) (.sort typeLevel))
    (lower : NativePlanSupported env U registry signature n)
    {target : List VExpr} {arguments newValues : List VExpr}
    {domain : VExpr} {key : Key n} {output : Atom n}
    {domainSupport packed : Profile n} {support : Profile (n+1)}
    {domainFootprint bodyFootprint outside : Footprint} {available : Valuation}
    (origin : signature.domains[arguments.length]? = some domain)
    (domainCode : CodeCert env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) domain domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key domainSupport)
    (body : NativePlan env U registry target signature (arguments ++ [key.anchor])
      (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (hTarget : OnCtx target (env.IsType U))
    (newLength : newValues.length = arguments.length)
    (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse)
    (fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst newValues) available)
    (resources : (domainFootprint ++ outside).Available available)
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments)) support) :
    Related env U registry target (mkApps (.const data.name levels) arguments)
      (mkApps (.const data.name levels) newValues)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      (Profile.fn key output) support := by
  let literal : ConstantTelescope (signature.type.instL levels) :=
    ⟨signature.domains, signature.result, telescope_eq signature.telescope⟩
  exact ConstantPlanSupported.binder (signature := literal)
    (Plan := fun target arguments => NativePlan env U registry target signature arguments)
    henv hscoped hle earlier typeClosed.instL typeFormation lower
    origin domainCode guard
    (fun Δ ρ future => by
      simpa only [Profile.rename_singleton] using body.future henv future typeClosed)
    pack covered hTarget newLength closed raw fits resources typed code

end Lean4Lean.AnchoredSource.Adapted
