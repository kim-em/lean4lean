import Lean4Lean.Theory.Typing.AnchoredSourceLambdaIntroduction

/-! The original domain and body children reconstruct a right-hand lambda
with its actual consumed input. The old advertised input remains covered,
and its original annotation certificate/guard is retained explicitly. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem typed_subset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom hm => typed atom (subset atom hm)
  | succ n => exact ⟨fun atom hm => typed.1 atom (subset atom hm), typed.2.1,
      fun atom hm => typed.2.2 atom (subset atom hm)⟩

private theorem admitted_subset {key : Key n} {input : Profile n}
    (subset : ∀ atom ∈ input.atoms, atom ∈ key.input.atoms)
    (h : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (inputKey key input) x y := by
  obtain ⟨raw, pair, support, typed, formed, code, first, second⟩ := h
  exact ⟨raw, pair, support, typed_subset subset typed, formed, code,
    Related.of_singletons (fun atom hm => Related.singleton_of_mem first (subset atom hm)),
    Related.of_singletons (fun atom hm => Related.singleton_of_mem second (subset atom hm))⟩

structure LambdaTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst) (available : Valuation)
    (A' other : VExpr) (key : Key n) (output : Atom n) (domainSupport : Profile n) where
  input : Profile n
  covered : ∀ atom ∈ input.atoms, atom ∈ key.input.atoms
  domainFootprint : Footprint
  domain : CodeCert env U registry target locals realization A' domainSupport domainFootprint
  domainAvailable : domainFootprint.Available available
  annotationGuard : LambdaGuard env U registry target realization A' key domainSupport
  bodyFootprint : Footprint
  outside : Footprint
  body : Obs env U registry target (Locals.push locals) (realization.cons key.anchor)
    other (.singleton output) bodyFootprint
  pack : BinderPack n input bodyFootprint outside
  outsideAvailable : outside.Available available
  observation : Obs env U registry target locals realization (.lam A' other)
    (Profile.fn (inputKey key input) output) (domainFootprint ++ outside)

theorem Obs.lambda_transfer_smaller
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalDomain : Joint env U registry source A A' (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : Fits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n key.input bodyFootprint outside)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTransferResult env U registry target locals right available
      A' other key output domainSupport) := by
  have domainChild := originalDomain target locals left right available hTarget substitutions fits
  obtain ⟨newDomain⟩ := domain.transfer henv hscoped hTarget domainChild.1 domainAvailable
  have rawDomains := domains.substDF henv substitutions.wf hTarget substitutions
  have newGuard : LambdaGuard env U registry target right A' key domainSupport := {
    inputTyped := guard.inputTyped
    formed := guard.formed
    path := guard.path.trans (.single rawDomains)
    domains := guard.domains.trans henv newDomain.related
    anchor := guard.anchor }
  obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := guard.anchor
  have arguments := Related.convert henv guard.inputTyped guard.domains anchor
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons key.anchor) (A :: source) :=
    .cons substitutions domains.hasType.1 (guard.path.cast raw)
  have localFits := fits.push henv hTarget domain domainAvailable guard.inputTyped arguments
    bodyFootprint.localNeeds (fun need hm => (pack.localNeeds need hm).1)
    (fun need hm => (pack.localNeeds need hm).2)
  obtain ⟨transferred⟩ :=
    (originalBody target (Locals.push locals) (left.cons key.anchor)
      (right.cons key.anchor) (Valuation.push bodyFootprint.localNeeds available)
      hTarget paired localFits).1 observation (pack.available outsideAvailable)
  obtain ⟨input, external, packed, covered, externalAvailable⟩ :=
    Footprint.pack_available transferred.resultAvailable
      (fun need hm => (pack.localNeeds need hm).1)
      (fun need hm => (pack.localNeeds need hm).2)
  have smallerGuard : LambdaGuard env U registry target right A' (inputKey key input)
      domainSupport := {
    inputTyped := typed_subset covered newGuard.inputTyped
    formed := newGuard.formed
    path := newGuard.path
    domains := newGuard.domains
    anchor := admitted_subset covered newGuard.anchor }
  exact ⟨⟨input, covered, newDomain.footprint, newDomain.certificate, newDomain.available,
    newGuard, transferred.resultFootprint, external, transferred.observation, packed,
    externalAvailable, Obs.lam newDomain.certificate smallerGuard transferred.observation packed⟩⟩

/-- Original lambda children produce the smaller-input right observation and
the semantic relation at the original input simultaneously. Restoring the
original source demand is intentionally not asserted here. -/
theorem Obs.lambda_children
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalDomain : Joint env U registry source A A' (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : Fits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n key.input bodyFootprint outside)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (LambdaTransferResult env U registry target locals right available
      A' other key output domainSupport) ∧
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals left (.forallE A B) support footprint) ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  exact ⟨Obs.lambda_transfer_smaller henv hscoped originalDomain originalBody domains
      hTarget substitutions fits domain guard observation pack domainAvailable outsideAvailable,
    Obs.lambda_interpret henv hscoped originalBody originalCodomain domains codomain
      leftBody rightBody hTarget substitutions fits domain guard observation pack
      domainAvailable outsideAvailable⟩

end Lean4Lean.AnchoredSource
