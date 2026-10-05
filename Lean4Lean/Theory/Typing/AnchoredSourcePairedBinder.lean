import Lean4Lean.Theory.Typing.AnchoredSourcePairedFits
import Lean4Lean.Theory.Typing.AnchoredSourceAdaptedFundamental

/-! Binder extension for paired source evidence. The second annotation
certificate and its semantic bridge come from the original domain child's
transfer clause at the existing finite demand. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem PairedFits.push
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (closed : available.AtomClosed)
    (originalDomain : AdaptedTransfer env U registry target locals σ τ
      available A A (.sort level))
    (fits : PairedFits env U registry source target locals σ τ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available) := by
  obtain ⟨rightDomain⟩ := domain.transfer_adapted henv hscoped hTarget closed
    originalDomain domainAvailable
  exact fits.pushCertificates henv hTarget domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered

theorem PairedFits.pushDiagonal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    {A x : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (fits : PairedFits env U registry source target locals σ σ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (argument : Related env U registry target x x (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (σ.cons x) (Valuation.push localNeeds available) :=
  .diagonal (fits.forward.push henv hTarget domain domainAvailable typed argument
    localNeeds bounded covered)

end Lean4Lean.AnchoredSource
