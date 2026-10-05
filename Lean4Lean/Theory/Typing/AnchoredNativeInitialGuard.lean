import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree
import Lean4Lean.Theory.Typing.AnchoredCodeTransitivity

/-! The initial dependent field bridge comes from the ORIGINAL variable
argument typing of the constructor result. It is interpreted in the FULL
original equation/constructor context. No strengthening removes the current
field, and no reconstruction from an arbitrary proof major is asserted.

The earlier-stage hypothesis interprets raw Strong proofs in a PREDECESSOR
environment into the fixed final target relation. Its use below is limited to
the retained bvar formation and defeq children of the supplied typing tree. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure InitialNativeAlignment (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (declared natural : VExpr) (support : Profile n) where
  footprint : Footprint
  naturalCertificate : CodeCert env U registry target locals σ natural support footprint
  resources : footprint.Available available
  path : TypeConversion env U target (natural.subst σ) (declared.subst σ)
  related : TypeRelated env U registry target (natural.subst σ) (declared.subst σ) support

/-- Retain the actual source-variable conversion chain, including conversions
which depend on its inhabitance. `fits` is for the original full constructor
context: it is NOT obtained by assuming that the copied occurrence index is
already a value at the reconstructed field type.

The declared certificate is an actual proper descendant demand. Its support
is preserved exactly through every original conversion child. -/
theorem HasTypeStrong.initialNativeAlignment
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {expression natural : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression natural structural)
    {index : Nat} {declared : VExpr} (isVariable : expression = .bvar index)
    (lookup : Lookup source index declared)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ declared support footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeAlignment env U registry target locals σ available
      declared natural support) := by
  induction original generalizing index declared footprint with
  | bvar found hu formation _ =>
    cases isVariable
    cases found.uniq lookup
    obtain ⟨result⟩ := certificate.transfer_graded henv hscoped hTarget closed
      (earlier formation.refl target locals σ σ available closed hTarget substitutions fits).1 resources
    exact ⟨⟨result.footprint, result.certificate, result.available, .refl, result.related⟩⟩
  | base _ ih => exact ih isVariable lookup substitutions fits certificate resources
  | defeq hu conversion _ _ _ _ _ ih =>
    obtain ⟨previous⟩ := ih isVariable lookup substitutions fits certificate resources
    obtain ⟨next⟩ := previous.naturalCertificate.transfer_graded henv hscoped hTarget closed
      (earlier conversion target locals σ σ available closed hTarget substitutions fits).1
      previous.resources
    have raw := (conversion.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
    exact ⟨{
      footprint := next.footprint
      naturalCertificate := next.certificate
      resources := next.available
      path := (TypeConversion.single raw).symm.trans previous.path
      related := TypeRelated.trans henv (next.related.symm henv certificate.formed.wf_value)
        previous.related }⟩
  | _ => cases isVariable

/-- The demanded field is supported at its DECLARED lookup type by an
existing original-context fitting entry. The constructor's original index
argument typing transports that same demand to the natural index domain.
This is the initial bridge producer, not an assumption about the later
occurrence's arbitrary major proof. -/
theorem HasTypeStrong.initialNativeField
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {index : Nat} {declared natural : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (.bvar index) natural structural)
    (lookup : Lookup source index declared)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {input : Profile n} (needed : (⟨n, input⟩ : Need) ∈ available index) :
    ∃ support, input.HasType support ∧
      Nonempty (InitialNativeAlignment env U registry target locals σ available
        declared natural support) ∧
      Related env U registry target (σ index) (σ index) (natural.subst σ) input support := by
  obtain ⟨entry⟩ := fits.forward.entry index ⟨n, input⟩ needed declared lookup
  obtain ⟨alignment⟩ := HasTypeStrong.initialNativeAlignment henv hscoped hle earlier original
    rfl lookup closed hTarget substitutions fits entry.certificate entry.available
  refine ⟨entry.support, entry.typed, ⟨alignment⟩, ?_⟩
  exact Related.convert henv entry.typed
    (alignment.related.symm henv entry.typed.wf_type) entry.related

end Lean4Lean.AnchoredSource.Adapted
