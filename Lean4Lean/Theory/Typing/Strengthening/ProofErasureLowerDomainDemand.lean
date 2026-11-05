import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTypeDemand

/-! # Lower lambda domains with dependent control codomains

Only the Pi domain is anchored below the temporary prefix. Its codomain is
arbitrary and may mention every temporary control variable. This is the base
payload for recursive observations of native types in the lambda observer.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.IndexedControlObservation
open ProofShape.PiOriginObservation (FixedTail)
variable [Params] {D : PureObservation.Definitions}

/-- A typed lower domain and its forward computation history, lifted through
the current control prefix. No restriction is imposed on the Pi codomain. -/
def LowerDomainHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (anchor : ProofShape) (n : Nat) (_Δ : List ProofShape) (A _B : ProofShape) : Prop :=
  ∃ A₀ u, env.HasType univs Γ A₀ (.sort u) ∧ (proofErase Γ A₀).liftN n = A ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      anchor (proofErase Γ A₀)

/-- Ordinary substitution changes every temporary codomain dependency while
fixing the lower domain history. No native image recovery is required. -/
theorem lower_domain_history_substitution :
    PayloadSubstitution (LowerDomainHistory D Γ anchor) := by
  intro n m Δ Δ' A B σ _ HT H
  obtain ⟨A₀, u, hA₀, rfl, RA⟩ := H
  exact ⟨A₀, u, hA₀, (HT.payload (proofErase Γ A₀)).symm, RA⟩

/-- Full-union domain computation descends to the original context and
appends to its history. The simultaneously computed codomain is unrestricted. -/
theorem lower_domain_history_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    IndexedPiComponentClosure (ErasedStaticStructureEtaExpansionUnion D) Γ
      (LowerDomainHistory D Γ anchor) := by
  intro Γ' n A B u v X Y hΓ' W _ _ H RA _
  obtain ⟨A₀, w, hA₀, E, R₀⟩ := H
  rw [← E] at RA
  obtain ⟨A₁, HA₁, R₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓ' W hA₀ rfl RA
  exact ⟨A₁, w, HA₁.hasType.2, EA₁, R₀.trans R₁⟩

/-- Recursive native-type observations instantiated with the lower-domain
history. Temporary codomains and higher-order argument demands remain dependent. -/
abbrev LowerDomainDemand (D : PureObservation.Definitions) (Γ : List VExpr)
    (anchor : ProofShape) := NativeTypeDemand (LowerDomainHistory D Γ anchor)

/-- A literal Pi endpoint exposes its exact lower domain, including the
forward history at depth zero or under any temporary control prefix. -/
theorem LowerDomainDemand.domain
    (H : LowerDomainDemand D Γ anchor .pi n Δ (.forallE A B)) :
    ∃ A₀ u, env.HasType univs Γ A₀ (.sort u) ∧ (proofErase Γ A₀).liftN n = A ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        anchor (proofErase Γ A₀) := H.payload_parts

/-- These observations survive arbitrary typed substitution of temporary
controls. Only original variables must remain fixed. -/
theorem LowerDomainDemand.substitute
    (H : LowerDomainDemand D Γ anchor o n Δ T)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ) :
    LowerDomainDemand D Γ anchor o m Δ' (T.subst σ) :=
  H.subst lower_domain_history_substitution W HT

/-- All recursive observations survive computation of their represented
type at full static structure/function-eta depth. No confluence, joining, or
native recovery of substituted controls is assumed. -/
theorem LowerDomainDemand.compute_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : LowerDomainDemand D Γ anchor o n (proofEraseCtx Γ') (proofErase Γ' T))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hT : env.HasType univs Γ' T (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
      (proofErase Γ' T) out) : LowerDomainDemand D Γ anchor o n (proofEraseCtx Γ') out :=
  H.compute heq hs lower_domain_history_substitution
    (lower_domain_history_components heq hs hΓ) hΓ' W hT R

end Lean4Lean.VEnv.Strengthening
