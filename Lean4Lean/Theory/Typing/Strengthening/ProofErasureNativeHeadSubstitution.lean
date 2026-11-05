import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeadBeta

/-! # Substitution preserves certified head developments

Native images transport each retained cut certificate, including certificates
whose guards use arbitrary finite structure/function-eta depth. Residuals of existing certified head reductions therefore remain certified.
Newly created cuts still need their own native evidence; this is not coverage
of arbitrary typed images or all redexes exposed by substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private finite_uniform_bound from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageUnion
variable [Params] {D : PureObservation.Definitions}

/-- A finite source context collects a uniform native-image stage from
pointwise union recovery. This applies to every monotone family of primitive
relations, including the full structure/function-eta stages. -/
theorem NativeImageTransport.Images.finite_stage
    {Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (hmono : ∀ {n m Δ a b}, n ≤ m → Stages n Δ a b → Stages m Δ a b)
    (H : NativeImageTransport.Images (fun Δ a b => ∃ n, Stages n Δ a b) Γ Γ₀ τ) :
    ∃ k, NativeImageTransport.Images (Stages k) Γ Γ₀ τ := by
  classical
  let P (i k : Nat) := ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (Stages k) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ)
  have HM : ∀ {i n m}, n ≤ m → P i n → P i m := by
    intro i n m hle H hn
    exact (H hn).mono (fun H => hmono hle H)
  have HB : ∀ i, i < Γ.length → ∃ k, P i k := by
    intro i hi
    by_cases hn : IsProof Γ (.bvar i)
    · exact ⟨0, fun H => (H hn).elim⟩
    · obtain ⟨k, HR⟩ := (H (Lookup.ofLt hi).2 hn).finite_stage (Stages := Stages)
        (fun {n m} hle {Δ a b} H => hmono hle H)
      exact ⟨k, fun _ => HR⟩
  obtain ⟨k, HK⟩ := finite_uniform_bound (P := P) (count := Γ.length) (fun hle H => HM hle H) HB
  exact ⟨k, fun hl hn => HK _ hl.lt hn⟩

/-- Full-union recovery transports through a typed simultaneous substitution
whose retained images recover in the union. The selected output is substituted
exactly; finite bounds are collected from the context and the source certificate. -/
theorem static_structure_union_recovery_subst_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : NativeImageTransport.Images (ErasedStaticStructureEtaExpansionUnion D) Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  obtain ⟨k, HI⟩ := HI.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m Δ a b} hle H => erased_static_structure_eta_expansion_stage_mono hle H)
  obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  have R := StaticStructureEtaNativeSubstitution.recovery heq hs RN W.wf ht rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  rw [← proofErase_subst_with hΓ₀ W ht ES] at R
  exact R.mono (fun H => ⟨n+k, H⟩)

/-- Simultaneous native substitution preserves the entire certified head
development. Every root cut's body typing is substituted under its own binder,
and each retained argument's selected type is transported exactly. -/
theorem NativeHeadBeta.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : NativeImageTransport.Images (ErasedStaticStructureEtaExpansionUnion D) Γ Γ₀ τ)
    (H : NativeHeadBeta D Γ e e') : NativeHeadBeta D Γ₀ (e.subst σ) (e'.subst σ) := by
  induction H with
  | refl => exact .refl
  | constant hb hx =>
    have hb' := hb.subst henv.orderedStrong W hΓ₀
    have hx' := hx.subst henv.orderedStrong W hΓ₀
    simpa only [VExpr.subst, VExpr.lift_subst_lift] using NativeHeadBeta.constant hb' hx'
  | @beta A u b B x hA hb hx HR =>
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hb' := hb.subst henv.orderedStrong (W.lift henv.ordered hA) ⟨hΓ₀, u, hA'⟩
    have hx' := hx.subst henv.orderedStrong W hΓ₀
    have HR' : ¬ IsProof Γ₀ (x.subst σ) →
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
          (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (A.subst σ)) := by
      intro hn
      have hn₀ : ¬ IsProof Γ x := fun hp => hn ((isProof_subst hΓ₀ W hx).2 hp)
      simpa only [proofErase_subst_with hΓ₀ W hA ES] using
        static_structure_union_recovery_subst_native heq hs hΓ₀ W ES HI hx (HR hn₀)
    simpa only [VExpr.subst, VExpr.subst_inst] using NativeHeadBeta.beta hA' hb' hx' HR'
  | app _ ih => exact .app ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One retained native argument suffices to instantiate an entire certified
head development. A proof argument supplies its fresh image vacuously. There
is no prescribed common stage bound for the development and the argument. -/
theorem NativeHeadBeta.inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (H : NativeHeadBeta D (A :: Γ) b b') : NativeHeadBeta D Γ (b.inst x) (b'.inst x) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have R := H.subst heq hs hΓ ((Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx)
    (erasedSubstAgreement_one hΓA hx) (NativeImageTransport.Images.inst_retained hΓ hx HR)
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using R

/-- Developing a certified head path in a beta body's original context and
then contracting the cut agrees with contracting first and developing its
substituted residual. Both resulting head paths retain their native cut
certificates, so every native expansion can subsequently commute past them. -/
theorem NativeHeadBeta.body_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (H : NativeHeadBeta D (A :: Γ) b b') :
    NativeHeadBeta D Γ (b.inst x) (b'.inst x) ∧
      NativeHeadBeta D Γ (.app (.lam A b') x) (b'.inst x) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb' := (beta_eq hΓA hb H.beta_path).hasType.2
  exact ⟨H.inst heq hs hΓ hx HR, .beta hA hb' hx HR⟩

end Lean4Lean.VEnv.Strengthening
