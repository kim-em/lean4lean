import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDemandProfileTyping

/-! # Expansion frames with dependent and ignored control domains -/
namespace Lean4Lean.VEnv.Strengthening.DemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Native Pi selection retains both profile components at the selected
actual domain. The guard's type may differ syntactically from the old witness. -/
theorem Typing.native_pi (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e (.arrow p q))
    (RN : ScopedTypeRecovery Step Δ e (.forallE D C)) :
    ∃ Γ f A B, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
      env.HasType univs Γ f (.forallE A B) ∧ Fits Γ A p ∧ Fits (A :: Γ) B q ∧
      proofErase Γ f = e ∧ proofErase Γ A = D ∧ proofErase (A :: Γ) B = C := by
  obtain ⟨Γ, f, T, hΓ, rfl, hf, HP, rfl⟩ := H
  obtain ⟨A, B, hfAB, EA, EB⟩ := proofErase_scoped_recovered_pi_descend
    hstep hΓ hΓ (Ctx.LiftN.zero []) hf
    (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
  simp only [List.length_nil, ProofShape.liftN_zero] at EA EB
  obtain ⟨HA, HB⟩ := (HP.convert hΓ (hf.uniqU henv hΓ hfAB)).forallE_inv hΓ
  exact ⟨Γ, f, A, B, hΓ, rfl, hfAB, HA, HB, rfl, EA, EB⟩

/-- An observed argument profile forces a positive domain universe, even
when the selected eta annotation depends on the ambient context. -/
theorem Typing.eta_domain_ne_zero (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e (.arrow p q)) (HV : p.Visible)
    (RN : ScopedTypeRecovery Step Δ e (.forallE D C)) (S : DomainSort Δ D u) : ¬ u ≈ .zero := by
  obtain ⟨Γ, f, A, B, hΓ, rfl, hf, HA, HB, Ef, EA, EB⟩ := H.native_pi hstep RN
  obtain ⟨v, hA, hv⟩ := HA.positive hΓ HV
  have S' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) u := by
    simpa only [ProofShape.liftN_zero, EA] using S
  have hAu := S'.descend hΓ hΓ (Ctx.LiftN.zero []) hA
  have E := (hA.uniqU henv hΓ hAu).sort_inv henv hΓ
  intro E0
  exact hv [] ((congrFun E []).trans (congrFun E0 []))

/-- Eta supplies its body profile without any shape assumption on an ignored
argument. When that argument is demanded, its syntax is the retained fresh
variable and it carries the demanded domain profile. -/
theorem Typing.eta_parts (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e (.arrow p q)) (R : NativeEtaExpansion Step Δ e out) :
    ∃ D u, out = .lam D (.app (e.liftN 1) (etaArgument u)) ∧
      Typing Δ out (.arrow p q) ∧
      Typing (D :: Δ) (.app (e.liftN 1) (etaArgument u)) q ∧ DomainSort Δ D u ∧
      (p.Visible → etaArgument u = .bvar 0 ∧ Typing (D :: Δ) (.bvar 0) p) := by
  have HT := H.compute (erased_nativeEtaExpansion_descent hstep) (.base R)
  cases R with
  | intro RN S =>
    obtain ⟨HB, HX⟩ := HT.lam_parts
    exact ⟨_, _, rfl, HT, HB, S, fun HV =>
      ⟨if_neg (H.eta_domain_ne_zero hstep HV RN S), HX HV⟩⟩

/-- A constant wrapper has a universe domain and the same dependent result
profile. Its body is weakened in the actual context. -/
theorem Typing.constant_frame (H : Typing Δ e p) (HV : p.Visible) :
    Typing Δ (.lam (.sort (.succ .zero)) (e.liftN 1)) (.arrow .sort p) ∧
      DomainSort Δ (.sort (.succ .zero)) (.succ (.succ .zero)) := by
  obtain ⟨Γ, f, T, hΓ, rfl, hf, HP, rfl⟩ := H
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓ hS)
  have hF := HasType.lam hS (hf.weakN henv Ctx.LiftN.one)
  have HPS : Fits Γ (.sort (.succ .zero)) .sort := ⟨⟨_, hS⟩, _, hS.toU⟩
  have HPL := HP.weak hΓ hΓS
  obtain ⟨v, hPi⟩ := hF.isType henv hΓ
  have HPF : Fits Γ (.forallE (.sort (.succ .zero)) T.lift) (.arrow .sort p) :=
    ⟨hF.isType henv hΓ, _, _, hPi.toU, HPS, HPL⟩
  refine ⟨⟨Γ, _, _, hΓ, rfl, hF, HPF, ?_⟩, ⟨Γ, _, hΓ, rfl, hS, ES⟩⟩
  rw [show proofErase Γ (.lam _ _) = .lam _ _ from if_neg (HPF.not_isProof hΓ (.arrow HV) hF),
    ES, proofErase_liftN hΓ hΓS Ctx.LiftN.one hf]

/-- Native identity expansion reuses the selected actual type as its domain,
while preserving the source profile on both sides of that domain. -/
theorem Typing.identity_frame (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e p) (HV : p.Visible) (RN : ScopedTypeRecovery Step Δ e D) :
    Typing Δ (.lam D (.bvar 0)) (.arrow p p) := by
  obtain ⟨Γ, f, T, hΓ, rfl, hf, HP, rfl⟩ := H
  obtain ⟨A, hfA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
  obtain ⟨u, hA⟩ := hfA.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HPA := HP.convert hΓ (hf.uniqU henv hΓ hfA)
  have HPL := HPA.weak hΓ hΓA
  have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hF := HasType.lam hA hx
  obtain ⟨v, hPi⟩ := hF.isType henv hΓ
  have HPF : Fits Γ (.forallE A A.lift) (.arrow p p) :=
    ⟨hF.isType henv hΓ, _, _, hPi.toU, HPA, HPL⟩
  refine ⟨Γ, _, _, hΓ, rfl, hF, HPF, ?_⟩
  rw [show proofErase Γ (.lam _ _) = .lam _ _ from if_neg (HPF.not_isProof hΓ (.arrow HV) hF),
    EA, show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg (HPL.not_isProof hΓA HV hx)]

end Lean4Lean.VEnv.Strengthening.DemandProfile
