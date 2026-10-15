import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop

/-! # What paired instantiation must know about recursive types

Common checking of diagonal functions hides arbitrary domain conversion. Paired
instantiation into self-application reveals that conversion again. Consequently,
paired instantiation must cover every conversion out of a recursive domain,
even when its computation changes the diagonal annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem erase_self_body (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ RecursiveDomain.selfBody (.sort .zero)) :
    proofErase Γ RecursiveDomain.selfBody = .app (.bvar 0) (.bvar 0) := by
  have hn := not_isProof_of_sort hΓ ht
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  have hv := not_isProof_fn hΓ hf hx hn
  rw [show proofErase Γ RecursiveDomain.selfBody = .app _ _ from if_neg hn,
    show proofErase Γ (.bvar 0) = .bvar 0 from if_neg hv]

private theorem erase_diagonal (hΓ : OnCtx Γ (env.IsType univs))
    (hD : env.HasType univs Γ D (.sort u))
    (hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero)) :
    proofErase Γ (RecursiveDomain.diagonal D) = ProofShape.diagonal (proofErase Γ D) := by
  have hn := not_isProof_function_to_sort hΓ (HasType.lam hD hb)
  rw [show proofErase Γ (RecursiveDomain.diagonal D) = .lam _ _ from if_neg hn,
    erase_self_body (Γ := D :: Γ) ⟨hΓ, u, hD⟩ hb]
  rfl

/-- Paired instantiation forces common comparison of every domain convertible
to a recursive type `D ≡ D → Prop`. This is a necessary coverage condition,
not a sufficient strengthening front. Neither domain must be normal or fixed
by the chosen computation relation. -/
theorem ScopedPairedInstantiation.recursive_type_coverage
    (hinst : ScopedPairedInstantiation Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ D) (proofErase Γ D') := by
  have hD := Hrec.hasType.1
  have hD' := HD.hasType.2
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero) := hf.app hv
  have hb' : env.HasType univs (D' :: Γ) RecursiveDomain.selfBody (.sort .zero) :=
    hb.defeqDFC henv (.succ .zero HD)
  have Hdiag := IsDefEq.lamDF HD hb
  have hx := Hrec.symm.defeq Hdiag.hasType.1
  have hy := Hrec.symm.defeq Hdiag.hasType.2
  have EX := erase_diagonal hΓ hD hb
  have EY := erase_diagonal hΓ hD' hb'
  have HX : ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (RecursiveDomain.diagonal D))
      (proofErase Γ (RecursiveDomain.diagonal D')) := by
    rw [EX, EY]
    exact .lamCommon .refl
  have H := hinst hΓD hb hb hx hy .refl HX
  have hl := HasType.app Hdiag.hasType.1 hx
  have hr := HasType.app Hdiag.hasType.2 hy
  have Hloop : ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (RecursiveDomain.omegaTerm D))
      (proofErase Γ (RecursiveDomain.omegaTerm D')) := by
    simpa [RecursiveDomain.selfBody, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal,
      VExpr.inst, instVar] using H
  rw [show proofErase Γ (RecursiveDomain.omegaTerm D) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hl),
    show proofErase Γ (RecursiveDomain.omegaTerm D') = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hr), EX, EY] at Hloop
  exact Hloop.selfLoop_annotations hhead

end Lean4Lean.VEnv.Strengthening
