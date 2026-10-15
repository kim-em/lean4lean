import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.RecursiveProbeTyping

/-! # A necessary test for paired instantiation with arbitrary output stages

Only stage-zero input certificates are required here. Even this restricted
closure law must cover arbitrary conversions out of function-result recursive
types. The output stage is existential and has no prescribed bound.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The stage-zero special case of finite-stage common paired instantiation.
Both bodies and both arguments share their original types. The output may use
any finite stage. This is an open closure condition, not a smaller front. -/
def ScopedFinitePairedInstantiation
    (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ A b b' B x y}, OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) b' B →
    env.HasType univs Γ x A → env.HasType univs Γ y A →
    ScopedCompare (Stages 0) (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b') →
    ScopedCompare (Stages 0) (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y) →
    ∃ stage, ScopedCompare (Stages stage) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y))

private theorem erase_body (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ RecursiveDomain.selfBody (.forallE A (.sort u))) :
    proofErase Γ RecursiveDomain.selfBody = .app (.bvar 0) (.bvar 0) := by
  have hn := not_isProof_function_to_sort hΓ ht
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  have hv := not_isProof_fn hΓ hf hx hn
  rw [show proofErase Γ RecursiveDomain.selfBody = .app _ _ from if_neg hn,
    show proofErase Γ (.bvar 0) = .bvar 0 from if_neg hv]

/-- Function-result recursive domains expose their arbitrary annotation
conversions through common paired instantiation, even with an unrestricted
finite output stage. The self-application outputs are functions, not proofs. -/
theorem ScopedFinitePairedInstantiation.recursive_function_coverage
    (hinst : ScopedFinitePairedInstantiation Stages)
    (hhead : ∀ stage {Δ a b}, Stages stage Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (RecursiveProbe.result P).lift) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    ∃ stage, ScopedCompare (Stages stage) (proofEraseCtx Γ) true
      (proofErase Γ D) (proofErase Γ D') := by
  have hD := Hrec.hasType.1
  have hD' := HD.hasType.2
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hΓD' : OnCtx (D' :: Γ) (env.IsType univs) := ⟨hΓ, u, hD'⟩
  have hb := RecursiveProbe.body_typed Hrec
  have hb' : env.HasType univs (D' :: Γ) RecursiveDomain.selfBody (RecursiveProbe.result P).lift :=
    hb.defeqDFC henv (.succ .zero HD)
  have Hdiag := IsDefEq.lamDF HD hb
  have hx := Hrec.symm.defeq Hdiag.hasType.1
  have hy := Hrec.symm.defeq Hdiag.hasType.2
  have hl : env.HasType univs Γ (RecursiveDomain.omegaTerm D) (RecursiveProbe.result P) := by
    simpa only [inst_lift, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal] using HasType.app Hdiag.hasType.1 hx
  have hr : env.HasType univs Γ (RecursiveDomain.omegaTerm D') (RecursiveProbe.result P) := by
    simpa only [inst_lift, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal] using HasType.app Hdiag.hasType.2 hy
  have hnl := not_isProof_function_to_sort hΓ hl
  have hnr := not_isProof_function_to_sort hΓ hr
  have hnxl := not_isProof_fn hΓ Hdiag.hasType.1 hx hnl
  have hnxr := not_isProof_fn hΓ Hdiag.hasType.2 hy hnr
  have EX : proofErase Γ (RecursiveDomain.diagonal D) = ProofShape.diagonal (proofErase Γ D) := by
    rw [show proofErase Γ (RecursiveDomain.diagonal D) = .lam _ _ from if_neg hnxl,
      erase_body hΓD hb]
    rfl
  have EY : proofErase Γ (RecursiveDomain.diagonal D') = ProofShape.diagonal (proofErase Γ D') := by
    rw [show proofErase Γ (RecursiveDomain.diagonal D') = .lam _ _ from if_neg hnxr,
      erase_body hΓD' hb']
    rfl
  have HX : ScopedCompare (Stages 0) (proofEraseCtx Γ) true
      (proofErase Γ (RecursiveDomain.diagonal D)) (proofErase Γ (RecursiveDomain.diagonal D')) := by
    rw [EX, EY]
    exact .lamCommon .refl
  obtain ⟨stage, H⟩ := hinst hΓD hb hb hx hy .refl HX
  have Hloop : ScopedCompare (Stages stage) (proofEraseCtx Γ) true
      (proofErase Γ (RecursiveDomain.omegaTerm D)) (proofErase Γ (RecursiveDomain.omegaTerm D')) := by
    simpa [RecursiveDomain.selfBody, RecursiveDomain.omegaTerm, RecursiveDomain.diagonal,
      VExpr.inst, instVar] using H
  rw [show proofErase Γ (RecursiveDomain.omegaTerm D) = .app _ _ from if_neg hnl,
    show proofErase Γ (RecursiveDomain.omegaTerm D') = .app _ _ from if_neg hnr, EX, EY] at Hloop
  exact ⟨stage, Hloop.selfLoop_annotations (hhead stage)⟩

end Lean4Lean.VEnv.Strengthening
