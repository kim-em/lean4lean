import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryPrimitiveSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaLocalSquare

/-! # One-step squares at historically certified beta cuts

After any number of interleaved component rounds, every single-step competitor
still joins the original contractum. Current native recovery is unnecessary:
component steps extend the histories, and primitive roots use the native pivot.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every one-step competitor at a historical cut joins the original
contractum. This includes primitives requiring a native guard that the current
contractum no longer recovers. The theorem retains the original argument's
certificate, not an exact certificate at every intermediate cut. -/
theorem CutComponentHistory.step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.redex out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  change ScopedStep _ _ (.app (.lam s.1 s.2.1) s.2.2) out at R
  cases R with
  | primitive RP =>
    obtain ⟨shared, RL, RR⟩ := H.primitive_square heq hs hΓ hn HR RP
    exact ⟨shared, RL, .beta RR⟩
  | beta => exact ⟨_, (H.contract heq hs hΓ HR).1, .refl⟩
  | appL RF =>
    cases RF with
    | primitive RP =>
      have RL := (H.contract heq hs hΓ HR).1
      obtain ⟨⟨C, HAC, EC, _⟩, ⟨d, Hbd, Ed, _⟩, ⟨y, Hxy, Ey, _⟩⟩ := H
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
      have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
      have hdC := Hbd.hasType.2.defeqDFC henv HC
      have EdC : proofErase (C :: Γ) d = s.2.1 :=
        (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
      have HE := IsDefEq.appDF (IsDefEq.lamDF HAC Hbd) Hxy
      have hnr : ¬ IsProof Γ (.app (.lam C d) y) := fun hp => hn ((isProof_congr hΓ HE).2 hp)
      have hnf := not_isProof_fn hΓ (HasType.lam HAC.hasType.2 hdC) (HAC.defeq Hxy.hasType.2) hnr
      have EF : proofErase Γ (.lam C d) = .lam s.1 s.2.1 := by
        rw [show proofErase Γ (.lam C d) = .lam _ _ from if_neg hnf, EC, EdC]
      have RR := literal_lambda_primitive_application_beta heq hs hΓ HAC.hasType.2 hdC hnf (EF ▸ RP) s.2.2
      rw [EdC] at RR
      exact ⟨_, RL, .beta RR⟩
    | lamDomain RA =>
      rename_i C'
      have HH : CutComponentHistory D Γ A b x u B (C', s.2.1, s.2.2) :=
        H.advance heq hs hΓ ⟨RA.compute, .refl, .refl⟩
      exact ⟨_, (HH.contract heq hs hΓ HR).1, .beta .beta⟩
    | lamBody RB =>
      rename_i d'
      have HH : CutComponentHistory D Γ A b x u B (s.1, d', s.2.2) :=
        H.advance heq hs hΓ ⟨.refl, RB.compute, .refl⟩
      exact ⟨_, (HH.contract heq hs hΓ HR).1, .beta .beta⟩
  | appR RX =>
    rename_i y'
    have HH : CutComponentHistory D Γ A b x u B (s.1, s.2.1, y') :=
      H.advance heq hs hΓ ⟨.refl, .refl, RX.compute⟩
    exact ⟨_, (HH.contract heq hs hΓ HR).1, .beta .beta⟩

/-- A finite component development followed by any one-occurrence step joins
contraction of the initial native cut. The competing path can have arbitrarily
many changing binders and arguments before its final step. Root expansions that
are followed by further unrestricted computation still require a larger history
invariant; they are not silently included in the component-round premise. -/
theorem native_cut_development_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RC : ReflTransGen (CutComponentRound D (proofEraseCtx Γ))
      (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) s)
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.redex out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared :=
  ((CutComponentHistory.refl hA hb hx).rounds heq hs hΓ RC).step_square heq hs hΓ hn HR R

end Lean4Lean.VEnv.Strengthening
