import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextOracleBeta

/-! # Future family certificates beneath changing binders

Beta reduction of a displayed domain changes the body's comparison context.
An interpreted identity moves the retained body certificate to that context,
including after substitutions that create new domain or body redexes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params]

private theorem context_identity : ContextSubstitution Δ Δ ProofShape.Subst.id := by
  intro Γ hΓ EΓ
  cases EΓ
  exact (ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ))) hΓ rfl

private theorem lambda_future
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true) (A :: Δ) b b')
    (R : ProofShape.BetaRed (.lam A b) left)
    (S : ProofShape.BetaRed (.lam A' b') right) : JointCompare Step Δ true left right := by
  obtain ⟨D, body, rfl, RD, RB⟩ := R.lam_inv
  obtain ⟨D', body', rfl, _, RB'⟩ := S.lam_inv
  have HC := ((H.beta RB RB').subst (context_identity.cons_beta RD)).base
  simp only [ProofShape.subst_id] at HC
  exact .lamCommon HC

/-- Future common body comparisons give future common lambda comparisons.
The displayed domains may differ; their own beta reductions are accounted for
by moving the body certificate into the left residual domain's context. -/
theorem BetaStableFamily.lam_common
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true) (A :: Δ) b b') :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ (.lam A b) (.lam A' b') := by
  refine ⟨fun R S => lambda_future H R S, ?_⟩
  intro Δ' τ p q W R S
  exact lambda_future (H.subst W.cons) R S

private theorem forall_future
    (SA : DomainSort Δ A u) (SA' : DomainSort Δ A' u)
    (SB : DomainSort (A :: Δ) B v) (SB' : DomainSort (A :: Δ) B' v)
    (HA : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ A A')
    (HB : BetaStableFamily (fun Δ => JointCompare Step Δ true) (A :: Δ) B B')
    (R : ProofShape.BetaRed (.forallE A B) left)
    (S : ProofShape.BetaRed (.forallE A' B') right) : JointCompare Step Δ true left right := by
  obtain ⟨D, body, rfl, RD, RB⟩ := beta_forallE_parts R
  obtain ⟨D', body', rfl, RD', RB'⟩ := beta_forallE_parts S
  have W : ContextSubstitution (A :: Δ) (D :: Δ) ProofShape.Subst.id :=
    context_identity.cons_beta RD
  have HC := ((HB.beta RB RB').subst W).base
  have SD := W.sort (SB.beta RB)
  have SD' := W.sort (SB'.beta RB')
  simp only [ProofShape.subst_id] at HC SD SD'
  exact .forallSorted (SA.beta RD) (SA'.beta RD') (HA.1 RD RD') SD SD' HC

/-- Future domain/body certificates and their actual sort witnesses combine
under dependent Pi. Both endpoints may beta-reduce independently, including
inside their domains, before and after arbitrary interpreted substitution. -/
theorem BetaStableFamily.forall_sorted
    (SA : DomainSort Δ A u) (SA' : DomainSort Δ A' u)
    (SB : DomainSort (A :: Δ) B v) (SB' : DomainSort (A :: Δ) B' v)
    (HA : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ A A')
    (HB : BetaStableFamily (fun Δ => JointCompare Step Δ true) (A :: Δ) B B') :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ (.forallE A B) (.forallE A' B') := by
  refine ⟨fun R S => forall_future SA SA' SB SB' HA HB R S, ?_⟩
  intro Δ' τ p q W R S
  exact forall_future (W.sort SA) (W.sort SA') (ContextSubstitution.sort W.cons SB) (ContextSubstitution.sort W.cons SB')
    (HA.subst W) (HB.subst W.cons) R S

end Lean4Lean.VEnv.Strengthening
