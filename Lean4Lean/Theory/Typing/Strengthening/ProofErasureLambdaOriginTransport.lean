import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaOriginObservation

/-! # Typed transport of marked lambda origins

Payload lambdas update their component histories. Control lambdas instead pass
finite demands into their bodies. This distinction prevents the body's arbitrary
computations from being confused with the surrounding expansion control frames.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.LambdaOriginObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

variable [Params]
/-- Every expanded primitive preserves the marked payload directly. Opaque
heads and literal sort roots are excluded by the observation derivation. -/
theorem erased_expansion_stage_lambdaOriginObservation : ∀ stage {Δ a b P n S o},
    ErasedExpansionStage D stage Δ a b → Obs P n S a o → Obs P n S b o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b P n S o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b P n S o R H
    rcases R with R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R
      exact H.identity_expansion

/-- Unbounded finite guard depth preserves the same marked lambda observation. -/
theorem erased_expansion_union_lambdaOriginObservation
    (R : ErasedExpansionUnion D Δ a b) (H : Obs P n S a o) : Obs P n S b o := by
  obtain ⟨stage, R⟩ := R
  exact erased_expansion_stage_lambdaOriginObservation stage R H

/-- A payload closure law handles just component computation of a literal lambda
lifted through an arbitrary well-formed prefix. It retains exact raw outputs. -/
def LambdaOriginComponentClosure (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (P : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ' n A B X Y}, OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' → P A B →
    ScopedCompute Step (proofEraseCtx Γ') (A.liftN n) X →
    ScopedCompute Step (A.liftN n :: proofEraseCtx Γ') (B.liftN n 1) Y →
    ∃ A' B', P A' B' ∧ X = A'.liftN n ∧ Y = B'.liftN n 1

/-- Typed computation preserves marked observations whenever literal lambda
components preserve their histories. Control applications, beta contractions,
changing lambda annotations and temporary binders need no further premise. -/
theorem proofErase_scoped_compute_lambdaOriginObservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b n S o}, Step Δ a b → Obs P n S a o → Obs P n S b o)
    (hpi : LambdaOriginComponentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (H : Obs P n S source o) : Obs P n S out o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S o e T with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE (ih₁ hΓ' W ht EΓ Ee H)
  | app RF RX ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    obtain ⟨keys, HF, HX⟩ := H.app_inv
    exact .app (ihf hΓ' W hf EΓ Ef HF) (fun key hk => ihx hΓ' W hx EΓ Ex (HX key hk))
  | proj => exact H.not_proj.elim
  | lam RA RB ihA ihb =>
    rcases H.lam_inv with ⟨rfl, A, b, HP, rfl, rfl⟩ | ⟨keys, result, rfl, HB⟩
    · obtain ⟨A', b', HP', EX, EY⟩ := hpi hΓ' W HP (EΓ ▸ RA) (EΓ ▸ RB)
      rw [EX, EY]
      exact Obs.payload HP'
    · obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      apply Obs.lam
      exact ihb hΓA W' hb (by simp only [proofEraseCtx, EA, EΓ]) Eb HB
  | forallE => exact H.not_forallE.elim

end Lean4Lean.VEnv.Strengthening
