import Lean4Lean.Theory.Typing.Strengthening.LambdaObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionObservations

/-! # Lambda exposure through arbitrary controlled expansions

Whole-function computation can turn a lambda into an application of expansion
wrappers. A finite lambda demand survives every expanded stage and reads a
lambda back by beta, with no assumption that its body normalizes. This does
not retain the original domain/body computation histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open LambdaObservation
namespace ProofShape

/-- Lambda-head finite observations of the exact encoded proof shape. -/
def LambdaHeadObservation (S : PureObservation.Sets) (a : ProofShape) (o : PureObservation.Ob) : Prop :=
  Obs S a.toObservationExpr o

/-- Constant/projection-headed primitives cannot destroy a lambda demand. -/
theorem LambdaHeadObservation.not_primitiveHead (H : LambdaHeadObservation S a o) : ¬ PrimitiveHead a := by
  induction a generalizing S o with
  | const | proj => exact H.neutralHead.elim
  | app f x ihf _ =>
    obtain ⟨keys, hf, _⟩ := Obs.app_inv H
    exact ihf hf
  | proof | bvar | sort | lam | forallE => exact fun h => h

/-- A finite lambda demand reflects to an exact raw beta path with both
annotation and body retained in the resulting raw lambda. -/
theorem LambdaHeadObservation.lambda_exposure
    (H : LambdaHeadObservation (fun _ _ => False) a .pi) :
    ∃ A b, ProofShape.BetaRed a (.lam A b) := by
  obtain ⟨X, y, R⟩ := Obs.lambda_exposure H
  obtain ⟨out, RB, E⟩ := beta_of_toObservationExpr R
  obtain ⟨A, b, rfl, _, _⟩ := toObservationExpr_lam_inv E
  exact ⟨A, b, RB⟩

/-- Compatible computation preserves lambda demands whenever its primitive
roots do. No well-formedness or interpretation of the raw context is required. -/
theorem ScopedCompute.lambdaHeadObservation
    (hstep : ∀ {Δ a b S o}, Step Δ a b → LambdaHeadObservation S a o → LambdaHeadObservation S b o)
    (R : ScopedCompute Step Δ a b) (H : LambdaHeadObservation S a o) : LambdaHeadObservation S b o := by
  induction R generalizing S o with
  | base R => exact hstep R H
  | beta R => exact Obs.beta_compute_forward R.toObservationExpr H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := Obs.app_inv H
    exact Obs.app (ihf hf) (fun key hk => iha (ha key hk))
  | proj | forallE => exact H.neutralHead.elim
  | lam _ _ _ ihb =>
    rcases Obs.lam_inv H with rfl | ⟨keys, result, hb, hle⟩
    · exact Obs.head
    · exact Obs.sub (Obs.lam (ihb hb)) hle
end ProofShape

open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]
/-- Root expansions preserve the existing lambda demand directly. All other
primitive roots are opaque to this observation relation. -/
theorem erased_expansion_stage_lambdaHeadObservation : ∀ stage {Δ a b S o},
    ErasedExpansionStage D stage Δ a b → LambdaHeadObservation S a o → LambdaHeadObservation S b o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R <;> exact H.neutralHead.elim
    · cases R with
      | intro _ =>
        simpa only [LambdaHeadObservation, constantExpansion, toObservationExpr,
          toObservationExpr_liftN, VExpr.lift] using H.constant_expansion
  | succ stage ih =>
    intro Δ a b S o R H
    rcases R with R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R with
      | intro _ => exact H.identity_expansion

/-- Every union primitive has some finite stage preserving the demand. -/
theorem erased_expansion_union_lambdaHeadObservation
    (R : ErasedExpansionUnion D Δ a b) (H : LambdaHeadObservation S a o) : LambdaHeadObservation S b o := by
  obtain ⟨stage, R⟩ := R
  exact erased_expansion_stage_lambdaHeadObservation stage R H

/-- A lambda survives every finite expanded computation as a beta-exposable
lambda. The entire function can compute, including expansion at its root.
Its original annotation and body are completely unrestricted raw syntax. -/
theorem expansion_stage_lambda_persistence
    (R : ScopedCompute (ErasedExpansionStage D stage) Δ (.lam A b) out) :
    ∃ X y, ProofShape.BetaRed out (.lam X y) := by
  have H : LambdaHeadObservation (fun _ _ => False) (.lam A b) .pi := Obs.head
  exact (R.lambdaHeadObservation (erased_expansion_stage_lambdaHeadObservation stage) H).lambda_exposure

/-- Arbitrarily many finite guard stages still preserve lambda exposure. -/
theorem expansion_union_lambda_persistence
    (R : ScopedCompute (ErasedExpansionUnion D) Δ (.lam A b) out) :
    ∃ X y, ProofShape.BetaRed out (.lam X y) := by
  have H : LambdaHeadObservation (fun _ _ => False) (.lam A b) .pi := Obs.head
  exact (R.lambdaHeadObservation erased_expansion_union_lambdaHeadObservation H).lambda_exposure

/-- A computed function exposes a single body usable at every raw argument.
Neither argument typing nor recovery is needed to perform this beta step.
The body's relation to the original body is a separate origin obligation. -/
theorem expansion_union_computed_lambda_application
    (RF : ScopedCompute (ErasedExpansionUnion D) Δ (.lam A b) outF) :
    ∃ X y, ProofShape.BetaRed outF (.lam X y) ∧
      ∀ arg, ProofShape.BetaRed (.app outF arg) (y.inst arg) := by
  obtain ⟨X, y, R⟩ := expansion_union_lambda_persistence RF
  exact ⟨X, y, R, fun _ => (ProofShape.BetaRed.app R .refl).trans .beta⟩

/-- Independent argument computation can precede the exposed beta contraction.
The exact substituted body is a residual of the original application, with
no native image requirement and no increase in either primitive stage. -/
theorem expansion_computed_lambda_argument_square
    (RF : ScopedCompute (ErasedExpansionStage D n) Δ (.lam A b) outF)
    (RX : ScopedCompute (ErasedExpansionStage D m) Δ x outX) :
    ∃ X y, ProofShape.BetaRed outF (.lam X y) ∧
      ProofShape.BetaRed (.app outF outX) (y.inst outX) ∧
      ScopedCompute (ErasedExpansionStage D (max n m)) Δ
        (.app (.lam A b) x) (y.inst outX) := by
  obtain ⟨X, y, R, HB⟩ := expansion_union_computed_lambda_application
    (RF.mono (fun H => ⟨n, H⟩))
  exact ⟨X, y, R, HB outX,
    (ScopedCompute.app
      (RF.mono (fun H => erased_expansion_stage_mono (Nat.le_max_left _ _) H))
      (RX.mono (fun H => erased_expansion_stage_mono (Nat.le_max_right _ _) H))).trans
      (.beta (HB outX))⟩

/-- At a typed retained source the exposed raw lambda has an actual lambda
representative at the original type. Its exact beta path and computation stage
are retained; this does not infer component computation from actual equality. -/
theorem proofErase_expansion_lambda_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ (.lam A b) T)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) outF) :
    ∃ X y, env.IsDefEq univs Γ (.lam A b) (.lam X y) T ∧
      ProofShape.BetaRed outF (.lam (proofErase Γ X) (proofErase (X :: Γ) y)) ∧
      ScopedCompute (ErasedExpansionStage D stage) (proofEraseCtx Γ)
        (proofErase Γ (.lam A b)) (.lam (proofErase Γ X) (proofErase (X :: Γ) y)) := by
  have EE : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg hn
  obtain ⟨X, y, Rβ⟩ := expansion_stage_lambda_persistence (EE ▸ RF)
  have RC := RF.trans (.beta Rβ)
  obtain ⟨f', HF, EF⟩ := proofErase_scoped_compute_realize
    (erased_expansion_stage_descent heq hs stage) hΓ hf rfl rfl RC
  obtain ⟨X', y', rfl, _, EX, EY⟩ := erase_lam_inv EF
  rw [← EX, ← EY] at Rβ RC
  exact ⟨X', y', HF, Rβ, RC⟩

end Lean4Lean.VEnv.Strengthening
