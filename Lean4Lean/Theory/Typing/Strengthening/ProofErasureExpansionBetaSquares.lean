import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Contracting expansion wrappers after computations in their children

These local beta squares allow arbitrary expanded computations in the body and
argument. Constant wrappers discard the argument by certificate descent. Native
identity wrappers use the original recovery guard to instantiate the computed
body; no native certificate for the computed argument is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n k m : Nat}

/-- A computed argument passes through every occurrence in a typed template,
including dependent annotations, using only exact primitive renaming. -/
theorem proofErase_expansion_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ x) out) :
    ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming (erased_expansion_stage_rename heq hs m)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Body computation followed by argument computation joins at the exact
substituted raw outputs. Only the original argument needs native recovery.
The body's selected intermediate is reified at its actual original type. -/
theorem proofErase_expansion_body_argument_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ScopedTypeRecovery (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionStage D (max (n + k) m)) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  have R₁ := ExpansionNativeSubstitution.compute_inst heq hs hΓA.1 hx HR hb RB
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_expansion_stage_descent heq hs n) hΓA hb rfl rfl RB
  have R₂ := proofErase_expansion_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact (R₁.mono (fun H => erased_expansion_stage_mono (Nat.le_max_left _ _) H)).trans
    (R₂.mono (fun H => erased_expansion_stage_mono (Nat.le_max_right _ _) H))

/-- After arbitrary computation in a constant wrapper's body, removing its
unused binder leaves an exact lower computation. Every resulting raw argument
and annotation can then be discarded by one beta contraction. -/
theorem proofErase_expansion_constant_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute (ErasedExpansionStage D n) (.sort (.succ .zero) :: proofEraseCtx Γ)
      ((proofErase Γ e).liftN 1) outB) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      ∀ X arg, ProofShape.BetaRed (.app (.lam X outB) arg) (proofErase Γ e') := by
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have EΓ : proofEraseCtx (.sort (.succ .zero) :: Γ) = .sort (.succ .zero) :: proofEraseCtx Γ := by
    rw [proofEraseCtx, show proofErase Γ (.sort (.succ .zero)) = .sort _ from
      if_neg (not_isProof_of_sort hΓ hS)]
  obtain ⟨e', HE, RE, EE⟩ := proofErase_scoped_compute_certificate_descend
    (erased_expansion_stage_certificate_descent heq hs n) hΓ hΓS Ctx.LiftN.one ht EΓ RB
  refine ⟨e', HE, RE, ?_⟩
  intro X arg
  rw [← EE]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := X) (b := (proofErase Γ e').liftN 1) (a := arg))

/-- The identity wrapper's original native guard suffices to join beta with
arbitrary body and argument computations. The final annotation is irrelevant,
and native recovery of the final argument is not assumed. -/
theorem proofErase_expansion_identity_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (HR : ScopedTypeRecovery (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedExpansionStage D n) (proofErase Γ A :: proofEraseCtx Γ) (.bvar 0) outB)
    (RX : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionStage D (max (n + k) m)) (proofEraseCtx Γ)
      (proofErase Γ x) (outB.inst outX) ∧
      ∀ X, ProofShape.BetaRed (.app (.lam X outB) outX) (outB.inst outX) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have hn : ¬ IsProof (A :: Γ) (.bvar 0) := by
    intro hp
    exact HR.ne_proof (proofErase_eq_proof.2 ((isProof_subst hΓ W hb).2 hp))
  have EB : proofErase (A :: Γ) (.bvar 0) = .bvar 0 := if_neg hn
  have RC := proofErase_expansion_body_argument_square heq hs hΓA hb hx HR
    (by simpa only [EB, proofEraseCtx] using RB) RX
  refine ⟨?_, fun _ => .beta⟩
  simpa only [VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, VExpr.liftN_zero] using RC

/-- The body/argument square closes over the full expanded union, with
independent finite bounds for the guard and both child computations. -/
theorem proofErase_expansion_union_body_argument_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  obtain ⟨k, HR⟩ := HR.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨n, RB⟩ := RB.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨m, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (proofErase_expansion_body_argument_square heq hs hΓA hb hx HR RB RX).mono
    (fun H => ⟨max (n + k) m, H⟩)

/-- In the union the identity's local beta square needs no preselected common
stage. Its original guard suffices for both finite child computations. -/
theorem proofErase_expansion_union_identity_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (HR : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedExpansionUnion D) (proofErase Γ A :: proofEraseCtx Γ) (.bvar 0) outB)
    (RX : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (outB.inst outX) ∧
      ∀ X, ProofShape.BetaRed (.app (.lam X outB) outX) (outB.inst outX) := by
  obtain ⟨k, HR⟩ := HR.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨n, RB⟩ := RB.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨m, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨R, Hβ⟩ := proofErase_expansion_identity_square heq hs hΓ hx HR RB RX
  exact ⟨R.mono (fun H => ⟨max (n + k) m, H⟩), Hβ⟩

end Lean4Lean.VEnv.Strengthening
