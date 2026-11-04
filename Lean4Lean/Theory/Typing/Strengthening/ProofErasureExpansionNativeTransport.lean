import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredGuardTransport

/-! # Native-image transport with controlled expansion and recovered guards

A source at stage n transports to n+k for images recovered at stage k in the
same expanded system. Singleton guards include recovered-carrier nodes.
-/
namespace Lean4Lean.VEnv.Strengthening.ExpansionNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {k n : Nat}

/-- Exact images in the expanded computation system. -/
abbrev Images (D : PureObservation.Definitions) (k : Nat) :=
  NativeImageTransport.Images (ErasedExpansionStage D k)

/-- An interpreted substitution certified by those exact images. -/
abbrev ImageSubstitution (D : PureObservation.Definitions) (k : Nat) :=
  NativeImageTransport.ImageSubstitution (ErasedExpansionStage D k)

/-- Exact-image primitive substitution with an additive stage bound. Guards
are transported recursively at the preceding source and target stages. -/
theorem primitive_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ n {Γ Δ Δ' τ e T source out}, ErasedExpansionStage D n Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution D k Δ Δ' τ →
      ErasedExpansionStage D (n + k) Δ' (source.subst τ) (out.subst τ) := by
  intro n
  induction n with
  | zero =>
    intro Γ Δ Δ' τ e T source out H hΓ ht EΓ Ee W
    have H' : ErasedExpansionStage D 0 Δ' (source.subst τ) (out.subst τ) := by
      rcases H with (H | H) | H
      · exact .inl (.inl (erased_iota_primitive_subst H))
      · exact .inl (.inr H.subst)
      · exact .inr (H.subst_typed hΓ ht EΓ Ee W.interpretation)
    simpa only [Nat.zero_add] using erased_expansion_stage_mono (Nat.zero_le k) H'

  | succ n ih =>
    have hcompute : ∀ {Γ Δ Δ' τ e T source out},
        ScopedCompute (ErasedExpansionStage D n) Δ source out →
        OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
        proofEraseCtx Γ = Δ → proofErase Γ e = source → ImageSubstitution D k Δ Δ' τ →
        ScopedCompute (ErasedExpansionStage D (n + k)) Δ' (source.subst τ) (out.subst τ) := by
      intro Γ Δ Δ' τ e T source out R hΓ ht EΓ Ee W
      exact R.transport_typed (erased_expansion_stage_descent heq hs n)
        (ImageSubstitution D k) (fun W => NativeImageTransport.ImageSubstitution.cons (erased_expansion_stage_rename heq hs k) W)
        (fun H hΓ ht EΓ Ee W => .base (ih H hΓ ht EΓ Ee W)) hΓ ht EΓ Ee W
    have G : RecoveredGuardSubstitution (ErasedExpansionStage D n)
        (ErasedExpansionStage D (n + k)) (ImageSubstitution D k) :=
      ⟨⟨(fun W => W.interpretation),
        (fun W => NativeImageTransport.ImageSubstitution.cons (erased_expansion_stage_rename heq hs k) W),
        fun H => NativeImageTransport.check_of_compute (erased_expansion_stage_rename heq hs k)
          (erased_expansion_stage_descent heq hs n)
          (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H) hcompute H⟩,
        fun H => NativeImageTransport.recovered_of_compute (erased_expansion_stage_rename heq hs k)
          (erased_expansion_stage_descent heq hs n)
          (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H) hcompute H⟩
    intro Γ Δ Δ' τ e T source out H hΓ ht EΓ Ee W
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have WR : ImageSubstitution D k (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
      rw [EΓ, EΓ₀]
      exact W
    rw [Nat.succ_add]
    rcases H with H | H | H | H
    · exact .inl (ih H hΓ ht EΓ Ee W)
    · refine .inr (.inl ⟨H.1.subst W.interpretation, ?_⟩)
      have HH := proofErase_recovered_singleton_guard_subst_between heq
        (erased_expansion_stage_descent heq hs n)
        (erased_expansion_stage_descent heq hs (n + k)) G hΓ₀ WS ES WR ht
        (by simpa only [EΓ, Ee] using H.2)
      simpa only [EΓ₀, Ee] using HH
    · apply Or.inr; apply Or.inr; apply Or.inl
      have HH := proofErase_computed_prefix_guard_subst_between heq G.toComputedGuardSubstitution hΓ WR ht
        (by simpa only [EΓ, Ee] using H)
      simpa only [EΓ₀, Ee] using HH
    · exact .inr (.inr (.inr (H.subst_typed
        (erased_expansion_stage_rename heq hs k)
        (erased_expansion_stage_descent heq hs n)
        (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H)
        hcompute hΓ ht EΓ Ee W)))


/-- All compatible computations transport with the same additive stage bound,
including transitive intermediate terms and computations below binders. -/
theorem compute (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ErasedExpansionStage D n) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ImageSubstitution D k Δ Δ' τ) :
    ScopedCompute (ErasedExpansionStage D (n + k)) Δ' (source.subst τ) (out.subst τ) :=
  R.transport_typed (erased_expansion_stage_descent heq hs n)
    (ImageSubstitution D k) (fun W => NativeImageTransport.ImageSubstitution.cons (erased_expansion_stage_rename heq hs k) W)
    (fun H hΓ ht EΓ Ee W => .base (primitive_subst heq hs n H hΓ ht EΓ Ee W))
    hΓ ht EΓ Ee W

/-- Exact selected native types survive every finite guarded stage. -/
theorem recovery (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedExpansionStage D n) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ImageSubstitution D k Δ Δ' τ) :
    ScopedTypeRecovery (ErasedExpansionStage D (n + k)) Δ' (source.subst τ) (out.subst τ) :=
  NativeImageTransport.recovery_of_compute (erased_expansion_stage_rename heq hs k) (erased_expansion_stage_descent heq hs n)
    (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H) (fun R => compute heq hs R) R hΓ ht EΓ Ee W

/-- Both complete checking views transport at all finite stages; the image
hypothesis is a native recovery certificate, not a target checking premise. -/
theorem check (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedExpansionStage D n) Δ kind a b) :
    ComputedJointTransportResult (ImageSubstitution D k)
      (ErasedExpansionStage D (n + k)) Δ kind a b :=
  NativeImageTransport.check_of_compute (erased_expansion_stage_rename heq hs k) (erased_expansion_stage_descent heq hs n)
    (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H) (fun R => compute heq hs R) H

/-- The recovered family checker transports both native endpoints and their
common carrier guard through all expanded stages. -/
theorem recovered (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CarrierRecoveredCompare (ErasedExpansionStage D n) Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ImageSubstitution D k Δ Δ' τ) :
    CarrierRecoveredCompare (ErasedExpansionStage D (n + k)) Δ' mode (sa.subst τ) (sb.subst τ) :=
  NativeImageTransport.recovered_of_compute (erased_expansion_stage_rename heq hs k)
    (erased_expansion_stage_descent heq hs n)
    (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H)
    (fun R => compute heq hs R) H hΓ ha hb EΓ Ea Eb W

end Lean4Lean.VEnv.Strengthening.ExpansionNativeSubstitution
