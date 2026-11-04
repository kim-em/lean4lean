import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBackwardContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadout

/-! # Full Pi readout through controlled expansion

Marked observations retain actual lower Pi components and both computation
histories. Certificate descent handles temporary control binders; backward
context transport appends codomain computation at a changed payload domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation
variable [Params] {D : PureObservation.Definitions}

/-- A payload records actual component representatives and computation from
the initial Pi. Its codomain history stays in the initial binder context. -/
def ExpansionPiOrigin (D : PureObservation.Definitions) (Γ : List VExpr)
    (A B : VExpr) (u v : VLevel) (X Y : ProofShape) : Prop :=
  ∃ A' B', env.IsDefEq univs Γ A A' (.sort u) ∧
    env.HasType univs (A' :: Γ) B' (.sort v) ∧
    proofErase Γ A' = X ∧ proofErase (A' :: Γ) B' = Y ∧
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) X ∧
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) Y

/-- An initial typed Pi supplies a payload with reflexive component histories. -/
theorem ExpansionPiOrigin.refl
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v)) :
    ExpansionPiOrigin D Γ A B u v (proofErase Γ A) (proofErase (A :: Γ) B) :=
  ⟨A, B, hA, hB, rfl, rfl, .refl, .refl⟩

/-- Component computation of a marked Pi lowers through every temporary
prefix, then appends both histories. Later codomain paths are pulled back to
the initial domain using its retained computation and actual equality. -/
theorem expansion_piOrigin_componentClosure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    PiOriginComponentClosure (ErasedExpansionUnion D) Γ (ExpansionPiOrigin D Γ A B u v) := by
  intro Γ' n X Y outX outY hΓ' W HP RX RY
  obtain ⟨A₀, B₀, HA₀, hB₀, rfl, rfl, RA₀, RB₀⟩ := HP
  have hA₀ := HA₀.hasType.2
  have hΓA₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₀⟩
  have hΓA₀' : OnCtx (A₀.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀.weakN henv W⟩
  obtain ⟨A₁, HA₁, RA₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_expansion_union_certificate_descent heq hs) hΓ hΓ' W hA₀ rfl RX
  have EΓB : proofEraseCtx (A₀.liftN n :: Γ') =
      (proofErase Γ A₀).liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA₀]
  obtain ⟨B₁, HB₁, RB₁, EB₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_expansion_union_certificate_descent heq hs) hΓA₀ hΓA₀' W.succ hB₀ EΓB RY
  have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A₁ :: Γ) := .succ .zero HA₁
  have hB₁ := HB₁.hasType.2.defeqDFC henv HC
  have EB₁' := proofErase_defeqCtx hΓA₀ HC HB₁.hasType.2
  have RPB := proofErase_expansion_union_compute_backward_context heq hs hΓ HA₀ RA₀ hB₀ RB₁
  have EB₀ := proofErase_defeqCtx hΓA₀ (IsDefEqCtx.succ .zero HA₀.symm) hB₀
  rw [← EB₀, EB₁'] at RPB
  refine ⟨proofErase Γ A₁, proofErase (A₁ :: Γ) B₁,
    ⟨A₁, B₁, HA₀.trans HA₁, hB₁, rfl, rfl, RA₀.trans RA₁, RB₀.trans RPB⟩, EA₁.symm, ?_⟩
  rw [EB₁'] at EB₁
  exact EB₁.symm

/-- Arbitrary compatible expanded computation from a typed Pi retains its
actual lower payload and both original component histories. Applications,
computed constant/identity functions, beta interleavings and changed binders
are all covered by the same marked-observation induction. -/
theorem proofErase_expansion_union_pi_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ X Y, ExpansionPiOrigin D Γ A B u v X Y ∧ ProofShape.BetaRed out (.forallE X Y) := by
  have hPi := HasType.forallE hA hB
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have H : Obs (ExpansionPiOrigin D Γ A B u v) 0 (fun _ _ => False)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ => False) (ExpansionPiOrigin.refl hA hB))
  have HO := proofErase_scoped_compute_piOriginObservation
    (erased_expansion_union_descent heq hs) erased_expansion_union_piOriginObservation
    (expansion_piOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero []) hPi rfl E H
  exact HO.readout

/-- Full PiReadout coverage for every typed Pi and every expanded union path.
Both component paths remain in the original scopes, including the dependent
codomain. No native recovery or image-coverage assumption is required. -/
theorem proofErase_expansion_union_pi_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    PiReadout (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out := by
  obtain ⟨X, Y, ⟨A', B', _, _, _, _, RA, RB⟩, Rβ⟩ :=
    proofErase_expansion_union_pi_origin heq hs hΓ hA hB R
  exact ⟨X, Y, RA, by simpa only [proofEraseCtx] using RB, Rβ⟩

/-- A finite input stage has a finite later component bound. This extracts
only the stages actually used by the retained domain and codomain histories;
the enclosing wrapper computations need not be native recovered outputs. -/
theorem proofErase_expansion_stage_pi_readout_later
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedExpansionStage D stage) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ later, stage ≤ later ∧ PiReadout (ErasedExpansionStage D later) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out := by
  obtain ⟨X, Y, RA, RB, Rβ⟩ := proofErase_expansion_union_pi_readout heq hs hΓ hA hB
    (R.mono (fun H => ⟨stage, H⟩))
  obtain ⟨n, RA⟩ := RA.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨m, RB⟩ := RB.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  refine ⟨max stage (max n m), by omega, X, Y, ?_, ?_, Rβ⟩
  · exact RA.mono (fun H => erased_expansion_stage_mono (by omega) H)
  · exact RB.mono (fun H => erased_expansion_stage_mono (by omega) H)

end Lean4Lean.VEnv.Strengthening
