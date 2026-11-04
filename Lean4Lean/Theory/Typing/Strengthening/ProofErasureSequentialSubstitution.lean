import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralFirstStage

/-! # Finite sequences of certified substitutions

Each step is checked in its own intermediate context. Final composite images
need not satisfy the original image predicate: in particular, later steps may
replace heads that were protected by earlier structural-family certificates.
This proves closure of transport, not factorization of arbitrary typed maps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Compose actual typed diagonal substitutions without a recovery assumption. -/
theorem substEq_compose
    (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₁ σ₁ σ₁ Γ)
    (W₂ : Ctx.SubstEq env univs Γ₂ σ₂ σ₂ Γ₁) :
    Ctx.SubstEq env univs Γ₂ (σ₁.comp σ₂) (σ₁.comp σ₂) Γ := by
  apply substEq_of_lookup W₁.wf
  intro i A hl
  simpa only [VExpr.Subst.comp, VExpr.subst_subst] using
    (W₁.lookup hl).hasType.1.subst henv.orderedStrong W₂ hΓ₂

/-- Retained-variable erasure agreement composes through the actual intermediate
typing, including images whose erasures contain proof markers. -/
theorem ErasedSubstAgreement.compose
    (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₁ σ₁ σ₁ Γ)
    (W₂ : Ctx.SubstEq env univs Γ₂ σ₂ σ₂ Γ₁)
    (E₁ : ErasedSubstAgreement Γ Γ₁ σ₁ τ₁)
    (E₂ : ErasedSubstAgreement Γ₁ Γ₂ σ₂ τ₂) :
    ErasedSubstAgreement Γ Γ₂ (σ₁.comp σ₂) (τ₁.comp τ₂) := by
  intro i A hl hn
  exact (proofErase_subst_with hΓ₂ W₂ (W₁.lookup hl).hasType.1 E₂).trans
    (congrArg (·.subst τ₂) (E₁ hl hn))

/-- Context interpretations compose by realizing the second map on the actual
target supplied by the first. No fixed representative of a raw context is needed. -/
theorem ProofShape.ContextSubstitution.compose
    (W₁ : ContextSubstitution Δ Δ₁ τ₁)
    (W₂ : ContextSubstitution Δ₁ Δ₂ τ₂) :
    ContextSubstitution Δ Δ₂ (τ₁.comp τ₂) := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₁, σ₁, hΓ₁, EΓ₁, S₁, E₁⟩ := W₁ hΓ EΓ
  obtain ⟨Γ₂, σ₂, hΓ₂, EΓ₂, S₂, E₂⟩ := W₂ hΓ₁ EΓ₁
  exact ⟨Γ₂, σ₁.comp σ₂, hΓ₂, EΓ₂, substEq_compose hΓ₂ S₁ S₂,
    E₁.compose hΓ₂ S₁ S₂ E₂⟩

/-- Nonempty finite composition of a substitution class. Each leaf has its own
image certificate; there is no image certificate on a composite node. -/
inductive SequentialSubstitution
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop) :
    List ProofShape → List ProofShape → ProofShape.Subst → Prop
  | single : Transport Δ Δ' τ → SequentialSubstitution Transport Δ Δ' τ
  | comp : SequentialSubstitution Transport Δ Δ₁ τ₁ →
      SequentialSubstitution Transport Δ₁ Δ₂ τ₂ →
      SequentialSubstitution Transport Δ Δ₂ (τ₁.comp τ₂)

/-- A finite sequence preserves interpretation of the underlying typed maps. -/
theorem SequentialSubstitution.interpretation
    (G : ComputedZeroGuardSubstitution D Transport)
    (W : SequentialSubstitution Transport Δ Δ' τ) : ContextSubstitution Δ Δ' τ := by
  induction W with
  | single W => exact G.interpret W
  | comp _ _ ih₁ ih₂ => exact ih₁.compose ih₂

/-- A sequence lifts beneath a binder, substituting its annotation at every step. -/
theorem SequentialSubstitution.cons
    (G : ComputedZeroGuardSubstitution D Transport)
    (W : SequentialSubstitution Transport Δ Δ' τ) :
    SequentialSubstitution Transport (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  induction W generalizing A with
  | single W => exact .single (G.cons W)
  | comp _ _ ih₁ ih₂ =>
    simpa only [ProofShape.subst_subst, ProofShape.Subst.comp_lift] using
      SequentialSubstitution.comp (ih₁ (A := A)) (ih₂ (A := A.subst _))

/-- Both complete recursive checking views transport through a finite sequence.
Intermediate terms are realized and typed before the next checking theorem is
applied; no recovery condition is imposed on the final composite images. -/
theorem SequentialSubstitution.check
    (G : ComputedZeroGuardSubstitution D Transport)
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind a b) :
    ComputedJointTransportResult (SequentialSubstitution Transport)
      (ErasedJointStage D 0) Δ kind a b := by
  cases kind with
  | compare mode =>
    intro Γ a₀ b₀ A Δ' τ hΓ ha hb EΓ Ea Eb W
    induction W generalizing Γ a₀ b₀ A a b with
    | single W => exact G.check H hΓ ha hb EΓ Ea Eb W
    | @comp Δ Δ₁ τ₁ Δ₂ τ₂ W₁ W₂ ih₁ ih₂ =>
      have H₁ := ih₁ H hΓ ha hb EΓ Ea Eb
      obtain ⟨Γ₁, σ₁, hΓ₁, EΓ₁, S₁, E₁⟩ := W₁.interpretation G hΓ EΓ
      have ha₁ := ha.subst henv.orderedStrong S₁ hΓ₁
      have hb₁ := hb.subst henv.orderedStrong S₁ hΓ₁
      have Ea₁ := (proofErase_subst_with hΓ₁ S₁ ha E₁).trans (congrArg (·.subst τ₁) Ea)
      have Eb₁ := (proofErase_subst_with hΓ₁ S₁ hb E₁).trans (congrArg (·.subst τ₁) Eb)
      simpa only [ProofShape.subst_subst] using ih₂ H₁ hΓ₁ ha₁ hb₁ EΓ₁ Ea₁ Eb₁
  | carrier α =>
    intro Γ a₀ b₀ A Δ' τ hΓ ha hb EΓ EA Ea Eb W
    induction W generalizing Γ a₀ b₀ A α a b with
    | single W => exact G.check H hΓ ha hb EΓ EA Ea Eb W
    | @comp Δ Δ₁ τ₁ Δ₂ τ₂ W₁ W₂ ih₁ ih₂ =>
      have H₁ := ih₁ α H hΓ ha hb EΓ EA Ea Eb
      obtain ⟨Γ₁, σ₁, hΓ₁, EΓ₁, S₁, E₁⟩ := W₁.interpretation G hΓ EΓ
      have ha₁ := ha.subst henv.orderedStrong S₁ hΓ₁
      have hb₁ := hb.subst henv.orderedStrong S₁ hΓ₁
      obtain ⟨u, hA⟩ := ha.isType henv hΓ
      have EA₁ := (proofErase_subst_with hΓ₁ S₁ hA E₁).trans (congrArg (·.subst τ₁) EA)
      have Ea₁ := (proofErase_subst_with hΓ₁ S₁ ha E₁).trans (congrArg (·.subst τ₁) Ea)
      have Eb₁ := (proofErase_subst_with hΓ₁ S₁ hb E₁).trans (congrArg (·.subst τ₁) Eb)
      simpa only [ProofShape.subst_subst] using ih₂ _ H₁ hΓ₁ ha₁ hb₁ EΓ₁ EA₁ Ea₁ Eb₁

/-- Finite composition preserves all first-stage guard substitution requirements. -/
theorem ComputedZeroGuardSubstitution.sequential
    (G : ComputedZeroGuardSubstitution D Transport) :
    ComputedZeroGuardSubstitution D (SequentialSubstitution Transport) :=
  ⟨(fun W => W.interpretation G), (fun W => W.cons G), (fun H => SequentialSubstitution.check G H)⟩

/-- A whole first-layer computation transports through any finite sequence of
structural image substitutions, with the exact composed output at the same stage. -/
theorem proofErase_computed_joint_one_compute_subst_sequential
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : SequentialSubstitution (StructuralImageSubstitution D) Δ Δ' τ)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (R : ScopedCompute (ErasedComputedJointStage D 1) Δ source out) :
    ScopedCompute (ErasedComputedJointStage D 1) Δ' (source.subst τ) (out.subst τ) :=
  R.transport_firstStage_guard heq hs (ComputedZeroGuardSubstitution.structural hs).sequential
    hΓ ht EΓ Ee W

end Lean4Lean.VEnv.Strengthening
