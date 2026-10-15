import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedEtaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionImages

/-! # Two-sided eta residuals for contextual computation

Typed confluence of the same computational relation suffices to transport a
joined-body eta certificate through independent computation of both endpoints.
The computed lambda annotation changes the raw body context; its replay supplies
the context conversion needed to reindex the residual certificate.

This is conditional on typed computational confluence. In particular, it does
not establish confluence of the general singleton stages or transport arbitrary
recursive comparisons, and it never replaces a preceding-stage guard by a
later-stage certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The exact typed-source confluence obligation for a contextual computation.
For the general singleton stages this remains to be proved; operational replay
alone does not provide the forward paths required by this obligation. -/
def ErasedScopedTypedConfluent
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ e T a b}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) a →
    ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) b →
    ∃ out, ProofShape.ScopedCompute Step (proofEraseCtx Γ) a out ∧
      ProofShape.ScopedCompute Step (proofEraseCtx Γ) b out

/-- A literal common-reduct guard survives independent computation at the same
relation. Replay realizes the old common reduct before the final confluence
application; no common original type for the two starting endpoints is needed. -/
theorem ErasedScopedTypedConfluent.join_forward
    (hcon : ErasedScopedTypedConfluent Step) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (HA : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) shared)
    (HB : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) shared)
    (RA : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) b') :
    ∃ out, ProofShape.ScopedCompute Step (proofEraseCtx Γ) a' out ∧
      ProofShape.ScopedCompute Step (proofEraseCtx Γ) b' out := by
  obtain ⟨left, HL, HS⟩ := hcon hΓ ha RA HA
  obtain ⟨right, HR, HT⟩ := hcon hΓ hb RB HB
  obtain ⟨s, Hs, Es⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) ha rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using HA)
  simp only [List.length_nil, ProofShape.liftN_zero] at Es
  obtain ⟨out, RL, RR⟩ := hcon hΓ Hs.hasType.2 (Es.symm ▸ HS) (Es.symm ▸ HT)
  exact ⟨out, HL.trans RL, HR.trans RR⟩

/-- A joined-body eta guard survives independent contextual computation of its
lambda and short function, including changes to the lambda annotation. All
paths and the output comparison use exactly the supplied relation `Step`. -/
theorem proofErase_scoped_eta_join_forward
    (hcon : ErasedScopedTypedConfluent Step) (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → ProofShape.PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b C)
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (HB : ProofShape.ScopedCompute Step (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) shared)
    (HF : ProofShape.ScopedCompute Step (proofEraseCtx (A :: Γ))
      (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u)) shared)
    (RL : ProofShape.ScopedCompute Step (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) left)
    (RF : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) right) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨A', body', rfl, RA, RB⟩ := RL.lam_inv_typed hstep hsubst hroot hΓ hA rfl
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  have RS : ProofShape.ScopedCompute Step (proofEraseCtx (A :: Γ))
      (.app ((proofErase Γ f).liftN 1) (ProofShape.etaArgument u))
      (.app (right.liftN 1) (ProofShape.etaArgument u)) :=
    .app (RF.shift hsubst hΓ hA) .refl
  obtain ⟨out, HL, HR⟩ := hcon.join_forward hstep hΓA hb hopen HB
    (E.symm ▸ HF) RB (E.symm ▸ RS)
  obtain ⟨A₁, HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hA rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using RA)
  simp only [List.length_nil, ProofShape.liftN_zero] at EA
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (A₁ :: Γ) := .succ .zero HA
  have HG : ProofShape.ScopedCompare Step (proofEraseCtx (A :: Γ)) true body'
      (.app (right.liftN 1) (ProofShape.etaArgument u)) := .compute HL HR .refl
  apply ProofShape.ScopedCompare.etaBodyL (EA ▸ ProofShape.DomainSort.of_typed hΓ HA.hasType.2)
  simpa only [proofEraseCtx, EA] using HG.defeqCtx hsubst hΓ HC

/-- A displayed eta pair at a common original type retains a scoped comparison
after independent computations. Typed classification chooses the fresh proof
marker or retained variable; no untyped eta-transport claim is made. -/
theorem proofErase_scoped_eta_head_forward
    (hcon : ErasedScopedTypedConfluent Step) (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → ProofShape.PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f))
    (RE : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) left)
    (RF : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) right) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨A, B, u, hA, hfPi, hn, E⟩ := proofErase_eta_head_classified hΓ he hf H
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hfPi).hasType.1.lam_inv henv hΓ
  have EB := proofErase_eta_body hΓ hA hfPi hn
  exact proofErase_scoped_eta_join_forward hcon hstep hsubst hroot hΓ hA hopen hfPi hn
    .refl (EB ▸ ProofShape.ScopedCompute.refl) (EB.symm ▸ E ▸ RE) RF

/-- Arbitrary computations preceding a displayed eta guard also admit two-sided
residuals. The two eta endpoints are realized by replay, while confluence aligns
their competing paths. This covers computation followed by head eta, not every
recursive scoped comparison constructor. -/
theorem proofErase_scoped_computed_eta_forward
    (hcon : ErasedScopedTypedConfluent Step) (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → ProofShape.PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (HE : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) etaLeft)
    (HF : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) etaRight)
    (H : ProofShape.EtaHead etaLeft etaRight)
    (RE : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) left)
    (RF : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) right) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true left right := by
  obtain ⟨left', RL, EL⟩ := hcon hΓ he RE HE
  obtain ⟨right', RR, ER⟩ := hcon hΓ hf RF HF
  obtain ⟨e₀, He, Ee⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) he rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using HE)
  obtain ⟨f₀, Hf, Ef⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hf rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using HF)
  simp only [List.length_nil, ProofShape.liftN_zero] at Ee Ef
  exact .compute RL RR (proofErase_scoped_eta_head_forward hcon hstep hsubst hroot hΓ
    He.hasType.2 Hf.hasType.2 (Ee.symm ▸ Ef.symm ▸ H) (Ee.symm ▸ EL) (Ef.symm ▸ ER))

end Lean4Lean.VEnv.Strengthening
