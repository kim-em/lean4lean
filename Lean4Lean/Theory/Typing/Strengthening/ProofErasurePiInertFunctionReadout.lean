import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSelectorHistory

/-! # What hereditary function-body readout would have to prove

Retained fresh-body histories already suffice for shared application by actual
typed substitution. A universal extraction law for completed function histories
is explicitly left open; its unit-selector consequence is examined separately.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- Actual binder insertion preserves complete histories, including the assigned
type. This follows from future substitution and erasure under weakening. -/
theorem PiInertCarrierHistory.weakN
    (H : PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count k Γ Γ') (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ') (proofErase Γ' (C.liftN count k))
      (proofErase Γ' (a.liftN count k)) (proofErase Γ' (b.liftN count k)) := by
  rw [proofErase_liftN hΓ hΓ' W hC, proofErase_liftN hΓ hΓ' W ha,
    proofErase_liftN hΓ hΓ' W hb]
  simpa only [subst_bvar_liftN] using H.substitute (ContextRenaming.of_liftN hΓ hΓ' W).interpretation

/-- Endpoint core residuals retain the whole carrier history and every future
substitution. This permits an application output to be consumed after beta. -/
theorem PiInertCarrierHistory.endpoint_reducts
    (H : PiInertCarrierHistory D n Δ C a b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertCarrierHistory D n Δ C a' b' := by
  refine ⟨fun RC RL RR => H.base RC (RA.trans RL) (RB.trans RR), ?_⟩
  intro Δ' τ W C' left right RC RL RR
  exact H.future W RC ((RA.subst (fun R => erased_level_core_subst R)).trans RL)
    ((RB.subst (fun R => erased_level_core_subst R)).trans RR)

/-- Actual shared-argument instantiation of the fresh-body history. No joined
argument grammar, native image recovery, or canonical-Eq assumption is needed. -/
theorem PiInertCarrierHistory.apply_same_argument
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : PiInertCarrierHistory D n (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
      (proofErase (A :: Γ) (.app g.lift (.bvar 0)))) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  have test {f} (hf : env.HasType univs Γ f (.forallE A B)) :
      env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (hf.weak henv) (.bvar .zero)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨v, hB⟩ := (test hf).isType henv hΓA
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hx)
      (erasedSubstAgreement_one hΓA hx)
  have HI := H.substitute W
  have HE := proofErase_instN hΓA hx Ctx.InstN.zero (test hf)
  have HE' := proofErase_instN hΓA hx Ctx.InstN.zero (test hg)
  simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] at HE HE'
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hB, HE, HE']
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using HI

/-- Missing extraction law: a completed assigned-Pi carrier history must yield
a history for fresh applications under that Pi's domain. Arbitrary later stages
are allowed. This is not established by outer future substitution or by the
proved constructor taking a body history to a function history. -/
def FinitePiInertFunctionBodyReadout (D : Definitions) : Prop :=
  ∀ {n Γ A B f g u}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ f (.forallE A B) → env.HasType univs Γ g (.forallE A B) →
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ f) (proofErase Γ g) →
    ∃ m, PiInertCarrierHistory D m (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
      (proofErase (A :: Γ) (.app g.lift (.bvar 0)))

/-- Missing shared-argument application closure for completed histories.
Neither a prescribed output stage nor differing arguments are requested. -/
def FinitePiInertSharedApplication (D : Definitions) : Prop :=
  ∀ {n Γ A B f g x}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ f (.forallE A B) → env.HasType univs Γ g (.forallE A B) →
    env.HasType univs Γ x A →
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ f) (proofErase Γ g) →
    ∃ m, PiInertCarrierHistory D m (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x))

/-- A proof of hereditary fresh-body extraction would finish shared application
by the already checked substitution rule. This implication does not discharge
the extraction premise or assert that it is smaller than PropositionFront. -/
theorem FinitePiInertFunctionBodyReadout.shared_application
    (H : FinitePiInertFunctionBodyReadout D) : FinitePiInertSharedApplication D := by
  intro n Γ A B f g x hΓ hf hg hx HF
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  obtain ⟨m, HB⟩ := H hΓ hA hf hg HF
  exact ⟨m, HB.apply_same_argument hΓ hA hf hg hx⟩

/-- Conversely, shared application after actual binder insertion extracts the
fresh-body history. Thus this is exactly the same missing closure law, even
with arbitrary finite output stages, rather than a weaker replacement. -/
theorem FinitePiInertSharedApplication.function_body_readout
    (H : FinitePiInertSharedApplication D) : FinitePiInertFunctionBodyReadout D := by
  intro n Γ A B f g u hΓ hA hf hg HF
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  have HW := HF.weakN hΓ hΓA Ctx.LiftN.one hPi hf hg
  have hf' := hf.weak henv (B := A)
  have hg' := hg.weak henv (B := A)
  obtain ⟨m, HB⟩ := H hΓA hf' hg' (HasType.bvar .zero) HW
  exact ⟨m, by simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using HB⟩

/-- Hereditary body extraction and shared-argument closure are equivalent;
neither implication assumes strengthening or comparison completeness. -/
theorem finite_pi_inert_function_body_readout_iff_shared_application :
    FinitePiInertFunctionBodyReadout D ↔ FinitePiInertSharedApplication D :=
  ⟨FinitePiInertFunctionBodyReadout.shared_application,
    FinitePiInertSharedApplication.function_body_readout⟩

end Lean4Lean.VEnv.Strengthening
