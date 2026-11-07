import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypedLambdaCut
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertUnitCarrierConversion

/-! # Unit carrier histories at the lambda terminal

A body history is consumed in its recorded annotation context. Actual domain
equality types the supplied argument there; typed substitution and ordinary
beta computation then return to the target application's original scope.
The frame cases supply this history outright. Ordinary and sorted body children
retain their actual scope and typings; no guarded path is moved across domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every rigid frame tree over a nullary empty family supplies a complete
carrier history, at any stage and for arbitrary raw endpoints. Its ordinary
beta return supplies all future substitutions and independent residuals. -/
theorem RigidSortFrames.unit_history
    (H : RigidSortFrames family Δ C)
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    PiInertCarrierHistory D stage Δ C a b := by
  obtain ⟨ls, RB⟩ := H.beta_return
  obtain ⟨u, Γ, e, hΓ, EΓ, ht, Ee⟩ := H.typing
  exact pi_inert_beta_unit_carrier_history hs hc hi hp hx hf hD
    ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩ RB

/-- A history for the target type body can be consumed in either equal domain
context. The actual argument is retyped at that recorded domain, so no guarded
computation or comparison is transported. Lifted raw endpoints return unchanged
after substitution; ordinary beta supplies the target application carrier. -/
theorem PiInertCarrierHistory.type_body_application
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort w))
    (hd : env.HasType univs (C :: Γ) d (.sort v)) (hy : env.HasType univs Γ y C)
    (H : PiInertCarrierHistory D stage (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) d) (a.liftN 1) (b.liftN 1)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam C d) y)) a b := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.1⟩
  have hdA := hd.defeqDFC henv (IsDefEqCtx.succ .zero HAC.symm)
  have hyA := HAC.symm.defeq hy
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ y)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hyA)
      (erasedSubstAgreement_one hΓA hyA)
  have HI := H.substitute W
  have Hinst : PiInertCarrierHistory D stage (proofEraseCtx Γ)
      (proofErase Γ (d.inst y)) a b := by
    rw [proofErase_instN hΓA hyA Ctx.InstN.zero hdA]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using HI
  have happ := (HasType.lam HAC.hasType.2 hd).app hy
  exact PiInertCarrierHistory.carrier_prefix
    (PiInertEvidence.core hs hc hΓ happ (.beta (proofErase_beta_forward hΓ happ .beta))) Hinst

/-- Applying a type-valued lambda with a unit-framed body gives a complete
unit carrier history for every actual argument, including proof arguments.
No argument comparison, guarded substitution or canonical-Eq premise is used. -/
theorem RigidSortFrames.unit_application_history
    (H : RigidSortFrames family (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d))
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hd : env.HasType univs (C :: Γ) d (.sort v)) (hy : env.HasType univs Γ y C) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam C d) y)) a b := by
  obtain ⟨w, hC⟩ := hy.isType henv hΓ
  exact (H.unit_history hs hc hi hp hx hf hD).type_body_application hs hc hΓ hC hd hy

/-- The remaining lambda body child has actual sort-typed endpoints and the
source frame in its own recorded context. Equal annotations transport only
ordinary typing, erasure identities and frame data, not the stored comparison. -/
theorem InferredLambdaTerminal.typed_frame_or_scoped_body
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort w))
    (hb : env.HasType univs (A :: Γ) b (.sort u))
    (hd : env.HasType univs (C :: Γ) d (.sort v))
    (HF : RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (H : InferredLambdaTerminal Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) b) (proofErase Γ C) (proofErase (C :: Γ) d)) :
    RigidSortFrames c (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d) ∨
      ∃ X, (X = A ∨ X = C) ∧ env.IsDefEq univs Γ X C (.sort w) ∧
        env.HasType univs (X :: Γ) b (.sort u) ∧ env.HasType univs (X :: Γ) d (.sort v) ∧
        RigidSortFrames c (proofEraseCtx (X :: Γ)) (proofErase (X :: Γ) b) ∧
        ComputedJointCompare Step (proofEraseCtx (X :: Γ)) false
          (proofErase (X :: Γ) b) (proofErase (X :: Γ) d) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.1⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.2⟩
  have W : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have W' : IsDefEqCtx env univs Γ (C :: Γ) (A :: Γ) := .succ .zero HAC.symm
  rcases H.typed_frame_or_body hΓ HAC hb hd HF with HT | HL | HR
  · exact .inl HT
  · refine .inr ⟨A, .inl rfl, HAC, hb, hd.defeqDFC henv W', HF, ?_⟩
    rwa [proofErase_defeqCtx hΓC W' hd] at HL
  · have HF' := HF.context (ContextSubstitution.of_defeqCtx hΓ W)
    have EB := proofErase_defeqCtx hΓA W hb
    rw [EB] at HF' HR
    exact .inr ⟨C, .inr rfl, HAC.hasType.2, hb.defeqDFC henv W, hd, HF', HR⟩

/-- Reflexivity and typed eta at a unit-framed lambda terminal supply the
whole target application history at any chosen stage. Otherwise an actual
sort-typed inferred body child remains in its recorded context, ready for a
recursive history result and type_body_application. No new closure law is
assumed and no history is inferred merely from the remaining raw comparison. -/
theorem InferredLambdaTerminal.unit_application_or_body
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort w))
    (hb : env.HasType univs (A :: Γ) b (.sort u))
    (hd : env.HasType univs (C :: Γ) d (.sort v)) (hy : env.HasType univs Γ y C)
    (HF : RigidSortFrames family (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (H : InferredLambdaTerminal Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) b) (proofErase Γ C) (proofErase (C :: Γ) d)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam C d) y)) left right ∨
      ∃ X, (X = A ∨ X = C) ∧ env.IsDefEq univs Γ X C (.sort w) ∧
        env.HasType univs (X :: Γ) b (.sort u) ∧ env.HasType univs (X :: Γ) d (.sort v) ∧
        RigidSortFrames family (proofEraseCtx (X :: Γ)) (proofErase (X :: Γ) b) ∧
        ComputedJointCompare Step (proofEraseCtx (X :: Γ)) false
          (proofErase (X :: Γ) b) (proofErase (X :: Γ) d) := by
  rcases H.typed_frame_or_scoped_body hΓ HAC hb hd HF with HT | HB
  · exact .inl (HT.unit_application_history hs hc hi hp hx hf hD hΓ hd hy)
  · exact .inr HB

end Lean4Lean.VEnv.Strengthening
