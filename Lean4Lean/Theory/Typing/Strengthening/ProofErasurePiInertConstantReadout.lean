import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertIdentityReadout

/-! # Consume the body child of a framed function comparison

Stage-zero function paths lift through actual application. At a typed lambda
cut, the target application's own typing supplies its argument at the recovered
domain. A completed body history can then be consumed in its recorded context
and returned to the original application. The remaining comparison child is
retained explicitly; this file does not assert its history or strict smallness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A raw stage-zero function path survives actual application at any requested
evidence stage. The assigned Pi may be dependent and either application may
erase to proof; no source-head condition or hereditary input is required. -/
theorem pi_inert_zero_application_evidence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)) :
    PiInertEvidence D stage .compute (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  have ht := HasType.app (HasType.bvar (env := env) (U := univs)
    (Lookup.zero (ty := .forallE A B) (Γ := Γ))) (hx.weak henv (B := .forallE A B))
  have H := pi_inert_zero_consumer_evidence (stage := stage) heq hs hc hΓ hf hg ht R
  simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using H

/-- A complete body history in either equal annotation context supplies the
original function application's history. Only the raw function prefix must
have stage zero; the body history retains its own arbitrary finite stage. -/
theorem PiInertCarrierHistory.zero_function_body_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (HXC : env.IsDefEq univs Γ X C (.sort w))
    (hf : env.HasType univs Γ f (.forallE C (.sort u)))
    (hd : env.HasType univs (C :: Γ) d (.sort u)) (hy : env.HasType univs Γ y C)
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (.lam C d)))
    (H : PiInertCarrierHistory D stage (proofEraseCtx (X :: Γ))
      (proofErase (X :: Γ) d) (left.liftN 1) (right.liftN 1)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app f y)) left right :=
  PiInertCarrierHistory.carrier_prefix
    (pi_inert_zero_application_evidence heq hs hc hΓ hf (.lam HXC.hasType.2 hd) hy R)
    (H.type_body_application hs hc hΓ HXC hd hy)

/-- A framed function comparison at stage zero either finishes the original
target application or returns its actual inferred body child with a proved
history-consumption continuation. Ordinary/sorted children retain their own
recorded scope. No history is assumed for that child, and this cut alone does
not supply the well-founded comparison induction needed to construct it. -/
theorem pi_inert_zero_constant_application_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) F)
    (happ : env.HasType univs Γ (.app g y) T)
    (HB : RigidSortFrames family (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ g)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app g y)) left right ∨
      ∃ X e d w u, env.HasType univs Γ X (.sort w) ∧
        env.HasType univs (X :: Γ) e (.sort u) ∧ env.HasType univs (X :: Γ) d (.sort u) ∧
        RigidSortFrames family (proofEraseCtx (X :: Γ)) (proofErase (X :: Γ) e) ∧
        ComputedJointCompare (PiInertStage D 0) (proofEraseCtx (X :: Γ)) false
          (proofErase (X :: Γ) e) (proofErase (X :: Γ) d) ∧
        (PiInertCarrierHistory D stage (proofEraseCtx (X :: Γ))
          (proofErase (X :: Γ) d) (left.liftN 1) (right.liftN 1) →
          PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app g y)) left right) := by
  obtain ⟨Y, E, hg, hy⟩ := happ.app_inv henv hΓ
  obtain ⟨A', b', C, d, w, u, _, Hg, HAC, hb, hd, _, RG, HF, HT⟩ :=
    pi_inert_typed_lambda_frame_cut heq hs (henv.projectionRigid hi) hD hΓ hf hg HB H
  have htarget := HasType.lam HAC.hasType.2 hd
  have hgPi := (Hg.toU.of_r henv hΓ htarget).hasType.1
  have hyC := argument_at_displayed_domain hΓ hg hgPi hy
  rcases HT with HFtarget | HL | HR
  · exact .inl (pi_inert_zero_unit_application_history heq hs hc hi hp hx hfields hD
      hΓ hg hd hyC RG HFtarget)
  · have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.2⟩
    have W : IsDefEqCtx env univs Γ (C :: Γ) (A' :: Γ) := .succ .zero HAC.symm
    have hdA := hd.defeqDFC henv W
    rw [proofErase_defeqCtx hΓC W hd] at HL
    refine .inr ⟨A', b', d, w, u, HAC.hasType.1, hb, hdA, HF, HL, ?_⟩
    intro HK
    exact HK.zero_function_body_application heq hs hc hΓ HAC hgPi hd hyC RG
  · have hΓA : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.1⟩
    have W : IsDefEqCtx env univs Γ (A' :: Γ) (C :: Γ) := .succ .zero HAC
    have hbC := hb.defeqDFC henv W
    have Ebody := proofErase_defeqCtx hΓA W hb
    have HFC := HF.context (ContextSubstitution.of_defeqCtx hΓ W)
    rw [Ebody] at HFC HR
    refine .inr ⟨C, b', d, w, u, HAC.hasType.2, hbC, hd, HFC, HR, ?_⟩
    intro HK
    exact HK.zero_function_body_application heq hs hc hΓ HAC.hasType.2 hgPi hd hyC RG

end Lean4Lean.VEnv.Strengthening
