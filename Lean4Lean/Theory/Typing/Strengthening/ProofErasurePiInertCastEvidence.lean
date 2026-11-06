import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaEvidence

/-! # Derived interpreted comparisons feed subsequent casts

Cast consumers use interpreted child evidence directly, so a comparison
constructed by the eta rule can justify the next recursive cast. The retained
interpretation includes every future typed substitution and full-core residual.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Interpreted common comparison of the two types supplies the guard for an
arbitrary typed cast consumer. Its output retains an ordinary core tail and
uses only the next Pi-inert stage. -/
theorem PiInertInterpret.castConsumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (H : PiInertInterpret D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ X) (proofErase Γ Y)) :
    PiInertInterpret D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  refine ⟨⟨Γ, _, _, hΓ, rfl, ht.instN henv Ctx.InstN.zero hx, rfl⟩, ?_⟩
  intro left RL
  exact pi_inert_cast_consumer_core_commute heq hs hl hcon hc hreg hoff hD
    hu hΓ hX hY hq hx ht (fun RA RB => (H RA RB).mono (fun R => pi_inert_stage_embed R)) RL .refl

/-- Cast consumers preserve interpreted evidence through every future typed
substitution, including when the child came from a derived eta comparison. -/
theorem PiInertEvidence.castConsumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ X) (proofErase Γ Y)) :
    PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  refine ⟨PiInertInterpret.castConsumer heq hs hl hcon hc hreg hoff hD hu hΓ hX hY hq hx ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have HXY := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY
    (.carrierChecked ((H.base .refl .refl).mono (fun R => pi_inert_stage_embed R)))
  have hcast : env.HasType univs Γ (typeCast u X Y q x) X :=
    HXY.symm.defeq (IsDefEq.typeCast_refl henv heq hu hΓ HXY hq hx).hasType.1
  have hleft := ht.instN henv Ctx.InstN.zero hcast
  have hright := ht.instN henv Ctx.InstN.zero hx
  have hX' := hX.subst henv.orderedStrong WS hΓ₀
  have hY' := hY.subst henv.orderedStrong WS hΓ₀
  have hq' := hq.subst henv.orderedStrong WS hΓ₀
  have hx' := hx.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hX) ⟨hΓ₀, u, hX'⟩
  have H' : PiInertInterpret D n (.compare true) Δ'
      ((proofErase Γ X).subst τ) ((proofErase Γ Y).subst τ) := H.future W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hX ES,
    ← proofErase_subst_with hΓ₀ WS hY ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, VExpr.typeCast_subst]
  exact PiInertInterpret.castConsumer heq hs hl hcon hc hreg hoff hD hu hΓ₀ hX' hY' (by simpa only [VExpr.eqApp_subst, VExpr.subst] using hq')
    hx' ht' H'

/-- A retained interpreted type comparison constructs its canonical equality
major and then an arbitrary cast consumer. Thus derived comparisons can be
reused recursively without translating them back into the older grammar. -/
theorem PiInertEvidence.type_cast
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ X) (proofErase Γ Y)) :
    ∃ q, env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y) ∧
      PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  have HXY := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY
    (.carrierChecked ((H.base .refl .refl).mono (fun R => pi_inert_stage_embed R)))
  have hq := (IsDefEq.eqApp_r heq (by exact hu) (HasType.sort hu) hX HXY).defeq
    (HasType.eqReflApp heq (by exact hu) (HasType.sort hu) hX)
  exact ⟨_, hq, H.castConsumer heq hs hl hcon hc hreg hoff hD hu hΓ hX hY hq hx ht⟩

/-- Whole-Pi evidence drives eta inside a type-valued consumer, constructs the
resulting equality major, and justifies a subsequent cast inside any typed
consumer. The complete result retains future substitutions and core residuals
at stage n+1. Coverage for arbitrary strong derivations is not assumed. -/
theorem PiInertEvidence.eta_cast
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hw : w.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (ht : env.HasType univs (.forallE A B :: Γ) t (.sort w))
    (hx : env.HasType univs Γ x (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))))
    (hk : env.HasType univs (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0))) :: Γ) k K)
    (H : PiInertEvidence D n (.compare comparisonMode) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    ∃ q, env.HasType univs Γ q (eqApp (.succ w) (.sort w)
        (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))) (t.inst (.lam C b))) ∧
      PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
        (proofErase Γ (k.inst (typeCast w
          (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))) (t.inst (.lam C b)) q x)))
        (proofErase Γ (k.inst x)) := by
  have hX : env.HasType univs Γ
      (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))) (.sort w) :=
    ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  have hY : env.HasType univs Γ (t.inst (.lam C b)) (.sort w) :=
    ht.instN henv Ctx.InstN.zero hf
  have HE : PiInertEvidence D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.lam C b))) :=
    H.etaConsumer heq hs hc hΓ hA hB hC hE hf hn ht
  exact HE.type_cast heq hs hl hcon hc hreg hoff hD hw hΓ hX hY hx hk

end Lean4Lean.VEnv.Strengthening
