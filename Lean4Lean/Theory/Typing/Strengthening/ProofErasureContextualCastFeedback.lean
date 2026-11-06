import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualCastGuard

/-! # Annotation consumers justify later casts

A type-valued consumer of a certified lambda pair supplies both the next cast's
endpoint certificate and its actual equality proof. The resulting certificate
can be consumed by another annotation or cast constructor, with arbitrary core
tails retained at every stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A type-valued annotation consumer constructs a new cast certificate and
its equality major. The only comparison premise is the smaller recursive domain
certificate. No semantic endpoint equality or externally supplied future check
is assumed, and the payload may be non-proof data. -/
theorem ContextualCastGuard.annotation_cast
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hw : w.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t (.sort w))
    (hx : env.HasType univs Γ x (t.inst (.lam A b)))
    (H : ContextualCastGuard D n false (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    ∃ q, env.HasType univs Γ q
        (eqApp (.succ w) (.sort w) (t.inst (.lam A b)) (t.inst (.lam C b))) ∧
      ContextualCastGuard D (n+1) mode (proofEraseCtx Γ)
        (proofErase Γ (typeCast w (t.inst (.lam A b)) (t.inst (.lam C b)) q x)) (proofErase Γ x) := by
  have HC := H.forward heq hs hl hcon hc hreg hoff hD .refl .refl
  obtain ⟨v, hS⟩ := hA.isType henv hΓ
  have HAC := ((proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hA hC HC).1
    ⟨_, hS⟩).of_l henv hΓ hA
  have HL := IsDefEq.lamDF HAC hb
  have hX : env.HasType univs Γ (t.inst (.lam A b)) (.sort w) :=
    ht.instN henv Ctx.InstN.zero HL.hasType.1
  have hY : env.HasType univs Γ (t.inst (.lam C b)) (.sort w) :=
    ht.instN henv Ctx.InstN.zero HL.hasType.2
  have HA : ContextualCastGuard D n true (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) :=
    .annotation hΓ hA hC hb ht H
  have HXY := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY
    (.carrierChecked (HA.forward heq hs hl hcon hc hreg hoff hD .refl .refl))
  have hq := (IsDefEq.eqApp_r heq (by exact hw) (HasType.sort hw) hX HXY).defeq
    (HasType.eqReflApp heq (by exact hw) (HasType.sort hw) hX)
  exact ⟨_, hq, .cast hw hΓ hX hY hq hx HA⟩

omit [Params] in
/-- Actual environments construct the entire annotation-to-cast feedback step,
including the equality proof, without abstract core or registry assumptions. -/
theorem EnvironmentCore.contextual_annotation_cast {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u w A C b B t x n mode}, env.HasCanonicalEq → w.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t (.sort w) →
      env.HasType U Γ x (t.inst (.lam A b)) →
      ContextualCastGuard definitions n false (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C) →
      ∃ q, env.HasType U Γ q (eqApp (.succ w) (.sort w) (t.inst (.lam A b)) (t.inst (.lam C b))) ∧
        ContextualCastGuard definitions (n+1) mode (proofEraseCtx Γ)
          (proofErase Γ (typeCast w (t.inst (.lam A b)) (t.inst (.lam C b)) q x)) (proofErase Γ x) := by
  letI := henv.params U
  intro Γ u w A C b B t x n mode heq hw hΓ hA hC hb ht hx H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.annotation_cast heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hw hΓ hA hC hb ht hx

end Lean4Lean.VEnv.Strengthening
