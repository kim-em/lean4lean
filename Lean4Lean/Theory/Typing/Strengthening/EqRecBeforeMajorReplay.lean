import Lean4Lean.Theory.Typing.Strengthening.EqRecReplay

/-! # Source-typed replay before the equality proof major

The canonical recursor telescope supplies the proof domain of a five-argument
prefix. Endpoint conversion then justifies eta opening, full K computation and
closing the recovered domain, at every original type of that prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- The canonical equality recursor before its final proof argument. -/
def eqRecBeforeMajor (v w : VLevel) (α a M m b : VExpr) : VExpr :=
  mkApps (.const ``Eq.rec [v, w]) [α, a, M, m, b]

/-- Source typing of the partial recursor recovers all five supplied arguments
at the canonical telescope, independently of its supplied result type. -/
theorem eqRecBeforeMajor_typings (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (eqRecBeforeMajor v w α a M m b)) :
    v.WF U ∧ w.WF U ∧ env.HasType U Γ α (.sort w) ∧ env.HasType U Γ a α ∧
      env.HasType U Γ M (.forallE α (.forallE (eqApp w α.lift a.lift (.bvar 0)) (.sort v))) ∧
      env.HasType U Γ m (.app (.app M a) (eqReflApp w α a)) ∧ env.HasType U Γ b α := by
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ H
  obtain ⟨ci, hci, hw, _⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.2.1] at hci
  cases Option.some.inj hci
  have hhead := HasType.const (Γ := Γ) heq.2.2.1 hw (by rfl)
  obtain ⟨_, ht, _⟩ := HasType.mkApps_telescope henv hΓ hhead H (by rfl)
  cases ht with | cons hα ht =>
  cases ht with | cons ha ht =>
  cases ht with | cons hM ht =>
  cases ht with | cons hm ht =>
  cases ht with | cons hb ht =>
  cases ht
  refine ⟨hw _ (by simp), hw _ (by simp), ?_⟩
  simpa [canonicalEqRecMotive, canonicalEqRecMinor, instL, VLevel.inst,
    inst, instVar, liftN, inst_liftN_lo, inst_lift, liftN_liftN, eqApp, eqReflApp] using
    And.intro hα (And.intro ha (And.intro hM (And.intro hm hb)))

/-- The literal residual Pi type is available from the five argument typings. -/
theorem eqRecBeforeMajor_typed (heq : env.HasCanonicalEq) (hv : v.WF U) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hM : env.HasType U Γ M (.forallE α (.forallE (eqApp w α.lift a.lift (.bvar 0)) (.sort v))))
    (hm : env.HasType U Γ m (.app (.app M a) (eqReflApp w α a))) (hb : env.HasType U Γ b α) :
    env.HasType U Γ (eqRecBeforeMajor v w α a M m b)
      (.forallE (eqApp w α a b) (.app (.app M.lift b.lift) (.bvar 0))) := by
  have H := (HasType.eqRec4 heq hv hw hα ha hM hm).app hb
  simpa [eqRecBeforeMajor, mkApps, inst, instVar, eqApp, lift, liftN,
    inst_liftN_lo, inst_lift, liftN_liftN] using H

/-- Endpoint conversion unfolds the prefix before the major at every source
type. The lambda annotation comes from the canonical telescope, not a chosen
ambient eta annotation or a strengthened typing judgment. -/
theorem eqRecBeforeMajor_simAt (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hab : env.IsDefEqU U Γ a b) :
    env.SimAt U Γ (eqRecBeforeMajor v w α a M m b) (.lam (eqApp w α a b) m.lift) := by
  intro T ht
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hf := eqRecBeforeMajor_typed heq hv hw hα ha hM hm hb
  have hE := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType U) := ⟨hΓ, _, hE⟩
  have hbody : env.HasType U (eqApp w α a b :: Γ)
      (.app (eqRecBeforeMajor v w α a M m b).lift (.bvar 0))
      (.app (.app M.lift b.lift) (.bvar 0)) := by
    simpa [lift, liftN, inst, instVar, inst_liftN_lo, inst_lift, liftN_liftN, inst_liftN_bvar] using HasType.app (hf.weak henv.ordered) (.bvar .zero)
  have hbody' : env.HasType U (eqApp w α a b :: Γ)
      (eqRecApp v w α.lift a.lift M.lift m.lift b.lift (.bvar 0))
      (.app (.app M.lift b.lift) (.bvar 0)) := by
    simpa [eqRecBeforeMajor, mkApps, eqRecApp, lift, liftN] using hbody
  have HB := eqRecApp_simAt henv heq hΓE (hab.weak henv.ordered) _ hbody'
  have HL := IsDefEq.lamDF hE HB
  have HE := (IsDefEq.eta hf).symm.trans (by
    simpa [eqRecBeforeMajor, mkApps, eqRecApp, lift, liftN] using HL)
  exact (show env.IsDefEqU U Γ _ _ from ⟨_, HE⟩).of_l henv hΓ ht

end Lean4Lean.VEnv.Strengthening
