import Lean4Lean.Theory.Typing.Strengthening.ReflexiveCastReplay

/-! # Source-typed K computation for arbitrary canonical Eq motives

The motive may depend on both the endpoint and its equality proof. Typing of
the complete recursor application supplies every canonical telescope premise.
Definitional endpoint equality then replaces the major by reflexivity, allowing
the actual registered iota rule to compute at the source's original type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Invert all six canonical Eq.rec arguments at any typing of the source. -/
theorem eqRecApp_typings (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (eqRecApp v w α a motive minor b proof)) :
    v.WF U ∧ w.WF U ∧ env.HasType U Γ α (.sort w) ∧ env.HasType U Γ a α ∧
      env.HasType U Γ motive
        (.forallE α (.forallE (eqApp w α.lift a.lift (.bvar 0)) (.sort v))) ∧
      env.HasType U Γ minor (.app (.app motive a) (eqReflApp w α a)) ∧
      env.HasType U Γ b α ∧ env.HasType U Γ proof (eqApp w α a b) := by
  have H' : VExpr.WF env U Γ (mkApps (.const ``Eq.rec [v, w])
      [α, a, motive, minor, b, proof]) := H
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ H'
  obtain ⟨ci, hci, hw, _⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.2.1] at hci
  cases Option.some.inj hci
  have hhead := HasType.const (Γ := Γ) heq.2.2.1 hw (by rfl)
  obtain ⟨res, ht, _⟩ := HasType.mkApps_telescope henv hΓ hhead H' (by rfl)
  cases ht with | cons hα ht =>
  cases ht with | cons ha ht =>
  cases ht with | cons hM ht =>
  cases ht with | cons hm ht =>
  cases ht with | cons hb ht =>
  cases ht with | cons hp ht =>
  cases ht
  refine ⟨hw _ (by simp), hw _ (by simp), ?_⟩
  simpa [canonicalEqRecMotive, canonicalEqRecMinor, instL, VLevel.inst,
    inst, instVar, liftN, inst_liftN_lo, inst_lift, liftN_liftN, eqApp, eqReflApp] using
    And.intro hα (And.intro ha (And.intro hM (And.intro hm (And.intro hb hp))))

/-- K at arbitrary dependent motives, replayed at every supplied source type.
Only endpoint conversion is added to the typing of the source application. -/
theorem eqRecApp_simAt (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hab : env.IsDefEqU U Γ a b) :
    env.SimAt U Γ (eqRecApp v w α a motive minor b proof) minor := by
  intro T ht
  obtain ⟨_, hw, hα, ha, _, _, hb, hp⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have href := (IsDefEq.eqApp_r heq hw hα ha (hab.of_l henv hΓ ha)).defeq
    (HasType.eqReflApp heq hw hα ha)
  have hirr := IsDefEq.proofIrrel (HasType.eqApp heq hw hα ha hb) hp href
  obtain ⟨A, B, hf, hp'⟩ := (show VExpr.WF env U Γ
    (.app (.app (.app (.app (.app (.app (.const ``Eq.rec [v, w]) α) a) motive) minor) b) proof)
    from ⟨_, ht⟩).app_inv henv hΓ
  have hstep := IsDefEq.appDF hf ((show env.IsDefEqU U Γ proof (eqReflApp w α a)
    from ⟨_, hirr⟩).of_l henv hΓ hp')
  exact IsDefEq.trans_l henv hΓ ht
    (hstep.trans (IsDefEq.canonicalEqRec_iota henv heq hΓ hstep.hasType.2))

/-- Syntactic endpoint identity suffices to replay general K from source typing
alone, including proof-dependent motives and a free proof major. -/
theorem reflexive_eqRec_simAt (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) :
    env.SimAt U Γ (eqRecApp v w α a motive minor a proof) minor := by
  intro T ht
  obtain ⟨_, _, _, ha, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  exact eqRecApp_simAt henv heq hΓ ⟨_, ha⟩ T ht

end Lean4Lean.VEnv.Strengthening
