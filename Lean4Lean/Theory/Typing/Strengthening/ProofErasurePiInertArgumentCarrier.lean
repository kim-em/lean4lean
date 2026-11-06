import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLambdaCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryArgumentHistory

/-! # Joined arguments transport dependent carrier histories

The argument histories compute both bodies and the dependent carrier to their
shared instance. This handles different arguments without postulating paired
substitution closure for arbitrary carrier comparisons.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Joined argument histories instantiate a carrier history at the left
dependent carrier. The left argument's history also computes that carrier;
only substituting a shared argument in the endpoints would be insufficient. -/
theorem PiInertCarrierHistory.instantiate_argument_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : PiInertCarrierHistory D n (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ArgumentHistory D n Γ A (proofErase Γ x) shared)
    (RY : ArgumentHistory D n Γ A (proofErase Γ y) shared) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  have IX := RX.interpret heq hs hl hcon hcore hreg hoff hD
  have IY := RY.interpret heq hs hl hcon hcore hreg hoff hD
  obtain ⟨z, hz, Ez⟩ := IX.1
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨v, hB⟩ := hb.isType henv hΓA
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one shared) := by
    rw [← Ez]
    exact ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hz)
      (erasedSubstAgreement_one hΓA hz)
  have HM := H.substitute W
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hB,
    proofErase_instN hΓA hx Ctx.InstN.zero hb, proofErase_instN hΓA hy Ctx.InstN.zero hc]
  apply PiInertCarrierHistory.carrier_prefix
    ((IX.2 hB).pi_inert_evidence heq hs hl hcon hcore hreg hoff hD)
  apply PiInertCarrierHistory.prefixes
    ((IX.2 hb).pi_inert_evidence heq hs hl hcon hcore hreg hoff hD)
    ((IY.2 hc).pi_inert_evidence heq hs hl hcon hcore hreg hoff hD)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using HM

/-- Application at joined arguments consumes a retained fresh-body history.
Functions may be arbitrary typed terms. The premise is deliberately the body
history: inversion of a completed function-carrier certificate has not been
proved to retain the future substitutions needed here. -/
theorem PiInertCarrierHistory.application_argument_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : PiInertCarrierHistory D n (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
      (proofErase (A :: Γ) (.app g.lift (.bvar 0))))
    (RX : ArgumentHistory D n Γ A (proofErase Γ x) shared)
    (RY : ArgumentHistory D n Γ A (proofErase Γ y) shared) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have test {f} (hf : env.HasType univs Γ f (.forallE A B)) :
      env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (hf.weak henv) (.bvar .zero)
  have HI := H.instantiate_argument_histories heq hs hl hcon hcore hreg hoff hD
    hΓ hA (test hf) (test hg) hx hy RX RY
  simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using HI

/-- Displayed beta applications inherit the instantiated body history at the
left dependent result carrier. The argument histories may contain certified
casts; no ordinary-core join of the actual arguments is required. -/
theorem PiInertCarrierHistory.beta_application_argument_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : PiInertCarrierHistory D n (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ArgumentHistory D n Γ A (proofErase Γ x) shared)
    (RY : ArgumentHistory D n Γ A (proofErase Γ y) shared) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam A c) y)) := by
  have hleft := (HasType.lam hA hb).app hx
  have hright := (HasType.lam hA hc).app hy
  exact PiInertCarrierHistory.prefixes
    (PiInertEvidence.core hs hcore hΓ hleft (.beta (proofErase_beta_forward hΓ hleft .beta)))
    (PiInertEvidence.core hs hcore hΓ hright (.beta (proofErase_beta_forward hΓ hright .beta)))
    (H.instantiate_argument_histories heq hs hl hcon hcore hreg hoff hD hΓ hA hb hc hx hy RX RY)

omit [Params] in
/-- Actual canonical-Eq environments discharge all abstract computation and
registration assumptions for dependent application with joined histories. -/
theorem EnvironmentCore.carrier_argument_histories_application
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n Γ u A B f g x y shared}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) →
      env.HasType U Γ f (.forallE A B) → env.HasType U Γ g (.forallE A B) →
      env.HasType U Γ x A → env.HasType U Γ y A →
      PiInertCarrierHistory definitions n (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
        (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
        (proofErase (A :: Γ) (.app g.lift (.bvar 0))) →
      ArgumentHistory definitions n Γ A (proofErase Γ x) shared →
      ArgumentHistory definitions n Γ A (proofErase Γ y) shared →
      PiInertCarrierHistory definitions n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
        (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  letI := henv.params U
  intro n Γ u A B f g x y shared heq hΓ hA hf hg hx hy H RX RY
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.application_argument_histories heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hΓ hA hf hg hx hy RX RY

end Lean4Lean.VEnv.Strengthening
