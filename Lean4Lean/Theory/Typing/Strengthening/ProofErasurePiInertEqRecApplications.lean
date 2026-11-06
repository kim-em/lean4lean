import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecConsumer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertArgumentBoundary

/-! # Carrier-driven Eq computation beyond joined argument histories

Type-valued consumers transfer complete carrier histories. Distinct positive
unit variables instantiate the computation even though no joined argument
histories exist for those indices at any finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A type-valued consumer of general Eq recursion can supply the carrier of
another comparison. Both the index and minor carrier histories are retained
children; their combination requires exactly one additional stage. -/
theorem PiInertCarrierHistory.eq_rec_consumer_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t (.sort u))
    (HI : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b))
    (HM : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (t.inst m)) x y) :
    PiInertCarrierHistory D (n+1) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) x y :=
  PiInertCarrierHistory.carrier_prefix
    (HI.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ hr ht) (HM.raise (Nat.le_succ n))

/-- Distinct unit indices support general dependent Eq computation in every
typed consumer at stage one, although no joined ArgumentHistory pair exists
for those indices at any stage. The distinction is a checked theorem rather
than an assumption that carrier equality produces a common reduct. -/
theorem pi_inert_unit_eq_rec_consumer_without_argument_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hFamily : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hr : env.HasType univs Γ
      (eqRecApp v w (.const family ls) (.bvar i) M m (.bvar j) p) T)
    (ht : env.HasType univs (T :: Γ) t C) (hne : i ≠ j) :
    PiInertEvidence D 1 .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w (.const family ls) (.bvar i) M m (.bvar j) p)))
      (proofErase Γ (t.inst m)) ∧
    ∀ n shared, ¬ (ArgumentHistory D n Γ (.const family ls) (proofErase Γ (.bvar i)) shared ∧
      ArgumentHistory D n Γ (.const family ls) (proofErase Γ (.bvar j)) shared) := by
  obtain ⟨_, _, _, hiT, _, _, hjT, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  have HI : PiInertCarrierHistory D 0 (proofEraseCtx Γ) (proofErase Γ (.const family ls))
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
    rw [show proofErase Γ (.const family ls) = .const family ls from
      if_neg (not_isProof_of_sort hΓ hS)]
    exact pi_inert_unit_carrier_history hi hp hx hf hFamily
  exact ⟨HI.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ hr ht,
    (pi_inert_unit_argument_history_failure heq hs hl hcon hc hreg hoff hD
      hi hp hx hf hΓ hS hiT hjT hne).2⟩

omit [Params] in
/-- Actual canonical-Eq environments discharge soundness, confluence, universe
compatibility and registration hypotheses for the general consumer theorem.
Only the recursor/consumer typings and the index carrier history remain. -/
theorem EnvironmentCore.carrier_eq_rec_consumer {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n Γ v w α a M m b p T t S}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (eqRecApp v w α a M m b p) T →
      env.HasType U (T :: Γ) t S →
      PiInertCarrierHistory definitions n (proofEraseCtx Γ) (proofErase Γ α)
        (proofErase Γ a) (proofErase Γ b) →
      PiInertEvidence definitions (n+1) .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) (proofErase Γ (t.inst m)) := by
  letI := henv.params U
  intro n Γ v w α a M m b p T t S heq hΓ hr ht H
  obtain ⟨data, hlookup, hrec, hn, _⟩ := heq.recursorRegistration henv
  exact H.eq_rec_consumer heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hrec.eqRec_target heq hn).2.1
    (no_eqRec heq) hΓ hr ht

omit [Params] in
/-- The separation from joined histories holds for actual environments, with
arbitrary dependent motives and consumers. The literal unit carrier supplies
the index history automatically; no index-comparison premise is required. -/
theorem EnvironmentCore.unit_eq_rec_consumer_without_argument_join
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls Γ u v w i j M m p T t C}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.const family ls) (.sort (.succ u)) →
      env.HasType U Γ (eqRecApp v w (.const family ls) (.bvar i) M m (.bvar j) p) T →
      env.HasType U (T :: Γ) t C → i ≠ j →
      PiInertEvidence definitions 1 .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (eqRecApp v w (.const family ls) (.bvar i) M m (.bvar j) p)))
        (proofErase Γ (t.inst m)) ∧
      ∀ n shared, ¬ (ArgumentHistory definitions n Γ (.const family ls) (proofErase Γ (.bvar i)) shared ∧
        ArgumentHistory definitions n Γ (.const family ls) (proofErase Γ (.bvar j)) shared) := by
  letI := henv.params U
  intro family info ls Γ u v w i j M m p T t C heq hi hp hx hf hΓ hS hr ht hne
  obtain ⟨data, hlookup, hrec, hn, _⟩ := heq.recursorRegistration henv
  exact pi_inert_unit_eq_rec_consumer_without_argument_join heq sound (levelCompatible (fun H => H))
    (fun H => H) (typed_level_core_confluence (fun H => H)) hlookup (hrec.eqRec_target heq hn).2.1
    (no_eqRec heq) hi hp hx hf (no_rigid (henv.projectionRigid hi)) hΓ hS hr ht hne

end Lean4Lean.VEnv.Strengthening
