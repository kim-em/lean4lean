import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProbeExpansionBarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProbeCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaCarrier

/-! # Shared application can require a strictly later carrier stage

Reflexive Eq probes already separate stage-zero function histories from their
shared-argument results. The result is available at stage one, so this is an
exact stage boundary, not a failure of finite application closure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private selector_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- Distinct raw variables have no stage-zero history at a type-valued Eq
recursor, regardless of any actual definitional equality of its indices. -/
theorem eq_rec_no_pi_inert_zero_bvar_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) (.sort u)) (hne : i ≠ j) :
    ¬ PiInertCarrierHistory D 0 (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (.bvar i) (.bvar j) := by
  intro H
  exact hne (eq_rec_pi_inert_zero_guard_bvar_injective heq hs hl hcon hc hreg hoff hRec
    hRigid hΓ ht (H.base .refl .refl .refl))

/-- A reflexive probe hiding an empty structure admits the distinct-variable
history exactly at positive stages. Stage zero includes arbitrary constant
expansion, so the lower bound does not merely count visible head changes. -/
theorem reflexive_unit_probe_history_iff_positive_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P P)) (hne : i ≠ j) :
    PiInertCarrierHistory D n (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u (.const family ls) P P q)) (.bvar i) (.bvar j) ↔ 1 ≤ n := by
  constructor
  · intro H
    cases n with
    | zero => exact (eq_rec_no_pi_inert_zero_bvar_history heq hs hl hcon hc hreg hoff hRec
        hRigid hΓ (eqTypeProbe_typed heq hΓ hS hP hP hq) hne H).elim
    | succ => omega
  · intro hn
    have hcl : TypedCoreConfluence (ErasedLevelCore D) := proofErase_level_core_confluent hs hl hcon hc
    have HR : PiInertEvidence D 0 .compute (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ P) :=
      PiInertEvidence.core hs hcl hΓ hP .refl
    have H := (HR.join hcl HR).unit_probe_carrier (a := .bvar i) (b := .bvar j)
      heq hs hl hcon hreg hoff hRec
      hi hp hx hf (hRigid (henv.projectionRigid hi)) hΓ hS hP hP hq
    exact H.raise hn

/-- Actual typed functions can have a stage-zero assigned-Pi history while
their shared application has a stage-one history and no stage-zero history.
The hidden conversion uses a reflexive probe, not an unproved proposition
front. Hence application cannot in general preserve the input stage. -/
theorem pi_inert_shared_application_strict_stage_example
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P P))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    ∃ A B f g x, env.HasType univs Γ f (.forallE A B) ∧
      env.HasType univs Γ g (.forallE A B) ∧ env.HasType univs Γ x A ∧
      PiInertCarrierHistory D 0 (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
        (proofErase Γ f) (proofErase Γ g) ∧
      PiInertCarrierHistory D 1 (proofEraseCtx Γ) (proofErase Γ (B.inst x))
        (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) ∧
      ¬ PiInertCarrierHistory D 0 (proofEraseCtx Γ) (proofErase Γ (B.inst x))
        (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  let S := VExpr.const family ls
  let F := VExpr.forallE S S
  let T := eqTypeProbe (.succ u) S P P q
  have HE : env.IsDefEq univs Γ T S (.sort (.succ u)) :=
    eqTypeProbe_defeq heq hΓ hS hP hP hq ⟨_, hP⟩
  have hF : env.HasType univs Γ F (.sort (.imax (.succ u) (.succ u))) :=
    .forallE hS (hS.weak henv)
  have hid : env.HasType univs Γ (.lam S (.bvar 0)) F := .lam hS (.bvar .zero)
  have selector {k} (hk : env.HasType univs Γ (.bvar k) S) :
      env.HasType univs Γ (.lam F (.app (.bvar 0) (.bvar (k+1)))) (.forallE F T.lift) := by
    apply HasType.lam hF
    apply (HE.symm.weak henv).defeq
    apply HasType.app (show env.HasType univs (F :: Γ) (.bvar 0) F from .bvar .zero)
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hk.weak (B := F) henv
  refine ⟨F, T.lift, _, _, _, selector hiT, selector hjT, hid,
    pi_inert_unit_selector_carrier_history heq hi hp hx hf
      (hRigid (henv.projectionRigid hi)) hΓ hS hiT hjT, ?_, ?_⟩
  all_goals simp only [VExpr.inst_lift]
  all_goals
    have RI := proofErase_beta_forward hΓ (HasType.app (selector_typing hΓ hS hiT).1 hid)
      (BetaRed.trans .beta .beta)
    have RJ := proofErase_beta_forward hΓ (HasType.app (selector_typing hΓ hS hjT).1 hid)
      (BetaRed.trans .beta .beta)
    simp only [VExpr.liftN_zero, VExpr.inst, VExpr.instVar_upper, VExpr.instVar_zero] at RI RJ
    have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS hiT)
    have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hS hjT)
  · have hcl : TypedCoreConfluence (ErasedLevelCore D) := proofErase_level_core_confluent hs hl hcon hc
    have HB := (reflexive_unit_probe_history_iff_positive_stage heq hs hl hcon hc hreg hoff
      hRec hRigid hi hp hx hf hΓ hS hP hq hne).2 (Nat.le_refl 1)
    rw [← Ei, ← Ej] at HB
    exact HB.prefixes
      (PiInertEvidence.core hs hcl hΓ (HasType.app (selector hiT) hid) (.beta RI))
      (PiInertEvidence.core hs hcl hΓ (HasType.app (selector hjT) hid) (.beta RJ))
  · intro H
    have HB := H.endpoint_reducts (.beta RI) (.beta RJ)
    rw [Ei, Ej] at HB
    exact eq_rec_no_pi_inert_zero_bvar_history heq hs hl hcon hc hreg hoff hRec hRigid
      hΓ (eqTypeProbe_typed heq hΓ hS hP hP hq) hne HB

omit [Params] in
/-- Every actual canonical-Eq environment containing a closed positive empty
structure supplies the strict application-stage example. The context, two
variables, proposition and reflexive equality proof are constructed here. -/
theorem EnvironmentCore.shared_application_strict_stage_of_closed_unit
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls u}, env.HasCanonicalEq → env.projections family info →
      info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      env.HasType U [] (.const family ls) (.sort (.succ u)) →
      ∃ Γ A B f g x, OnCtx Γ (env.IsType U) ∧
        env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ g (.forallE A B) ∧
        env.HasType U Γ x A ∧
        PiInertCarrierHistory definitions 0 (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
          (proofErase Γ f) (proofErase Γ g) ∧
        PiInertCarrierHistory definitions 1 (proofEraseCtx Γ) (proofErase Γ (B.inst x))
          (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) ∧
        ¬ PiInertCarrierHistory definitions 0 (proofEraseCtx Γ) (proofErase Γ (B.inst x))
          (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  letI := henv.params U
  intro family info ls u heq hi hp hx hf hS
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType U) := ⟨⟨by trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hSw : env.HasType U Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  let P : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hP : env.HasType U Γ P (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  have hq := HasType.eqReflApp heq (by trivial) (HasType.sort (by trivial)) hP
  have hiT : env.HasType U Γ (.bvar 0) S := .bvar .zero
  have hjT : env.HasType U Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  obtain ⟨A, B, f, g, x, H⟩ := pi_inert_shared_application_strict_stage_example heq sound
    (levelCompatible (fun H => H)) (fun H => H) (typed_core_confluence (fun H => H))
    hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq) (fun hr => no_rigid hr)
    hi hp hx hf hΓ hSw hP hq hiT hjT (by decide)
  exact ⟨Γ, A, B, f, g, x, hΓ, H⟩

end Lean4Lean.VEnv.Strengthening
