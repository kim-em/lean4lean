import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbeComputation

/-! # Explicit index evidence repairs hidden carrier types

A type-valued Eq probe hides its minor behind proposition indices. Earlier
composition boundaries lacked those indices' comparison history. Given that
smaller child explicitly, full-core probe residuals return to minor residuals
at the next stage. Carrier histories then transfer to the hidden type while
retaining all three independent core paths and future typed substitutions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

omit [Params] in
/-- Type-valued Eq probe syntax commutes with actual simultaneous substitution. -/
theorem eqTypeProbe_subst : (eqTypeProbe u S P Q q).subst σ =
    eqTypeProbe u (S.subst σ) (P.subst σ) (Q.subst σ) (q.subst σ) := by
  simp only [eqTypeProbe, eqRecApp_subst, constantEqMotive,
    VExpr.subst, VExpr.eqApp_subst, VExpr.lift_subst_lift]
  rfl

/-- Every ordinary full-core residual of a typed probe computes to an ordinary
core residual of its minor. The supplied earlier-stage index interpretation
repairs the Eq prefix after universe and argument computation. -/
theorem pi_inert_type_probe_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertInterpret D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (R : Compute (ErasedLevelCore D) (proofErase Γ (eqTypeProbe u S P Q q)) out) :
    ∃ minor, Compute (ErasedLevelCore D) (proofErase Γ S) minor ∧
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) out minor := by
  have ht := eqTypeProbe_typed heq hΓ hS hP hQ hq
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ ht R
  rw [eqTypeProbe_erase heq hΓ hS hP hQ hq] at RM
  obtain ⟨α', a', M', m', b', rfl, _, Ra, _, Rm, Rb⟩ := RM.eqRec_proof_core_inv hreg hoff hD
  have HG := (H (Ra.mono (fun R => .inl R)) (Rb.mono (fun R => .inl R))).mono
    (fun R => pi_inert_stage_embed R)
  exact ⟨m', Rm.mono (fun R => .inl R),
    RT.in_pi_inert_stage.trans (ComputedJointCompare.next_pi_inert_stage HG)⟩

/-- The probe/minor computation retains its typed output and the full-core
output tail needed for subsequent carrier conversion. -/
theorem PiInertInterpret.type_probe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertInterpret D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    PiInertInterpret D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  refine ⟨⟨Γ, S, _, hΓ, rfl, hS, rfl⟩, ?_⟩
  intro out R
  obtain ⟨minor, RM, RT⟩ := pi_inert_type_probe_core_residual heq hs hl hcon hreg hoff hD
    hΓ hS hP hQ hq H R
  exact ⟨minor, RT, RM⟩

/-- Future typed substitutions reconstruct the probe and its index child at
exactly the next stage. No comparison closure for arbitrary substituted
certificates is assumed. -/
theorem PiInertEvidence.type_probe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  refine ⟨PiInertInterpret.type_probe heq hs hl hcon hreg hoff hD hΓ hS hP hQ hq H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have H' : PiInertInterpret D n (.compare true) Δ'
      ((proofErase Γ P).subst τ) ((proofErase Γ Q).subst τ) := H.future W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hP ES,
    ← proofErase_subst_with hΓ₀ WS hQ ES] at H'
  have ht := eqTypeProbe_typed heq hΓ hS hP hQ hq
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS ht ES,
    ← proofErase_subst_with hΓ₀ WS hS ES, eqTypeProbe_subst]
  exact PiInertInterpret.type_probe heq hs hl hcon hreg hoff hD hΓ₀
    (hS.subst henv.orderedStrong WS hΓ₀) (hP.subst henv.orderedStrong WS hΓ₀)
    (hQ.subst henv.orderedStrong WS hΓ₀)
    (by simpa only [VExpr.eqApp_subst, VExpr.subst] using hq.subst henv.orderedStrong WS hΓ₀) H'

/-- An explicit index-comparison child transfers the entire carrier history
from the minor to the type-valued Eq probe. This repairs the hidden-carrier
configuration conditionally on its actual conversion evidence, not on arbitrary
semantic equality or a universal carrier-composition principle. -/
theorem PiInertCarrierHistory.type_probe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q))
    (HC : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ S) a b) :
    PiInertCarrierHistory D (n+1) (proofEraseCtx Γ) (proofErase Γ (eqTypeProbe u S P Q q)) a b :=
  PiInertCarrierHistory.carrier_prefix (H.type_probe heq hs hl hcon hreg hoff hD hΓ hS hP hQ hq)
    (HC.raise (Nat.le_succ n))

/-- The empty-structure composition obstruction hidden behind an Eq probe is
repaired when its proposition-index comparison child is retained. The result
covers arbitrary endpoints, carrier residuals, and future typed substitutions.
No assertion that the child follows from semantic equality is made. -/
theorem PiInertEvidence.unit_probe_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hFamily : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    PiInertCarrierHistory D (n+1) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) a b := by
  have HC : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (.const family ls)) a b := by
    rw [show proofErase Γ (.const family ls) = .const family ls from if_neg (not_isProof_of_sort hΓ hS)]
    exact pi_inert_unit_carrier_history hi hp hx hf hFamily
  exact HC.type_probe heq hs hl hcon hreg hoff hD hΓ hS hP hQ hq H

omit [Params] in
/-- Actual well-formed canonical-Eq environments discharge the soundness,
registry, universe and non-unfolding premises for the hidden-unit repair. The
only conversion certificate retained as input is the explicit index child. -/
theorem EnvironmentCore.unit_probe_carrier_history {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls Γ u P Q q n a b}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.const family ls) (.sort u) →
      env.HasType U Γ P (.sort .zero) → env.HasType U Γ Q (.sort .zero) →
      env.HasType U Γ q (eqApp (.succ .zero) (.sort .zero) P Q) →
      PiInertEvidence definitions n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q) →
      PiInertCarrierHistory definitions (n+1) (proofEraseCtx Γ)
        (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) a b := by
  letI := henv.params U
  intro family info ls Γ u P Q q n a b heq hi hp hx hf hΓ hS hP hQ hq H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.unit_probe_carrier heq sound (levelCompatible (fun H => H)) (fun H => H)
    hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq) hi hp hx hf
    (no_rigid (henv.projectionRigid hi)) hΓ hS hP hQ hq

end Lean4Lean.VEnv.Strengthening
