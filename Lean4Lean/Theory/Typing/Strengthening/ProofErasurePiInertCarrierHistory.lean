import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierEvidence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCastEvidence

/-! # Carrier histories retain independent computation of the assigned type

The weaker carrier predicate retains endpoint residuals. Pulling a guard back
through a certified type computation additionally needs the output carrier's
ordinary-core residuals. This file constructs that stronger history for checked
comparisons and empty structures, and closes it under certified computations.
No arbitrary comparison-to-computation promotion or carrier conversion is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- All three positions may independently follow ordinary full-core paths.
Carrier computation is retained explicitly rather than inferred from endpoint
stability or from actual definitional equality of two types. -/
def PiInertCarrierResidual (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop :=
  ∀ {C' a' b'}, Compute (ErasedLevelCore D) C C' →
    Compute (ErasedLevelCore D) a a' → Compute (ErasedLevelCore D) b b' →
    ComputedJointCarrierGuard (PiInertStage D stage) Δ C' a' b'

/-- A carrier residual interpretation and every future interpreted typed
substitution of its three inputs. This stronger property is constructed below;
there is no universal promotion from PiInertCarrierEvidence. -/
structure PiInertCarrierHistory (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop where
  base : PiInertCarrierResidual D stage Δ C a b
  future : ∀ {Δ' τ}, ContextSubstitution Δ Δ' τ →
    PiInertCarrierResidual D stage Δ' (C.subst τ) (a.subst τ) (b.subst τ)

/-- Forgetting independent carrier reduction retains the previous evidence. -/
theorem PiInertCarrierHistory.evidence (H : PiInertCarrierHistory D stage Δ C a b) :
    PiInertCarrierEvidence D stage Δ C a b := by
  refine ⟨fun RA RB => H.base .refl RA RB, ?_⟩
  intro Δ' τ W a' b' RA RB
  exact H.future W .refl RA RB

/-- A common comparison supplies all carrier residuals because its checked
carrier rule does not inspect the supplied type. -/
theorem PiInertEvidence.carrier_history
    (H : PiInertEvidence D stage (.compare true) Δ a b) : PiInertCarrierHistory D stage Δ C a b := by
  refine ⟨fun _ RA RB => .carrierChecked (H.base RA RB), ?_⟩
  intro Δ' τ W C' a' b' _ RA RB
  exact .carrierChecked (H.future W RA RB)

/-- Future carrier histories compose typed substitutions at the same stage. -/
theorem PiInertCarrierHistory.substitute (H : PiInertCarrierHistory D stage Δ C a b)
    (W : ContextSubstitution Δ Δ' τ) :
    PiInertCarrierHistory D stage Δ' (C.subst τ) (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.comp V)

/-- Stage raising preserves the carrier and all future residuals. -/
theorem PiInertCarrierHistory.raise (hle : n ≤ m) (H : PiInertCarrierHistory D n Δ C a b) :
    PiInertCarrierHistory D m Δ C a b := by
  refine ⟨fun RC RA RB => (H.base RC RA RB).mono (fun R => pi_inert_stage_mono hle R), ?_⟩
  intro Δ' τ W C' a' b' RC RA RB
  exact (H.future W RC RA RB).mono (fun R => pi_inert_stage_mono hle R)

/-- Symmetry leaves the independently computed carrier unchanged. -/
theorem PiInertCarrierHistory.symm (H : PiInertCarrierHistory D stage Δ C a b) :
    PiInertCarrierHistory D stage Δ C b a := by
  refine ⟨fun RC RA RB => .carrierSymm (H.base RC RB RA), ?_⟩
  intro Δ' τ W C' a' b' RC RA RB
  exact .carrierSymm (H.future W RC RB RA)

/-- A rigid nullary empty structure remains an empty-structure carrier through
full-core computation, including universe conversion. All endpoint residuals
and future substitutions are allowed. Only its family must not unfold. -/
theorem pi_inert_unit_carrier_history
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    PiInertCarrierHistory D stage Δ (.const family ls) a b := by
  have local_history {Δ C' a' b'} (RC : Compute (ErasedLevelCore D) (.const family ls) C') :
      ComputedJointCarrierGuard (PiInertStage D stage) Δ C' a' b' := by
    have hroot : ConstantRootLevels (fun _ => ErasedLevelCore D) family := by
      intro Δ levels out R
      rcases R with R | R
      · exact (erased_iota_primitive_no_rigid (henv.projectionRigid hi) hD R rfl).elim
      · cases R with
        | const HL _ => exact ⟨_, rfl, HL⟩
    obtain ⟨ls', rfl, _⟩ := (RC.scoped (Δ := Δ) (fun R => .base R)).const_levels_inv @hroot
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)
  refine ⟨fun RC _ _ => local_history RC, ?_⟩
  intro Δ' τ _ C' a' b' RC _ _
  exact local_history RC

/-- A certified carrier computation retains an ordinary-core tail at its
output. The target history consumes that tail, giving a guard at every core
residual of the input carrier. No confluence of the guarded stage is needed. -/
theorem PiInertCarrierResidual.carrier_prefix
    (R : PiInertInterpret D stage .compute Δ C E)
    (H : PiInertCarrierResidual D stage Δ E a b) : PiInertCarrierResidual D stage Δ C a b := by
  intro C' a' b' RC RA RB
  obtain ⟨shared, RS, RE⟩ := R.2 RC
  exact .carrierCompute RS (H RE RA RB)

/-- Certified computation of a supplied type pulls back the complete carrier
history, including every future typed substitution and carrier residual. -/
theorem PiInertCarrierHistory.carrier_prefix
    (R : PiInertEvidence D stage .compute Δ C E)
    (H : PiInertCarrierHistory D stage Δ E a b) : PiInertCarrierHistory D stage Δ C a b :=
  ⟨PiInertCarrierResidual.carrier_prefix R.base H.base,
    fun W => PiInertCarrierResidual.carrier_prefix (R.future W) (H.future W)⟩

/-- Two certified endpoint computations preserve a history at the same carrier.
Their retained ordinary-core tails feed the old history independently. -/
theorem PiInertCarrierResidual.prefixes
    (RA : PiInertInterpret D stage .compute Δ a a')
    (RB : PiInertInterpret D stage .compute Δ b b')
    (H : PiInertCarrierResidual D stage Δ C a' b') : PiInertCarrierResidual D stage Δ C a b := by
  intro C' left right RC RL RR
  obtain ⟨left', RS, RT⟩ := RA.2 RL
  obtain ⟨right', RU, RV⟩ := RB.2 RR
  exact .carrierReduce RS RU (H RC RT RV)

/-- Endpoint computation and carrier computation can be nested and reused
without discarding any future substitution or independent core residual. -/
theorem PiInertCarrierHistory.prefixes
    (RA : PiInertEvidence D stage .compute Δ a a')
    (RB : PiInertEvidence D stage .compute Δ b b')
    (H : PiInertCarrierHistory D stage Δ C a' b') : PiInertCarrierHistory D stage Δ C a b :=
  ⟨PiInertCarrierResidual.prefixes RA.base RB.base H.base,
    fun W => PiInertCarrierResidual.prefixes (RA.future W) (RB.future W) (H.future W)⟩

/-- A type-valued consumer of a certified cast becomes a supplied carrier.
The explicit index comparison constructs the equality major; the consumer's
computation pulls back the old carrier history at the next stage. The result
retains all future carrier and endpoint residuals, not just a base guard. -/
theorem PiInertCarrierHistory.cast_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t (.sort w))
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ X) (proofErase Γ Y))
    (HC : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (t.inst x)) a b) :
    ∃ q, env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y) ∧
      PiInertCarrierHistory D (n+1) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X Y q x))) a b := by
  obtain ⟨q, hq, R⟩ := H.type_cast heq hs hl hcon hc hreg hoff hD hu hΓ hX hY hx ht
  exact ⟨q, hq, PiInertCarrierHistory.carrier_prefix R (HC.raise (Nat.le_succ n))⟩

end Lean4Lean.VEnv.Strengthening
