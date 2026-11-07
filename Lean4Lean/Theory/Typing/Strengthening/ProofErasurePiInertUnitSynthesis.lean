import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertZeroFrameReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecUniverse
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertApplicationFront

/-! # Finite synthesis of unit-carrier histories through nested Eq consumers

Leaves contain raw stage-zero comparisons, not hereditary histories. Internal
nodes retain the actual typing of an Eq consumer and recursively certify both
its index carrier and its returned carrier. The interpretation constructs all
future substitutions and independent residuals at an explicit finite stage.
This is a sound certificate language, not coverage of arbitrary type conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Finite provenance for a unit carrier. The comparison leaf uses the original
stage-zero checker. Eq nodes may nest in both the index carrier and the returned
carrier, and their consumers may duplicate, apply or bind the recursor value.
No node assumes a carrier history. Missing for general coverage is a construction
of this provenance from an arbitrary semantic conversion to a unit type. -/
inductive UnitCarrierSynthesis (D : Definitions) (family : Name) :
    Nat → List VExpr → VExpr → Prop where
  | compared (hΓ : OnCtx Γ (env.IsType univs))
      (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort v))
      (HF : RigidSortFrames family (proofEraseCtx Γ) (proofErase Γ A))
      (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) mode
        (proofErase Γ A) (proofErase Γ C)) :
      UnitCarrierSynthesis D family 0 Γ C
  | zeroPrefix (hΓ : OnCtx Γ (env.IsType univs))
      (hC : env.HasType univs Γ C (.sort u))
      (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
        (proofErase Γ C) (proofErase Γ E))
      (HE : UnitCarrierSynthesis D family n Γ E) : UnitCarrierSynthesis D family n Γ C
  | eqRec (hΓ : OnCtx Γ (env.IsType univs))
      (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
      (ht : env.HasType univs (T :: Γ) t (.sort u))
      (Hα : UnitCarrierSynthesis D family n Γ α)
      (Hm : UnitCarrierSynthesis D family k Γ (t.inst m)) :
      UnitCarrierSynthesis D family (max (n+1) k) Γ (t.inst (eqRecApp v w α a M m b p))
  | eqPrefix (hΓ : OnCtx Γ (env.IsType univs))
      (hr : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
      (ht : env.HasType univs (T :: Γ) t (.sort u))
      (Hα : UnitCarrierSynthesis D family n Γ α)
      (Hm : UnitCarrierSynthesis D family k Γ (t.inst (.lam (eqApp w α a b) m.lift))) :
      UnitCarrierSynthesis D family (max (n+1) k) Γ (t.inst (eqRecBeforeMajor v w α a M m b))

/-- A finite unit provenance constructs the entire carrier history. The index
child is interpreted first to license Eq computation; the result child consumes
its ordinary output tail. Only the index branch pays a stage increment, and no
raw comparison substitution or guarded confluence theorem is assumed. -/
theorem UnitCarrierSynthesis.history
    (H : UnitCarrierSynthesis D family n Γ C)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C) left right := by
  induction H generalizing left right with
  | compared hΓ hA hC HF H =>
    exact HF.zero_compared_history heq hs hc hi hp hx hfields hD hΓ hA hC H
  | zeroPrefix hΓ hC R HE ih =>
    exact PiInertCarrierHistory.carrier_prefix
      (PiInertEvidence.stage_zero heq hs hc ⟨_, _, _, hΓ, rfl, hC, rfl⟩ R) ih
  | @eqRec Γ v w α a M m b p T t u n k hΓ hr ht Hα Hm ihα ihm =>
    have R := ihα.eq_rec_consumer heq hs hl hcon hc hreg hoff hRec hΓ hr ht
    exact PiInertCarrierHistory.carrier_prefix
      (R.raise (Nat.le_max_left (n+1) k)) (ihm.raise (Nat.le_max_right (n+1) k))
  | @eqPrefix Γ v w α a M m b T t u n k hΓ hr ht Hα Hm ihα ihm =>
    have R := ihα.eq_prefix_consumer heq hs hl hcon hreg hoff hRec hΓ hr ht
    exact PiInertCarrierHistory.carrier_prefix
      (R.raise (Nat.le_max_left (n+1) k)) (ihm.raise (Nat.le_max_right (n+1) k))

/-- Synthesis forces actual carrier exposure, even in a context without two
unit inhabitants. Its interpretation allows arbitrary raw endpoints; distinct
variables rule out the checked-comparison alternative. -/
theorem UnitCarrierSynthesis.exposure
    (H : UnitCarrierSynthesis D family n Γ C)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    ∃ out, ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ C) out ∧
      CarrierExposure out := by
  have HK : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C) (.bvar 0) (.bvar 1) :=
    H.history heq hs hl hcon hc hreg hoff hRec hi hp hx hfields hD
  rcases (HK.base .refl .refl .refl).checked_or_exposed with HC | ⟨out, R, HE, _⟩
  · have E := HC.pi_inert_bvar_injective
    cases E
  · exact ⟨out, R, HE⟩

/-- A synthesized carrier for the lifted Eq type probe already reads the
original proposition equation below the added binders. Thus completeness of
this certificate language for arbitrary converted unit types cannot be assumed
as a harmless closure step: it must solve the same proposition-front test. -/
theorem UnitCarrierSynthesis.type_probe_descend
    (H : UnitCarrierSynthesis D family n Γ'
      (eqTypeProbe u (S.liftN count) (P.liftN count) (Q.liftN count) q))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ') (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count))) :
    env.IsDefEqU univs Γ P Q := by
  obtain ⟨out, R, HE⟩ := H.exposure heq hs hl hcon hc hreg hoff hRec hi hp hx hfields hD
  exact pi_inert_type_probe_descend heq hs hreg hoff hRec hΓ hΓ' W hS hP hQ hq R HE

end Lean4Lean.VEnv.Strengthening
