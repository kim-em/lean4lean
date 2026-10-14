import Lean4Lean.Theory.Typing.Strengthening.RigidFullExposure
import Lean4Lean.Theory.Typing.Strengthening.FamilyRecoveryExistence

/-! # The operational gap in recovery completeness

Confluence already produces full Pi/family exposure. Recovery completeness
therefore needs repair of head-exposing paths into the chosen computational
model, allowing different annotations and family arguments. Exact replay of
every ambient reduction target is unnecessary and is refuted elsewhere.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {C : List VExpr → VExpr → VExpr → Prop}

/-- Repair a full Pi-exposing path to some computational Pi exposure. This is
unproved for the concrete staged models; its target annotations may change. -/
def RecoveryPiHeadRepair (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ T A B u}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ T (.sort u) →
    @FullReduction (henv.params univs) Γ T (.forallE A B) →
    ∃ A' B', C Γ T (.forallE A' B')

/-- Repair full family exposure at a typed projection. A registration witness,
field success, and original family parameters are not requested of the output.
This is unproved for the concrete staged models. -/
def RecoveryFamilyHeadRepair (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ s i m T ls args}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.proj s i m) → env.HasType univs Γ m T →
    @FullReduction (henv.params univs) Γ T (mkApps (.const s ls) args) →
    ∃ ls' args', C Γ T (mkApps (.const s ls') args')

/-- Declarative Pi exposure supplies repair by soundness of full reduction. -/
theorem RecoveryPiExposure.headRepair (H : RecoveryPiExposure C) :
    RecoveryPiHeadRepair C := by
  intro Γ T A B u hΓ hT R
  exact H hΓ hT ⟨_, @FullReduction.defeq (henv.params univs) _ _ _ _ hΓ R hT⟩

/-- Confluence supplies the path needed by the repair premise. This asks for
head repair alone, without any normalization of arbitrary expressions. -/
theorem RecoveryPiHeadRepair.exposure (H : RecoveryPiHeadRepair C)
    (heq : env.HasCanonicalEq) : RecoveryPiExposure C := by
  intro Γ T A B u hΓ hT HT
  obtain ⟨A', B', R⟩ := defeq_pi_full_exposure henv heq hΓ (HT.of_l henv hΓ hT)
  exact H hΓ hT R

/-- Under canonical Eq, the declarative Pi premise is precisely full-path
head repair; confluence contributes no additional unresolved obligation. -/
theorem recoveryPiExposure_iff_headRepair (heq : env.HasCanonicalEq) :
    RecoveryPiExposure C ↔ RecoveryPiHeadRepair C :=
  ⟨RecoveryPiExposure.headRepair, fun H => H.exposure heq⟩

/-- Family exposure trivially repairs any given full exposing path. -/
theorem RecoveryFamilyExposure.headRepair (H : RecoveryFamilyExposure C) :
    RecoveryFamilyHeadRepair C := by
  intro Γ s i m T ls args hΓ ht hm _
  exact H hΓ ht hm

/-- Rigid-family exposure supplies the full path at every source projection,
including eta-expanded intermediate spines and nonliteral family headers. -/
theorem RecoveryFamilyHeadRepair.exposure (H : RecoveryFamilyHeadRepair C)
    (heq : env.HasCanonicalEq) : RecoveryFamilyExposure C := by
  intro Γ s i m T hΓ ht hm
  obtain ⟨ls, args, R⟩ := projection_type_full_exposure henv heq hΓ ht hm
  exact H hΓ ht hm R

/-- The projection-family premise likewise has no remaining declarative
head-exposure gap. Only repair into the computational model is open. -/
theorem recoveryFamilyExposure_iff_headRepair (heq : env.HasCanonicalEq) :
    RecoveryFamilyExposure C ↔ RecoveryFamilyHeadRepair C :=
  ⟨RecoveryFamilyExposure.headRepair, fun H => H.exposure heq⟩

/-- These two operational repair clauses suffice for re-synthesis existence.
They are not claimed sufficient alone for the original strengthening theorem. -/
theorem RecoveryExists.of_full_head_repair (hc : ComputeDescent C)
    (heq : env.HasCanonicalEq) (hPi : RecoveryPiHeadRepair C)
    (hFamily : RecoveryFamilyHeadRepair C) : RecoveryExists C :=
  RecoveryExists.of_head_exposure hc (hPi.exposure heq) (hFamily.exposure heq)

end Lean4Lean.VEnv.Strengthening
