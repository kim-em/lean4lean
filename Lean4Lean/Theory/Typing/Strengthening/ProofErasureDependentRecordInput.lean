import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentRecordReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureObservedOracleBoundary

/-! # Native joins with dependent beta-wrapped family annotations

The family parameter may depend on an arbitrary displayed binder, including a
proof binder. Its supplied argument needs ordinary typing only. The wrapped
annotation and all its full computational descendants initialize actual lookup.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

namespace RigidDemandProfile

/-- A typed type-valued beta wrapper carries its body's family demand with
no demand on the supplied argument. The displayed domain may be open or Prop. -/
theorem Obs.typed_wrapper
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (hx : env.HasType univs Γ x A)
    (H : Obs family arity (proofEraseCtx (A :: Γ)) (fun _ _ _ => False)
      (proofErase (A :: Γ) B) .sort .pi) :
    Obs family arity (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.app (.lam A B) x)) .sort .pi := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hf := HasType.lam hA hB
  have ht : env.HasType univs Γ (.app (.lam A B) x) (.sort v) := .app hf hx
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hV⟩ := ht.isType henv hΓ
  have EF : proofErase Γ (.lam A B) = .lam (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EE : proofErase Γ (.app (.lam A B) x) =
      .app (.lam (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.lam A B) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), EF]
  rw [EE]
  refine .app (A := .ignored) (keys := [])
    ⟨Γ, _, _, hΓ, rfl, ht, DemandProfile.Fits.of_sortTelescope hΓ hV .sort, EE⟩
    (.lam ⟨Γ, _, _, hΓ, rfl, hf, DemandProfile.Fits.of_sortTelescope hΓ hPi (.forallE .sort), EF⟩
      (by simp) ?_) (by simp)
  simpa only [ProofShape.subst_id, proofEraseCtx] using
    H.rename ContextRenaming.identity.interpretation
      (T := DemandProfile.Sets.cons .ignored [] (fun _ _ _ => False)) (by intro i t k h; cases h)

end RigidDemandProfile

namespace DependentRecordDemand
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier ObservedInput)
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

include hF in
/-- The registered family initializes the independent dependent observer. -/
theorem rigid_family_observation (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (Q.control U).expr) :
    RigidDemandProfile.Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.app (.const t []) p)) .sort .pi := by
  have hf := hF.weak0 (Γ := Γ) henv.ordered
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have HP := DemandProfile.Fits.of_sortTelescope hΓ hPi (.forallE .sort)
  have EF : proofErase Γ (.const t []) = .const t [] := if_neg (not_isProof_function_to_sort hΓ hf)
  have H : RigidDemandProfile.Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.const t [])) (DemandProfile.spineProfile 1) (DemandProfile.spineDemand 1) := by
    rw [EF]
    exact .const ⟨Γ, _, _, hΓ, rfl, hf, HP, EF⟩
  exact H.telescope (args := [p]) hΓ hf HP (.cons hp .nil)

/-- Dependent beta-wrapped families have both ordinary carrier equality and
operational family evidence. In particular proof domains impose no restriction. -/
theorem wrapped_family_evidence
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hx : env.HasType univs Γ x A)
    (hp : env.HasType univs (A :: Γ) p (Q.control U).expr) :
    TypeEquality (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.app (.const t []) p)) x)) (.atom RT) ∧
      RigidDemandProfile.Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
        (proofErase Γ (.app (.lam A (.app (.const t []) p)) x)) .sort .pi := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hf := hF.weak0 (Γ := A :: Γ) henv.ordered
  have hB := hf.app hp
  have HB : env.IsDefEq univs (A :: Γ) (.app (.const t []) p)
      (HeterogeneousControl.ControlType.atom RT).expr (.sort (.succ .zero)) :=
    IsDefEq.appDF hf (Q.value_equal hi hS hp)
  have HI : env.IsDefEq univs Γ ((VExpr.app (.const t []) p).inst x)
      (HeterogeneousControl.ControlType.atom RT).expr (.sort (.succ .zero)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, HeterogeneousControl.ControlType.expr_subst,
      VExpr.subst] using HB.instN henv.ordered hx Ctx.InstN.zero
  exact ⟨⟨Γ, _, hΓ, rfl, (IsDefEq.beta hB hx).trans HI, rfl⟩,
    (rigid_family_observation hi hS Q hF hΓA hp).typed_wrapper hΓ hA hB hx⟩

/-- Independent family evidence at the actual annotation initializes an
unknown record and its exact native oracle. It has no free value assumptions. -/
theorem independent_record_input
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (HE : TypeEquality (proofEraseCtx Γ) (proofErase Γ A) (.atom RT))
    (HR : RigidDemandProfile.Obs t 1 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ A) .sort .pi) :
    (ObservedInput i .record).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) ∧
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) (.bvar i) .record := by
  have HT := HE.lookup_control hΓ hl
  refine ⟨?_, ?_, .var HT (by simp [Key.Valid]) ⟨rfl, rfl⟩⟩
  · rintro j k ⟨rfl, rfl⟩; exact HT
  · rintro j k ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    exact E ▸ Obs.record_type HE HR

/-- Full computation of a dependent beta-wrapped annotation can be stored as
an actual record lookup. Both value and native evidence follow without any
native certificate for the argument supplied inside the annotation. -/
theorem wrapped_record_input
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i T)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (hp : env.HasType univs (A :: Γ) p (Q.control U).expr)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A (.app (.const t []) p)) x)) (proofErase Γ T)) :
    (ObservedInput i .record).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) ∧
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) (.bvar i) .record := by
  obtain ⟨HE, HR⟩ := wrapped_family_evidence hi hS Q hTag hF hΓ hA hx hp
  exact independent_record_input hi hS Q hTag hF hΓ hl
    (HE.compute (erased_static_structure_eta_expansion_union_descent heq hs) RP)
    (family_preserves_union hi hS Q hTag heq hs hf RP HR)

/-- The earlier proof-domain obstruction is now admitted by the extended
observer, while remaining excluded by the original grammar. -/
theorem proof_wrapper_strict_extension
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hz : env.HasType univs Γ z P) (hp : env.HasType univs Γ p (Q.control U).expr) :
    ∃ A, Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S (proofErase Γ A) (.type .record) ∧
      ¬ IgnoredRecordDemand.Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) S
        (proofErase Γ A) (.type .record) := by
  have hp' : env.HasType univs (P :: Γ) p.lift (Q.control U).expr := by
    simpa only [HasType, (Q.control U).closedN.lift_eq] using hp.weak henv
  obtain ⟨HE, HR⟩ := wrapped_family_evidence hi hS Q hTag hF hΓ hP hz hp'
  obtain ⟨_, _, HN⟩ := IgnoredRecordDemand.proof_domain_beta_predecessor_boundary
    (unit := U) (record := RT) (parameter := Q.control U) (uc := uc) (ctor := c) (family := t)
    (S := S) hΓ hP hz ((hF.weak0 henv.ordered).app hp)
  exact ⟨_, .record_type HE HR, HN⟩

include hTag hF in
/-- Native types of unknown records with dependent beta-wrapped annotations
join independently computed assigned families after arbitrary raw substitution.
The wrapper domain and argument are arbitrary, and all later histories are full. -/
theorem wrapped_record_environment_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i T₀)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (hp : env.HasType univs (A :: Γ) p (Q.control U).expr)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A (.app (.const t []) p)) x)) (proofErase Γ T₀))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort v))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) (.bvar i) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HS, HV, H⟩ := wrapped_record_input hi hS Q hTag hF heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hΓ hl hA hx hp RP
  exact program_environment_native_assigned_join hi hS Q hTag hF heq hcf hU hT H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

end DependentRecordDemand
end Lean4Lean.VEnv.Strengthening
