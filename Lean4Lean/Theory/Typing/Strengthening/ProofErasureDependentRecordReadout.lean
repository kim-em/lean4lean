import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentRecordStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordTypeReadout

/-! # Native readout with dependent family certificates

The new type leaf admits dependent/proof-domain control frames. Actual family
metadata and ordinary equality fix its monomorphic head before raw substitution.
-/
namespace Lean4Lean.VEnv.Strengthening.DependentRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier TypeRealizes HeadFree)
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

/-- Independent dependent-profile evidence beta-exposes the registered
monomorphic family. Ordinary carrier equality fixes the universe instance before
any untyped substitution is applied; no target interpretation is required. -/
theorem dependent_family_head
    (HE : TypeEquality Δ e (.atom RT))
    (HR : RigidDemandProfile.Obs t 1 Δ (fun _ _ _ => False) e .sort .pi) :
    ∃ a, BetaRed (e.subst σ) (.app (.const t []) a) := by
  obtain ⟨ls, args, hn, RB⟩ := HR.head_readout
  obtain ⟨Γ, A, hΓ, EΓ, HE, EA⟩ := HE
  obtain ⟨actual, RA, EE⟩ := proofErase_beta_replay hΓ HE.hasType.1 (EA ▸ RB)
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EE
  have HE' := HE.symm.trans (beta_eq hΓ HE.hasType.1 RA)
  have HF : env.IsDefEqU univs Γ (VExpr.mkApps (.const t []) [Q.value hi hS])
      (VExpr.mkApps (.const t ls) args') := HE'.toU
  have HL := (HF.structApp_inv henv hΓ hTag HE.hasType.2).1
  cases HL
  cases args with
  | nil => simp at hn
  | cons a args =>
    have E : args = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hn; omega)
    subst args
    exact ⟨a.subst σ, by simpa only [ProofShape.mkApps, List.foldl_cons, List.foldl_nil,
      ProofShape.subst] using RB.subst (σ := σ)⟩

/-- The joint observer admits a type-only realization under raw substitution.
No value normalization is used to obtain the operational family-type head. -/
theorem Obs.type_realizes (H : Obs U RT (Q.control U) uc c t Ω S e key)
    (hσ : ∀ j key, S j key → TypeRealizes t (σ j) key) :
    TypeRealizes t (e.subst σ) key := by
  induction H generalizing σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [TypeRealizes]
  | record_ctor =>
    simp only [TypeRealizes]
    exact fun _ _ => trivial
  | family =>
    simp only [ProofShape.subst, TypeRealizes]
    exact fun a _ => ⟨a, .refl⟩
  | record_type HE HR =>
    simpa only [TypeRealizes] using dependent_family_head hi hS Q hTag hF (σ := σ) HE HR
  | unit_type | univ | family_type | pi => simp only [TypeRealizes]
  | app _ _ _ ihf iha =>
    have HF := ihf hσ
    simp only [TypeRealizes] at HF
    exact HF _ (fun key hk => iha key hk hσ)
  | @lam Δ A b domain keys result S _ _ _ _ _ _ ihb =>
    simp only [TypeRealizes]
    intro a ha
    have HB := ihb (σ := σ.cons a) (fun j key hj => by
      cases j with
      | zero => exact ha key hj
      | succ j => exact hσ j key hj)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext j
      cases j with
      | zero => rfl
      | succ j => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons,
          ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact TypeRealizes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB

/-- Native family observations expose their fixed head despite arbitrary
head-free ambient values and arbitrary raw substitution of those values. -/
theorem Obs.head_free_family_readout
    (H : Obs U RT (Q.control U) uc c t Δ S e (.type .record))
    (HV : ∀ i key, S i key → HeadFree key) :
    ∃ a, BetaRed (e.subst σ) (.app (.const t []) a) := by
  simpa only [TypeRealizes] using H.type_realizes hi hS Q hTag hF (σ := σ) (fun i key hi => (HV i key hi).realizes)

/-- Full term/native/type histories of an observed program preserve its native
family head. Free record values and functions returning record values may be
unknown. Their actual oracle types remain jointly observed through HV. -/
theorem program_native_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (H : Obs U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ T out) :
    ∃ a, BetaRed (out.subst σ) (.app (.const t []) a) := by
  have HE := H.full_compute hi hS Q hTag hF heq hs huc hc hf HS HV RE
  have HN := HE.full_native hi hS Q hTag hF heq hs huc hc hf HS HV RN
  exact (HN.full_compute hi hS Q hTag hF heq hs huc hc hf HS HV RA).head_free_family_readout hi hS Q hTag hF HF

/-- Actual stored family data joins substituted native histories of observed
programs with independently computed assigned families. Target native recovery
and argument normalization follow from the declaration and unit-arrow profile;
the source program's joint observation is the remaining explicit restriction. -/
theorem program_environment_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (H : Obs U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨a, HA⟩ := program_native_head_readout hi hS Q hTag hF (σ := σ) heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) H HS HV HF RE RN RA
  have HC := Q.caller_telescope hi hS heq EnvironmentCore.sound hΓ' (B := proofErase ((Q.control U).expr :: Γ') B) .nil
  exact ⟨(ScopedCompute.beta HA).trans
      (HC.compute (args := [a]) (Q.stored_family_native hi hS hΓ' hcf hU hT) rfl),
    Q.environment_stored_family_return hi hS heq hTag rfl hcf hU hT hΓ' hAssigned RB⟩

end Lean4Lean.VEnv.Strengthening.DependentRecordDemand
