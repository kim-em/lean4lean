import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordReturn

/-! # Native family readout without normalizing unknown record values

Value demands can be interpreted trivially while the record-family type demand
still exposes a literal family head. Free functions returning record values are
also harmless; free functions returning family types are explicitly excluded.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets unitCarrier UnitArrows)
variable [Params] {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType}
variable {uc ctor family : Name}

/-- Only the record-family type key has an operational head requirement.
Function demands preserve that requirement at their result; value keys are true. -/
def TypeRealizes (family : Name) (e : ProofShape) : Key → Prop
  | .unit | .record => True
  | .fn _ keys result => ∀ a, (∀ key ∈ keys, TypeRealizes family a key) → TypeRealizes family (.app e a) result
  | .type .record => ∃ a, BetaRed e (.app (.const family []) a)
  | .type _ => True
termination_by key => sizeOf key

/-- These free keys cannot supply a family head. In particular record values
and arbitrary-order functions returning them need no operational realization. -/
def HeadFree : Key → Prop
  | .fn _ _ result => HeadFree result
  | .type .record => False
  | _ => True

/-- Every raw term realizes a head-free key, even after an untyped substitution.
This does not assert normalization or native recovery for that term. -/
theorem HeadFree.realizes (H : HeadFree key) : TypeRealizes family e key := by
  cases key with
  | unit | record => simp only [TypeRealizes]
  | fn A keys result =>
    simp only [HeadFree] at H
    simp only [TypeRealizes]
    exact fun _ _ => HeadFree.realizes H
  | type key => cases key <;> simp_all only [HeadFree, TypeRealizes]
termination_by sizeOf key

/-- Beta predecessors preserve the type-only interpretation. -/
theorem TypeRealizes.beta_back (R : BetaRed e e') (H : TypeRealizes family e' key) :
    TypeRealizes family e key := by
  cases key with
  | unit | record => simp only [TypeRealizes]
  | fn A keys result =>
    simp only [TypeRealizes] at H ⊢
    exact fun a ha => TypeRealizes.beta_back (.app R .refl) (H a ha)
  | type key =>
    cases key with
    | unit | fn | type => simp only [TypeRealizes]
    | record =>
      simp only [TypeRealizes] at H ⊢
      obtain ⟨a, HA⟩ := H
      exact ⟨a, R.trans HA⟩
termination_by sizeOf key

/-- The joint observer admits a type-only realization under raw substitution.
No value normalization is used to obtain the operational family-type head. -/
theorem Obs.type_realizes (H : Obs unit record parameter uc ctor family Ω S e key)
    (hσ : ∀ j key, S j key → TypeRealizes family (σ j) key) :
    TypeRealizes family (e.subst σ) key := by
  induction H generalizing σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [TypeRealizes]
  | record_ctor =>
    simp only [TypeRealizes]
    exact fun _ _ => trivial
  | family =>
    simp only [ProofShape.subst, TypeRealizes]
    exact fun a _ => ⟨a, .refl⟩
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
    (H : Obs unit record parameter uc ctor family Δ S e (.type .record))
    (HV : ∀ i key, S i key → HeadFree key) :
    ∃ a, BetaRed (e.subst σ) (.app (.const family []) a) := by
  simpa only [TypeRealizes] using H.type_realizes (σ := σ) (fun i key hi => (HV i key hi).realizes)

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

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
  exact (HN.full_compute hi hS Q hTag hF heq hs huc hc hf HS HV RA).head_free_family_readout HF

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

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
