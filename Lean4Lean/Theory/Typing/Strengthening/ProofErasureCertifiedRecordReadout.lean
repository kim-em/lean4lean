import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordTypeReadout

/-! # Parametric operational readout from joint native observations

The result predicate may admit beta-only or actual delta cleanup. Its only
requirements are explicit backward beta closure, literal family seeds, and
readout of independent family evidence. Value demands remain unrestricted.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier HeadFree)
variable [Params] {evidence : FamilyEvidence}
variable {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType}
variable {uc ctor family : Name} {P : ProofShape → Prop}

/-- Only the record-family type key has an operational head requirement.
Function demands preserve that requirement at their result; value keys are true. -/
def TypeRealizes (P : ProofShape → Prop) (e : ProofShape) : Key → Prop
  | .unit | .record => True
  | .fn _ keys result => ∀ a, (∀ key ∈ keys, TypeRealizes P a key) → TypeRealizes P (.app e a) result
  | .type .record => P e
  | .type _ => True
termination_by key => sizeOf key

/-- Every raw term realizes a head-free key, even after an untyped substitution.
This does not assert normalization or native recovery for that term. -/
theorem head_free_realizes (H : HeadFree key) : TypeRealizes P e key := by
  cases key with
  | unit | record => simp only [TypeRealizes]
  | fn A keys result =>
    simp only [HeadFree] at H
    simp only [TypeRealizes]
    exact fun _ _ => head_free_realizes H
  | type key => cases key <;> simp_all only [HeadFree, TypeRealizes]
termination_by sizeOf key

/-- Beta predecessors preserve the type-only interpretation. -/
theorem TypeRealizes.beta_back
    (hP : ∀ {a b}, BetaRed a b → P b → P a) (R : BetaRed e e') (H : TypeRealizes P e' key) :
    TypeRealizes P e key := by
  cases key with
  | unit | record => simp only [TypeRealizes]
  | fn A keys result =>
    simp only [TypeRealizes] at H ⊢
    exact fun a ha => TypeRealizes.beta_back hP (.app R .refl) (H a ha)
  | type key =>
    cases key with
    | unit | fn | type => simp only [TypeRealizes]
    | record =>
      simp only [TypeRealizes] at H ⊢
      exact hP R H
termination_by sizeOf key

/-- The joint observer admits a type-only realization under raw substitution.
No value normalization is used to obtain the operational family-type head. -/
theorem Obs.type_realizes (H : Obs evidence unit record parameter uc ctor family Ω S e key)
    (hP : ∀ {a b}, BetaRed a b → P b → P a)
    (hconst : ∀ a, P (.app (.const family []) a))
    (hfamily : ∀ {Δ e σ}, TypeEquality Δ e (.atom record) → evidence.holds Δ e → P (e.subst σ))
    (hσ : ∀ j key, S j key → TypeRealizes P (σ j) key) :
    TypeRealizes P (e.subst σ) key := by
  induction H generalizing σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [TypeRealizes]
  | record_ctor =>
    simp only [TypeRealizes]
    exact fun _ _ => trivial
  | family =>
    simp only [ProofShape.subst, TypeRealizes]
    exact fun a _ => hconst a
  | record_type HE HR =>
    simpa only [TypeRealizes] using hfamily (σ := σ) HE HR
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
    exact TypeRealizes.beta_back hP (E ▸ (BetaRed.beta (A := A.subst σ))) HB

/-- Native family observations expose their fixed head despite arbitrary
head-free ambient values and arbitrary raw substitution of those values. -/
theorem Obs.head_free_family_readout
    (H : Obs evidence unit record parameter uc ctor family Δ S e (.type .record))
    (hP : ∀ {a b}, BetaRed a b → P b → P a)
    (hconst : ∀ a, P (.app (.const family []) a))
    (hfamily : ∀ {Δ e σ}, TypeEquality Δ e (.atom record) → evidence.holds Δ e → P (e.subst σ))
    (HV : ∀ i key, S i key → HeadFree key) : P (e.subst σ) := by
  simpa only [TypeRealizes] using H.type_realizes (σ := σ) hP hconst hfamily
    (fun i key hi => head_free_realizes (HV i key hi))

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
theorem program_native_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfamily : FamilyPreserves (ErasedStaticStructureEtaExpansionUnion D) evidence)
    (hP : ∀ {a b}, BetaRed a b → P b → P a)
    (hconst : ∀ a, P (.app (.const t []) a))
    (hread : ∀ {Δ e σ}, TypeEquality Δ e (.atom RT) → evidence.holds Δ e → P (e.subst σ))
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (H : Obs evidence U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation evidence U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ T out) :
    P (out.subst σ) := by
  have HE := H.full_compute hi hS Q hTag hF heq hs hfamily huc hc hf HS HV RE
  have HN := HE.full_native hi hS Q hTag hF heq hs hfamily huc hc hf HS HV RN
  exact (HN.full_compute hi hS Q hTag hF heq hs hfamily huc hc hf HS HV RA).head_free_family_readout hP hconst hread HF

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
