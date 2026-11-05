import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordFunctionInput

/-! # Actual lookup from independently observed annotations

An annotation seed combines ordinary carrier equality with an operational type
observation having no free demands. It can therefore be checked before the
variable whose native oracle it will justify is added to the demand set.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

namespace ConstructorDemand

/-- An erased annotation equality applies to any actual typed representative
in the same erased context. Reflection is used only between equal erasures of
types, whose sort typings ensure that neither is a proof. -/
theorem TypeEquality.actual (H : TypeEquality Δ e domain)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (hA : env.HasType univs Γ A (.sort u)) (EA : proofErase Γ A = e) :
    env.IsDefEq univs Γ A domain.expr (.sort domain.level) := by
  obtain ⟨Γ₀, A₀, hΓ₀, EΓ₀, HE, E₀⟩ := H
  have W := proofEraseCtx_defeq hΓ₀ hΓ (EΓ₀.trans EΓ.symm)
  have HE' := HE.defeqDFC henv W
  have E₀' : proofErase Γ A₀ = e := (proofErase_defeqCtx hΓ₀ W HE.hasType.1).symm.trans E₀
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ hA HE'.hasType.1 (EA.trans E₀'.symm)).2
    (not_isProof_of_sort hΓ hA)
  exact ((HN.defeq hΓ).of_r henv hΓ HE'.hasType.1).trans HE'

/-- A carrier equality at the actual lookup annotation types the retained raw
variable. No native-type coverage or directed annotation exposure is assumed. -/
theorem TypeEquality.lookup_control
    (H : TypeEquality (proofEraseCtx Γ) (proofErase Γ A) domain)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A) :
    HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar i) domain := by
  have hx : env.HasType univs Γ (.bvar i) A := .bvar hl
  obtain ⟨_, hA⟩ := hx.isType henv hΓ
  have ht := (H.actual hΓ rfl hA rfl).defeq hx
  exact ⟨Γ, _, hΓ, rfl, ht, if_neg (HeterogeneousControl.ControlType.not_isProof hΓ ht)⟩

end ConstructorDemand

namespace IgnoredRecordDemand
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
variable {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType}
variable {uc ctor family : Name}

/-- Enlarging free demands preserves all existing value and type observations. -/
theorem Obs.weaken_demands (H : Obs unit record parameter uc ctor family Δ S e key)
    (hST : ∀ i key, S i key → T i key) : Obs unit record parameter uc ctor family Δ T e key := by
  simpa only [ProofShape.subst_id] using
    H.rename ContextRenaming.identity.interpretation (fun i key hi => ⟨i, rfl, hST i key hi⟩)

/-- Independently checked annotation evidence. The empty free-demand set
prevents the annotation's native proof from assuming the variable it introduces. -/
def AnnotationSeed (unit record : AtomicControl.Atom) (parameter : HeterogeneousControl.ControlType)
    (uc ctor family : Name) (Δ : List ProofShape) (A : ProofShape) (key : Key) : Prop :=
  TypeEquality Δ A (key.control unit record) ∧
    Obs unit record parameter uc ctor family Δ (fun _ _ => False) A (.type key)

/-- One demanded free variable, at an arbitrary finite value key. -/
def ObservedInput (i : Nat) (key : Key) : Sets := fun j k => j = i ∧ k = key

/-- Materialize a seed at an actual lookup. The resulting valuation observes
the exact context oracle, and requires no recursive assumption about that oracle. -/
theorem AnnotationSeed.lookup
    (H : AnnotationSeed unit record parameter uc ctor family (proofEraseCtx Γ) (proofErase Γ A) key)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A) :
    (ObservedInput i key).Typed unit record (proofEraseCtx Γ) ∧
      Valuation unit record parameter uc ctor family (proofEraseCtx Γ) (ObservedInput i key) ∧
      Obs unit record parameter uc ctor family (proofEraseCtx Γ) (ObservedInput i key) (.bvar i) key := by
  have HT := H.1.lookup_control hΓ hl
  have HK : key.Valid unit record := by simpa only [Key.Valid] using H.2.valid
  refine ⟨?_, ?_, .var HT HK ⟨rfl, rfl⟩⟩
  · rintro j k ⟨rfl, rfl⟩; exact HT
  · rintro j k ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    exact E ▸ H.2.weaken_demands (by intro j k h; cases h)

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

/-- A complete computation history preserves independently checked annotation
evidence. In particular it may change the written head of the future oracle. -/
theorem AnnotationSeed.full_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (H : AnnotationSeed U RT (Q.control U) uc c t Δ A key)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ A B) :
    AnnotationSeed U RT (Q.control U) uc c t Δ B key :=
  ⟨H.1.compute (erased_static_structure_eta_expansion_union_descent heq hs) R,
    H.2.full_compute hi hS Q hTag hF heq hs huc hc hf
      (by intro i key h; cases h) (by intro i key h; cases h) R⟩

end IgnoredRecordDemand
end Lean4Lean.VEnv.Strengthening
