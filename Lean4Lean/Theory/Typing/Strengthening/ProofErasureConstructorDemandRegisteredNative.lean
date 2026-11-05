import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandStructure

/-! # Registered headers discharge the native induction premises

The family-to-universe header uses ordinary equality. The constructor header is
observed from its stored declaration, computed with the empty valuation, then
weakened to the caller's demands. Thus no arbitrary native-header premise is
left when primitive observation preservation is available at a finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (.const s []) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hTag hF

/-- Any realized raw context types the registered constructor at its closed
simple control arrow. The arbitrary source is used only to realize the context. -/
theorem constructor_typing (H : HeterogeneousControl.ControlTyping Δ e controlTy) :
    HeterogeneousControl.ControlTyping Δ (.const c []) (.arrow (.atom U) (.atom RT)) := by
  obtain ⟨Γ, _, hΓ, EΓ, _, _⟩ := H
  have hc : env.HasType univs Γ (.const c [])
      (HeterogeneousControl.ControlType.arrow (.atom U) (.atom RT)).expr :=
    (registered_unit_constructor_simple_arrow hi hS hTag hF).weak0 henv.ordered
  exact ⟨Γ, _, hΓ, EΓ, hc, if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hc)⟩

/-- At the registered unit/record signature, primitive preservation supplies
complete native observation preservation. The constant-header obligations are
discharged here, including arbitrary converted family headers. -/
theorem Obs.registered_native
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ S a b key}, Step Δ a b → S.Typed U RT Δ → Valuation U RT uc c t Δ S →
      Obs U RT uc c t Δ S a key → Obs U RT uc c t Δ S b key)
    (H : Obs U RT uc c t Δ S source key)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT uc c t Δ S)
    (RN : ScopedTypeRecovery Step Δ source out) : Obs U RT uc c t Δ S out (.type key) := by
  have hcomp : ∀ {Δ S a b key}, S.Typed U RT Δ → Valuation U RT uc c t Δ S →
      ScopedCompute Step Δ a b → Obs U RT uc c t Δ S a (.type key) → Obs U RT uc c t Δ S b (.type key) := by
    intro Δ S a b key HS HV R H
    exact H.compute hstep hroot R HS HV
  have HC : ∀ {Δ S A},
      HeterogeneousControl.ControlTyping Δ (.const c []) (.arrow (.atom U) (.atom RT)) →
      ScopedTypeRecovery Step Δ (.const c []) A →
      Obs U RT uc c t Δ S A (.type (.fn (.atom U) [.unit] .record)) := by
    intro Δ S A HT RN
    obtain ⟨Γ, _, hΓ, EΓ, _, _⟩ := HT
    have HN : Obs U RT uc c t (proofEraseCtx Γ) (fun _ _ => False) A
        (.type (.fn (.atom U) [.unit] .record)) :=
      registered_constructor_native_of_type_preservation hi hS hTag hF hΓ
        (fun R H => hcomp (by intro i key h; cases h) (by intro i key h; cases h) R H)
        (by simpa only [EΓ] using RN)
    have W : ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ) Subst.id :=
      AtomicControl.control_context_substitution (.refl hΓ)
    have HM := HN.rename W (T := S) (fun i key h => h.elim)
    simpa only [ProofShape.subst_id, EΓ] using HM
  exact H.native_of_type_preservation hstep hcomp HC HS HV RN

/-- Actual structure expansion preserves the observer once the previous
stage's primitive preservation supplies its selected native parameter. -/
theorem Obs.registered_structure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ S a b key}, Step Δ a b → S.Typed U RT Δ → Valuation U RT uc c t Δ S →
      Obs U RT uc c t Δ S a key → Obs U RT uc c t Δ S b key)
    (H : Obs U RT uc c t Δ S source key)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT uc c t Δ S)
    (R : NativeMaskedStructureExpansion Step Δ source out) : Obs U RT uc c t Δ S out key := by
  have HT := H.typing.compute (erased_nativeMaskedStructureExpansion_descent hstep) (.base R)
  cases key with
  | unit =>
    obtain rfl := unit_structure_output hi hS hstep H.typing R
    exact .unit_ctor HT
  | record =>
    obtain ⟨p, RN, rfl⟩ := record_structure_output hi hTag hF hstep H.typing R
    have HP := (H.registered_native hi hS hTag hF hstep hroot HS HV RN).family_parameter
    exact .app HT (.record_ctor (constructor_typing hi hS hTag hF H.typing)) (by
      intro key hk; obtain rfl := List.mem_singleton.1 hk; exact HP)
  | fn A keys result => exact (no_structure_control hstep H.typing (.inl ⟨_, _, rfl⟩) R).elim
  | type key => exact (no_structure_control hstep H.typing (.inr ⟨_, rfl⟩) R).elim

/-- The actual native identity guard supplies its required annotation demand
from the preceding stage's observation preservation. -/
theorem Obs.registered_identity
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ S a b key}, Step Δ a b → S.Typed U RT Δ → Valuation U RT uc c t Δ S →
      Obs U RT uc c t Δ S a key → Obs U RT uc c t Δ S b key)
    (H : Obs U RT uc c t Δ S source key)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT uc c t Δ S)
    (R : NativeIdentityExpansion Step Δ source out) : Obs U RT uc c t Δ S out key := by
  cases R with
  | intro RN =>
    exact H.identity_of_type_observation hstep RN
      (H.registered_native hi hS hTag hF hstep hroot HS HV RN)

/-- Function eta obtains the input annotation demands from its actual native
Pi guard. Unit, record and type keys exclude function eta by ordinary typing. -/
theorem Obs.registered_eta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ S a b key}, Step Δ a b → S.Typed U RT Δ → Valuation U RT uc c t Δ S →
      Obs U RT uc c t Δ S a key → Obs U RT uc c t Δ S b key)
    (H : Obs U RT uc c t Δ S source key)
    (HS : S.Typed U RT Δ) (HV : Valuation U RT uc c t Δ S)
    (R : NativeEtaExpansion Step Δ source out) : Obs U RT uc c t Δ S out key := by
  cases key with
  | unit | record => exact (H.typing.no_eta_atom hstep R).elim
  | type key => exact (H.typing.no_eta_sort hstep R).elim
  | fn A keys result =>
    cases R with
    | intro RN SD =>
      have E : etaArgument _ = .bvar 0 := if_neg (H.typing.eta_domain_ne_zero hstep RN SD)
      rw [E]
      exact H.eta_of_type_observation hstep RN SD
        (H.registered_native hi hS hTag hF hstep hroot HS HV RN)

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
