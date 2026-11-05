import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueObservationReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralHead

/-! # Rigid value histories along universe-ending dependent telescopes

The original argument erasures label the observer. Ordinary domain sorts
classify proof versus retained data slots before any computation; typed
instantiation preserves that classification. No argument native recovery or
type-fork joining is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
/-- A visible result profile stays visible beneath arbitrary telescope slots. -/
theorem argumentProfile_visible (HV : p.Visible) : (argumentProfile slots p).Visible := by
  induction slots with
  | nil => exact HV
  | cons _ _ ih => exact .arrow ih

/-- A literal universe-ending telescope supplies proof/data classifications
for arbitrary labels. Domain sorts, rather than argument syntax, determine them. -/
theorem Fits.of_sort_telescope
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HT : DemandProfile.SortTelescope n T) (hargs : origins.length = n) :
    ∃ slots, slots.map Prod.snd = origins ∧ Fits Γ T (argumentProfile slots .sort) := by
  induction HT generalizing Γ u origins with
  | sort =>
    have E : origins = [] := List.eq_nil_of_length_eq_zero hargs
    subst origins
    exact ⟨[], rfl, ⟨⟨_, hT⟩, _, hT.toU⟩⟩
  | @forallE n B A HT ih =>
    cases origins with
    | nil => simp at hargs
    | cons a origins =>
      obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
      obtain ⟨slots, ES, HB⟩ := ih (Γ := A :: Γ) ⟨hΓ, v, hA⟩ hB (by simpa using hargs)
      by_cases hv : v ≈ .zero
      · have HP : Fits Γ A .proof :=
          (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hv).defeq hA
        exact ⟨(true, a) :: slots, by simp [ES], ⟨⟨_, hT⟩, A, B, hT.toU, HP, HB⟩⟩
      · exact ⟨(false, a) :: slots, by simp [ES], ⟨⟨_, hT⟩, A, B, hT.toU, ⟨v, hA, hv⟩, HB⟩⟩

/-- Actual arguments at the telescope's proof slots erase to proof markers. -/
theorem Fits.proof_slots
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : Fits Γ T (argumentProfile slots .sort))
    (HW : InstForallsC env univs Γ T args result)
    (HE : slots.map Prod.snd = args.map (proofErase Γ)) :
    ∀ s ∈ slots, s.1 = true → s.2 = .proof := by
  induction HW generalizing slots with
  | nil =>
    have : slots = [] := List.eq_nil_of_length_eq_zero (by simpa using congrArg List.length HE)
    subst slots
    simp
  | @cons a A args result B ha HW ih =>
    cases slots with
    | nil => cases HE
    | cons s slots =>
      obtain ⟨Es, Et⟩ := List.cons.inj HE
      obtain ⟨HA, HB⟩ := HP.forallE_inv hΓ
      obtain ⟨u, hA⟩ := HA.isType
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have W := Ctx.InstN.zero.substEq hΓA ha
      have HB' : Fits Γ (B.inst a) (argumentProfile slots .sort) := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
      intro q hq hproof
      rcases List.mem_cons.mp hq with rfl | hq
      · have HAP : env.HasType univs Γ A (.sort .zero) := by simpa [slotProfile, hproof, Fits] using HA
        exact Es.trans (proofErase_eq_proof.mpr ⟨A, ha, HAP⟩)
      · exact ih HB' Et q hq hproof

/-- Applying the original typed arguments supplies all demanded value keys.
Proof slots have no keys, while data slots use reflexive scoped value chains. -/
theorem Obs.telescope
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f T)
    (HP : Fits Γ T (argumentProfile slots .sort))
    (HW : InstForallsC env univs Γ T args result)
    (HE : slots.map Prod.snd = args.map (proofErase Γ))
    (H : Obs D c 0 (proofEraseCtx Γ) S (proofErase Γ f)
      (argumentProfile slots .sort) (argumentKey slots o)) :
    Obs D c 0 (proofEraseCtx Γ) S (proofErase Γ (VExpr.mkApps f args)) .sort o := by
  induction HW generalizing slots f with
  | nil =>
    have : slots = [] := List.eq_nil_of_length_eq_zero (by simpa using congrArg List.length HE)
    subst slots
    exact H
  | @cons a A args result B ha HW ih =>
    cases slots with
    | nil => cases HE
    | cons s slots =>
      obtain ⟨Es, Et⟩ := List.cons.inj HE
      obtain ⟨HA, HB⟩ := HP.forallE_inv hΓ
      obtain ⟨u, hA⟩ := HA.isType
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have W := Ctx.InstN.zero.substEq hΓA ha
      have HB' : Fits Γ (B.inst a) (argumentProfile slots .sort) := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
      have hfa := hf.app ha
      have Efa : proofErase Γ (.app f a) = .app (proofErase Γ f) (proofErase Γ a) :=
        if_neg (HB'.not_isProof hΓ (argumentProfile_visible .sort) hfa)
      have HT : Typing (proofEraseCtx Γ) (.app (proofErase Γ f) (proofErase Γ a))
          (argumentProfile slots .sort) := ⟨Γ, _, _, hΓ, rfl, hfa, HB', Efa⟩
      have HNext : Obs D c 0 (proofEraseCtx Γ) S (proofErase Γ (.app f a))
          (argumentProfile slots .sort) (argumentKey slots o) := by
        rw [Efa]
        apply Obs.app HT H
        intro key hk
        cases hb : s.1 with
        | true => simp [slotKeys, hb] at hk
        | false =>
          have EK : key = .value s.2 := by simpa [slotKeys, hb] using hk
          subst key
          apply Obs.value ⟨Γ, a, A, hΓ, rfl, ha, by simpa [slotProfile, hb] using HA, rfl⟩
          rw [ProofShape.liftN_zero, Es]
          exact ScopedValueChain.of_typed hΓ (.refl ha)
      exact ih hfa HB' Et HNext

/-- Every saturated rigid constant at a universe-ending telescope has an
initial closed head observation labelled by its actual argument erasures. -/
theorem initial_rigid_value_observation
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.const c ls) T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result) :
    Obs D c 0 (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (VExpr.mkApps (.const c ls) args)) .sort (.head (args.map (proofErase Γ))) := by
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  obtain ⟨slots, ES, HP⟩ := Fits.of_sort_telescope hΓ hT HT
    (show (args.map (proofErase Γ)).length = args.length from List.length_map ..)
  have E : proofErase Γ (.const c ls) = .const c ls :=
    if_neg (HP.not_isProof hΓ (argumentProfile_visible .sort) hf)
  have H : Obs D c 0 (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ (.const c ls))
      (argumentProfile slots .sort) (spineKey slots) := by
    rw [E]
    exact .const ⟨Γ, _, T, hΓ, rfl, hf, HP, E⟩ (HP.proof_slots hΓ HW ES)
  have HR := H.telescope hΓ hf HP HW ES
  simpa only [spineKey, ES] using HR

/-- Full structure/function-eta computation retains the rigid head and a scoped
value history for every original argument. Arbitrary dependent data, function
arguments and proof slots are covered; forward argument origins are not claimed. -/
theorem static_structure_rigid_value_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.const c ls) T)
    (HT : DemandProfile.SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const c ls) args)) out) :
    ∃ ls' outputs, BetaRed out (ProofShape.mkApps (.const c ls') outputs) ∧
      List.Forall₂ (ScopedValueChain D (proofEraseCtx Γ)) (args.map (proofErase Γ)) outputs :=
  ((initial_rigid_value_observation hΓ hf HT HW).static_structure_union heq hs hc hD R
    (fun _ _ _ h => h.elim)).head_readout heq hs

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
