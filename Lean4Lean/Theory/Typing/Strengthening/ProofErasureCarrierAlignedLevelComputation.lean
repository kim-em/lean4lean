import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCoreJoint

/-! # Explicit universe conversion as erased theory computation

These theory-only primitives change equivalent universe annotations at a sort
or constant. Compatible closure converts a whole structural variant. Typed
binder descent is proved from level congruence; no executable reduction rule,
normalization of terms or carrier-conversion oracle is introduced.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv ProofShape.liftN_sort_inv ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison

namespace ProofShape
/-- Reversing a structural universe variant changes no raw syntax shape. -/
theorem StructuralVariant.symm (H : StructuralVariant a b) : StructuralVariant b a := by
  induction H with
  | refl => exact .refl
  | sort H => exact .sort H.symm
  | const H => exact .const (H.flip.imp (fun _ _ H => H.symm))
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihB => exact .lam ihA ihB
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- Structural universe variation composes without computation. -/
theorem StructuralVariant.trans (H : StructuralVariant a b) (K : StructuralVariant b c) :
    StructuralVariant a c := by
  induction H generalizing c with
  | refl => exact K
  | sort H =>
    cases K with
    | refl => exact .sort H
    | sort K => exact .sort (H.trans K)
  | const H =>
    cases K with
    | refl => exact .const H
    | const K => exact .const (H.trans (fun _ _ _ H K => H.trans K) K)
  | app Hf Hx ihf ihx =>
    cases K with
    | refl => exact .app Hf Hx
    | app Kf Kx => exact .app (ihf Kf) (ihx Kx)
  | proj H ih =>
    cases K with
    | refl => exact .proj H
    | proj K => exact .proj (ih K)
  | lam HA HB ihA ihB =>
    cases K with
    | refl => exact .lam HA HB
    | lam KA KB => exact .lam (ihA KA) (ihB KB)
  | forallE HA HB ihA ihB =>
    cases K with
    | refl => exact .forallE HA HB
    | forallE KA KB => exact .forallE (ihA KA) (ihB KB)

/-- Explicit universe conversion at retained sort and constant nodes. Target
levels must be well formed; source well-formedness comes from actual typing. -/
inductive LevelPrimitive (U : Nat) : ProofShape → ProofShape → Prop where
  | sort : u ≈ v → v.WF U → LevelPrimitive U (.sort u) (.sort v)
  | const : List.Forall₂ (· ≈ ·) ls ls' → (∀ l ∈ ls', l.WF U) →
      LevelPrimitive U (.const c ls) (.const c ls')

/-- Universe conversion changes only equivalent annotations. -/
theorem LevelPrimitive.variant (H : LevelPrimitive U a b) : StructuralVariant a b := by
  cases H with
  | sort H _ => exact .sort H
  | const H _ => exact .const H
end ProofShape

variable [Params]

/-- Universe conversion descends through arbitrary inserted binder blocks.
The lower target is constructed using original level congruence at the same
actual type, including proof-status preservation for retained constants. -/
theorem erased_level_primitive_descent :
    ErasedScopedPrimitiveDescent (fun _ => LevelPrimitive univs) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize ES : (proofErase Γ e).liftN n k = source at R
  cases R with
  | sort HL hw =>
    have ES := ProofShape.liftN_sort_inv ES
    obtain rfl := erase_sort_inv ES
    have HE := ((LEquiv.sort HL hw).defeq henv hΓ ⟨_, ht⟩).of_l henv hΓ ht
    refine ⟨_, HE, ?_⟩
    rw [show proofErase Γ (.sort _) = .sort _ from
      if_neg (not_isProof_of_sort hΓ (HasType.sort hw))]
    rfl
  | const HL hw =>
    rename_i ls ls' c
    have ES := ProofShape.liftN_const_inv ES
    obtain rfl := erase_const_inv ES
    have HE := ((LEquiv.const HL hw).defeq henv hΓ ⟨_, ht⟩).of_l henv hΓ ht
    have hn : ¬ IsProof Γ (.const c ls) := by
      intro H
      have E := proofErase_eq_proof.2 H
      rw [ES] at E
      cases E
    refine ⟨_, HE, ?_⟩
    rw [show proofErase Γ (.const _ _) = .const _ _ from if_neg (mt (isProof_congr hΓ HE).2 hn)]
    rfl

/-- A typed target supplies every level-well-formedness fact needed to compute
from a structural variant. This changes annotations only, including those below
binders and inside dependent projection arguments. -/
theorem proofErase_carrier_aligned_variant_level_compute
    (V : StructuralVariant a (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    Compute (LevelPrimitive univs) a (proofErase Γ e) := by
  generalize Ee : proofErase Γ e = b at V
  induction V generalizing Γ e T with
  | refl => exact .refl
  | sort HL =>
    obtain rfl := erase_sort_inv Ee
    exact .base (.sort HL (ht.sort_inv henv))
  | const HL =>
    obtain rfl := erase_const_inv Ee
    obtain ⟨_, _, hw, _⟩ := ht.const_inv henv hΓ
    exact .base (.const HL hw)
  | app Vf Vx ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf Ef) (ihx hΓ hx Ex)
  | proj Vm ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 Em)
  | lam VA VB ihA ihB | forallE VA VB ihA ihB =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := by
      first | exact erase_lam_inv Ee | exact erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact ht.lam_inv henv hΓ | exact ht.forallE_inv henv
    have RB := ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb Eb
    first | exact .lam (ihA hΓ hA EA) RB | exact .forallE (ihA hΓ hA EA) RB

end Lean4Lean.VEnv.Strengthening
