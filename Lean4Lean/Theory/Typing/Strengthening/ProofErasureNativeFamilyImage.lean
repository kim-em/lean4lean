import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProtectedNativeRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolymorphicTypeFamily

/-! # Protected native images accepting higher-order family arguments

The function's actual native type is retained separately from the source's
selected carrier. A finite tree certifies each actual input for whole-carrier
conversion. Exact recovery then licenses application without promoting a
function argument's guard to ordinary comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A finite type-valued function tree. Inputs have the already proved
substitution-stable family readout; codomains retain dependent child trees. -/
inductive NativeFamilyTree : List VExpr → VExpr → Prop where
  | sort : NativeFamilyTree Γ (.sort u)
  | function : PolymorphicTypeFamily Γ A → NativeFamilyTree (A :: Γ) B →
      NativeFamilyTree Γ (.forallE A B)

/-- Actual typed substitution preserves every input and dependent result tree. -/
theorem NativeFamilyTree.subst (H : NativeFamilyTree Γ T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v)) : NativeFamilyTree Γ₀ (T.subst σ) := by
  induction H generalizing Γ₀ σ v with
  | sort => exact .sort
  | function HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .function (HA.subst hΓ₀ W hA)
      (ih ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩ (W.lift henv.ordered hA) hB)

/-- A typed function tree with exact native recovery at its own actual type.
The footprint protects queried variables from local beta substitution. -/
def NativeFamilyImage (D : PureObservation.Definitions) (cut : Nat)
    (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ T, env.HasType univs Γ e T ∧ NativeFamilyTree Γ T ∧
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ T) ∧
    RecoveryHeadsAbove cut (proofErase Γ e)

/-- A retained protected variable has exact native recovery at its lookup type. -/
theorem NativeFamilyImage.bvar
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i T)
    (HT : NativeFamilyTree Γ T) (hi : cut ≤ i) (hn : ¬ IsProof Γ (.bvar i)) :
    NativeFamilyImage D cut Γ (.bvar i) := by
  refine ⟨T, HasType.bvar hl, HT, proofErase_scoped_lookup_recovery hΓ hl hn .refl, ?_⟩
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
  exact hi

/-- A protected interpreted substitution retains the image's actual native
carrier, its finite family tree, and its recovery footprint. -/
theorem NativeFamilyImage.subst (H : NativeFamilyImage D cut Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WP : ProtectedOracleSubstitution cut cut' (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) :
    NativeFamilyImage D cut' Γ₀ (e.subst σ) := by
  obtain ⟨T, ht, HT, R, HH⟩ := H
  obtain ⟨u, hT⟩ := ht.isType henv W.wf
  refine ⟨T.subst σ, ht.subst henv.orderedStrong W hΓ₀, HT.subst hΓ₀ W hT, ?_, ?_⟩
  · simpa only [proofErase_subst_with hΓ₀ W ht ES, proofErase_subst_with hΓ₀ W hT ES] using
      R.subst_protected (Step' := ErasedJointStage D 0) (fun H _ => erased_iota_primitive_subst H) HH WP
  · simpa only [proofErase_subst_with hΓ₀ W ht ES] using HH.subst WP

/-- Local beta contraction preserves the native image without assuming any
native recovery for the substituted argument. -/
theorem NativeFamilyImage.inst (H : NativeFamilyImage D (cut + 1) (A :: Γ) e)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A) :
    NativeFamilyImage D cut Γ (e.inst p) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  have WI : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ p)) := ContextSubstitution.of_typed hΓ W ES
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    H.subst hΓ W ES (ProtectedOracleSubstitution.one WI)

/-- A function occurrence exposes an actual native Pi with a certified input
and a dependent result tree. It need not recover the source's selected Pi. -/
theorem NativeFamilyImage.function (H : NativeFamilyImage D cut Γ f)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E)) :
    ∃ A B, env.HasType univs Γ f (.forallE A B) ∧ PolymorphicTypeFamily Γ A ∧
      NativeFamilyTree (A :: Γ) B ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ f)
        (proofErase Γ (.forallE A B)) ∧ RecoveryHeadsAbove cut (proofErase Γ f) := by
  obtain ⟨T, ht, HT, R, HH⟩ := H
  cases HT with
  | sort => exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  | function HA HB => exact ⟨_, _, ht, HA, HB, R, HH⟩

/-- Applying a native image follows its dependent child tree. Recovery never
queries the argument's type; only its ordinary actual typing is used. -/
theorem NativeFamilyImage.application (H : NativeFamilyImage D cut Γ f)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app f x) T)
    (hn : ¬ IsProof Γ (.app f x)) : NativeFamilyImage D cut Γ (.app f x) := by
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨A, B, hf', HA, HB, R, HH⟩ := H.function hΓ hf
  have hx' := argument_at_displayed_domain hΓ hf hf' hx
  obtain ⟨_, hPi⟩ := hf'.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx'
  refine ⟨B.inst x, HasType.app hf' hx', ?_, ?_, ?_⟩
  · simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W hB
  · rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
      proofErase_instN hΓA hx' .zero hB]
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at R
    exact .app R
  · rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn]
    exact HH

/-- Reindex the whole argument guard to the image's own recovered domain, then
use native application. No ordinary comparison promotion is assumed or needed. -/
theorem NativeFamilyImage.application_checked (H : NativeFamilyImage D cut Γ f)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (EC : proofErase Γ C = raw)
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false (proofErase Γ f) g)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      raw (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (.app (proofErase Γ f) (proofErase Γ x)) (.app g (proofErase Γ y)) := by
  obtain ⟨A, B, hf', HA, HB, R, HH⟩ := H.function hΓ hf
  obtain ⟨⟨_, HCA⟩, _, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
  have HX' := HA.carrier_convert hs hΓ hx hy HCA.toU (by simpa only [EC] using HX)
  obtain ⟨_, hPi⟩ := hf'.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at R
  exact .appCarrier R HF HX'

end Lean4Lean.VEnv.Strengthening
