import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFamilyImage

/-! # Aligning actual native carriers with selected outputs

The certificate belongs to the recovered type, not to a beta reduct of the
term. Its dependent children substitute using ordinary typing alone. This
lets applications retain native recovery at the original term even when the
source-selected output differs from the actual native carrier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_forall_parts from Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
variable [Params]

/-- A finite alignment between an actual recovered type and a selected raw
output. Family leaves admit whole-domain guard conversion. A Pi wrapper keeps
its written domain and a dependent child; conversions affect only selection. -/
inductive NativeCarrierAlignment (D : PureObservation.Definitions) :
    List VExpr → VExpr → ProofShape → Prop where
  | family : NativeFamilyTree Γ T → NativeCarrierAlignment D Γ T out
  | function : NativeCarrierAlignment D (A :: Γ) B out →
      NativeCarrierAlignment D Γ (.forallE A B) (.forallE (proofErase Γ A) out)
  | convert : NativeCarrierAlignment D Γ T out → Compute (ErasedIotaPrimitive D) out out' →
      NativeCarrierAlignment D Γ T out'

/-- Alignment substitutes independently of native recovery for substitution
images. Only the actual carrier's typing and the erasure agreement are used. -/
theorem NativeCarrierAlignment.subst (H : NativeCarrierAlignment D Γ T out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hT : env.HasType univs Γ T (.sort u)) :
    NativeCarrierAlignment D Γ₀ (T.subst σ) (out.subst τ) := by
  induction H generalizing Γ₀ σ τ u with
  | family HT => exact .family (HT.subst hΓ₀ W hT)
  | function HB ih =>
    obtain ⟨⟨v, hA⟩, _, hB⟩ := hT.forallE_inv henv
    simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES] using
      NativeCarrierAlignment.function
        (ih ⟨hΓ₀, v, hA.subst henv.orderedStrong W hΓ₀⟩
          (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA) hB)
  | convert H R ih =>
    exact .convert (ih hΓ₀ W ES hT) (R.subst (fun H => erased_iota_primitive_subst H))

/-- Every actual carrier in this fragment has a literal sort or Pi head.
No assertion about the selected output's head is needed. -/
theorem NativeCarrierAlignment.shape (H : NativeCarrierAlignment D Γ T out) :
    (∃ u, T = .sort u) ∨ ∃ A B, T = .forallE A B := by
  induction H with
  | family HT => cases HT with
    | sort => exact .inl ⟨_, rfl⟩
    | function => exact .inr ⟨_, _, rfl⟩
  | function => exact .inr ⟨_, _, rfl⟩
  | convert _ _ ih => exact ih

/-- Expose only the carrier certificate. The term and its native recovery
remain unchanged, so this requires no backward recovery through beta. -/
theorem NativeCarrierAlignment.expose (H : NativeCarrierAlignment D Γ T out) :
    NativeFamilyTree Γ T ∨ ∃ A B raw, T = .forallE A B ∧
      NativeCarrierAlignment D (A :: Γ) B raw ∧
      Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ A) raw) out := by
  induction H with
  | family HT => exact .inl HT
  | function HB => exact .inr ⟨_, _, _, rfl, HB, .refl⟩
  | convert _ R ih =>
    rcases ih with HT | ⟨A, B, raw, rfl, HB, RC⟩
    · exact .inl HT
    · exact .inr ⟨A, B, raw, rfl, HB, RC.trans R⟩

/-- A selected Pi exposes an actual native Pi, a dependent aligned child, and
either a family input or forward computation of the actual input to selection. -/
theorem NativeCarrierAlignment.function_parts
    (H : NativeCarrierAlignment D Γ T (.forallE rawA rawB))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ f T)
    (hf : env.HasType univs Γ f (.forallE C E)) :
    ∃ A B, T = .forallE A B ∧ NativeCarrierAlignment D (A :: Γ) B rawB ∧
      (PolymorphicTypeFamily Γ A ∨ Compute (ErasedIotaPrimitive D) (proofErase Γ A) rawA) := by
  rcases H.expose with HT | ⟨A, B, raw, rfl, HB, RC⟩
  · cases HT with
    | sort => exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
    | function HA HB => exact ⟨_, _, rfl, .family HB, .inl HA⟩
  · obtain ⟨_, _, EE, RA, RB⟩ := core_forall_parts RC
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
    exact ⟨A, B, rfl, HB.convert RB, .inr RA⟩

/-- Native recovery at an actual typed carrier, with a finite alignment to the
selected output. There is no footprint restriction on the recovered term. -/
def AlignedNativeRecovery (D : PureObservation.Definitions)
    (Γ : List VExpr) (e : VExpr) (out : ProofShape) : Prop :=
  ∃ T, env.HasType univs Γ e T ∧ NativeCarrierAlignment D Γ T out ∧
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ T)

/-- Previously protected native images enter the new relation at any selected
output. Subsequent constructors do not propagate their footprint condition. -/
theorem NativeFamilyImage.aligned (H : NativeFamilyImage D cut Γ e) :
    AlignedNativeRecovery D Γ e out := by
  obtain ⟨T, ht, HT, R, _⟩ := H
  exact ⟨T, ht, .family HT, R⟩

/-- Selection can compute without changing the actual recovered type. -/
theorem AlignedNativeRecovery.convert (H : AlignedNativeRecovery D Γ e out)
    (RC : Compute (ErasedIotaPrimitive D) out out') : AlignedNativeRecovery D Γ e out' := by
  obtain ⟨T, ht, HT, R⟩ := H
  exact ⟨T, ht, HT.convert RC, R⟩

/-- An aligned body gives native lambda recovery, even if its written domain
is outside the polymorphic family fragment. -/
theorem AlignedNativeRecovery.lam (H : AlignedNativeRecovery D (A :: Γ) b out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hn : ¬ IsProof Γ (.lam A b)) :
    AlignedNativeRecovery D Γ (.lam A b) (.forallE (proofErase Γ A) out) := by
  obtain ⟨B, hb, HB, R⟩ := H
  have ht := HasType.lam hA hb
  obtain ⟨_, hPi⟩ := ht.isType henv hΓ
  refine ⟨_, ht, .function HB, ?_⟩
  rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn,
    show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
  exact .lam R

/-- Application follows the actual dependent codomain and substitutes its
alignment. Native recovery uses no recovery premise for the argument. -/
theorem AlignedNativeRecovery.app (H : AlignedNativeRecovery D Γ f (.forallE rawA rawB))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.app f x) T)
    (hn : ¬ IsProof Γ (.app f x)) :
    AlignedNativeRecovery D Γ (.app f x) (rawB.inst (proofErase Γ x)) := by
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨T', hf', HA, R⟩ := H
  obtain ⟨A, B, rfl, HB, _⟩ := HA.function_parts hΓ hf' hf
  have hx' := argument_at_displayed_domain hΓ hf hf' hx
  obtain ⟨_, hPi⟩ := hf'.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx'
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx'
  refine ⟨B.inst x, HasType.app hf' hx', ?_, ?_⟩
  · simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      HB.subst hΓ W ES hB
  · rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
      proofErase_instN hΓA hx' .zero hB]
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at R
    exact .app R

/-- Consume an argument guard at the selected domain using native recovery at
the original function. Input computation or proved family conversion supplies
the actual-domain guard; no ordinary function-argument comparison is assumed. -/
theorem AlignedNativeRecovery.application_checked
    (H : AlignedNativeRecovery D Γ f (.forallE rawA rawB))
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (EC : proofErase Γ C = rawA)
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false (proofErase Γ f) g)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      rawA (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (.app (proofErase Γ f) (proofErase Γ x)) (.app g (proofErase Γ y)) := by
  obtain ⟨T, ht, HT, R⟩ := H
  obtain ⟨A, B, rfl, _, HA⟩ := HT.function_parts hΓ ht hf
  have HX' : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y) := by
    rcases HA with HA | RC
    · obtain ⟨⟨_, HCA⟩, _, _⟩ := (hf.uniqU henv hΓ ht).forallE_inv henv hΓ
      exact HA.carrier_convert hs hΓ hx hy HCA.toU (by simpa only [EC] using HX)
    · exact .carrierCompute (RC.scoped (fun H => .base H)) HX
  obtain ⟨_, hPi⟩ := ht.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at R
  exact .appCarrier R HF HX'

/-- An aligned type-valued term recovers a literal sort, possibly with a
level different from the source selection. The actual typing is retained. -/
theorem AlignedNativeRecovery.sort (H : AlignedNativeRecovery D Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort v)) :
    ∃ u, env.HasType univs Γ e (.sort u) ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (.sort u) := by
  obtain ⟨T, he, HT, R⟩ := H
  rcases HT.shape with ⟨u, rfl⟩ | ⟨A, B, rfl⟩
  · obtain ⟨_, hsort⟩ := he.isType henv hΓ
    have EE : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hsort)
    exact ⟨u, he, by simpa only [EE] using R⟩
  · exact ((ht.uniqU henv hΓ he).sort_forallE_inv henv hΓ).elim

/-- The aligned fragment cannot supply a structure major: every actual
carrier has a sort or Pi head, excluded by rigid structure head inversion. -/
theorem AlignedNativeRecovery.not_projection (H : AlignedNativeRecovery D Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T) : False := by
  obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  obtain ⟨C, he, HC, _⟩ := H
  have HE := he.uniqU henv hΓ hm.hasType.2
  obtain ⟨_, hC⟩ := he.isType henv hΓ
  rcases HC.shape with ⟨u, rfl⟩ | ⟨A, B, rfl⟩
  · exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi) (HE.typeChain henv hΓ hC)
  · exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi) (HE.typeChain henv hΓ hC)

end Lean4Lean.VEnv.Strengthening
