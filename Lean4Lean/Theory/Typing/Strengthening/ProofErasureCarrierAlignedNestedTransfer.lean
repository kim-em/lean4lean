import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedFieldTransfer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelVariants

/-! # Nested structural subsingleton fields across universe variants

A retained field may be checked by its carrier rather than by an ordinary
comparison of the projections. Structural subsingleton carriers, including
dependent functions into empty structures, survive universe variants of the
complete projection recipe. Ordinary checked fields can be mixed with them.
Arbitrary computed or recursively nested carrier guards are not covered here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

private theorem variant_app_inv (H : StructuralVariant (.app f x) b) :
    ∃ g y, b = .app g y ∧ StructuralVariant f g ∧ StructuralVariant x y := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app HF HX => exact ⟨_, _, rfl, HF, HX⟩

private theorem variant_constant_spine (H : StructuralVariant (ProofShape.mkApps (.const c ls) args) b) :
    ∃ ls' args', b = ProofShape.mkApps (.const c ls') args' ∧ args.length = args'.length := by
  induction args using List.snoc_induction generalizing b with
  | nil =>
    cases H with
    | refl => exact ⟨_, [], rfl, rfl⟩
    | const HL => exact ⟨_, [], rfl, rfl⟩
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at H
    obtain ⟨g, y, rfl, HF, _⟩ := variant_app_inv H
    obtain ⟨ls', args', rfl, hlen⟩ := ih HF
    exact ⟨ls', args' ++ [y], by simp [ProofShape.mkApps_snoc], by simp [hlen]⟩

variable [Params]

/-- Structural variants preserve the static subsingleton carrier grammar,
including arbitrary parameters and dependent function codomains. -/
theorem ProofShape.SubsingletonCarrier.variant
    (H : SubsingletonCarrier A) (V : StructuralVariant A B) : SubsingletonCarrier B := by
  induction H generalizing B with
  | unit hi hx hf hp =>
    obtain ⟨ls', ps', rfl, hlen⟩ := variant_constant_spine V
    exact .unit hi hx hf (hlen.symm.trans hp)
  | forallE H ih =>
    cases V with
    | refl => exact .forallE H
    | forallE VA VB => exact .forallE (ih VB)

/-- A nested guard changes universe instances by transporting each dependent
field recipe. A retained field may use an ordinary comparison or a structural
subsingleton carrier; these alternatives can vary from field to field. -/
theorem ProofShape.ComputedJointCarrierGuard.nested_subsingletons_congr_levels
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (HT : ProjTele env univs family info ls doms result)
    (HT' : ProjTele env univs family info ls' doms' result')
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step Δ true (.proj family i a) (.proj family i b) ∨
      SubsingletonCarrier (projectionType family info doms i (by have := HT.numFields; omega) ps a)) :
    ComputedJointCarrierGuard Step Δ (ProofShape.mkApps (.const family ls') ps) a b := by
  have hadm' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
    rcases hadm with hpos | hproof
    · exact .inl (hpos.of_equiv (VLevel.inst_congr rfl he))
    · exact .inr (hproof.level_congr henv hi hw hw' hl he)
  apply ComputedJointCheck.carrierNested hi hx hp hadm' HT'
  intro i hj hn
  rcases H i hj (fun Hproof => hn (Hproof.congr_levels hi hw hw' hl he)) with HC | HS
  · exact .carrierChecked HC
  · apply ComputedJointCheck.carrierSubsingleton
    exact HS.variant (proofErase_carrier_aligned_projection_type_variant HT HT' hw hw' he _ _)

/-- Aligned nullary exposure transfers mixed checked/subsingleton field guards
to a selected carrier, including a carrier reached only after computation.
The source telescope and field certificates are reused through level transport. -/
theorem proofErase_carrier_aligned_nullary_nested_target
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : info.nparams = 0)
    (HT : ProjTele env univs family info ls doms result)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y) ∨
      SubsingletonCarrier (projectionType family info doms i (by have := HT.numFields; omega) [] x)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ b) x y := by
  obtain ⟨ls', R, HL⟩ := proofErase_carrier_aligned_nullary_levels_exposure hstep hn hΓ ha hb H Ea
  obtain ⟨b', HB, Eb'⟩ := proofErase_scoped_compute_realize hstep hΓ hb rfl rfl R
  obtain rfl := erase_const_inv Ea
  obtain rfl := erase_const_inv Eb'
  have hsource := StructureReplay.family_instance_levels hi hΓ ha
  have htarget := StructureReplay.family_instance_levels hi hΓ HB.hasType.2
  obtain ⟨doms', result', HT'⟩ := projection_telescope_exists hi htarget.1
  exact .carrierCompute R (ComputedJointCarrierGuard.nested_subsingletons_congr_levels
    hi hx (ps := []) hp.symm HT HT' hsource.1 htarget.1 hsource.2 HL hadm Hfields)

/-- Native Pi selection now supports nested structural-subsingleton fields.
The selected domain, its inferred comparison and its argument guard are returned
together; no recovery at the exact assigned domain is requested. -/
theorem proofErase_carrier_aligned_recovered_nullary_nested_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : info.nparams = 0)
    (HT : ProjTele env univs family info ls doms result)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y) ∨
      SubsingletonCarrier (projectionType family info doms i (by have := HT.numFields; omega) [] x)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ D) x y := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_carrier_aligned_recovered_pi_domain hstep hhead hΓ hf R H
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hPi'⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi'.forallE_inv henv
  exact ⟨D, C, hfDC, RD, HD,
    proofErase_carrier_aligned_nullary_nested_target hstep hn hi hx hp HT hΓ hA hD HD EA hadm Hfields⟩

/-- All primitive interfaces for mixed checked/subsingleton nested fields are
discharged at the full recovered-carrier union. The initial native function
recovery and type alignment remain explicit. -/
theorem proofErase_carrier_aligned_union_nullary_nested_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0) (hp : info.nparams = 0)
    (HT : ProjTele env univs family info ls doms result)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (Hfields : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      ComputedJointCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true (.proj family i x) (.proj family i y) ∨
      SubsingletonCarrier (projectionType family info doms i (by have := HT.numFields; omega) [] x)) :
    ∃ A' C, env.HasType univs Γ f (.forallE A' C) ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ A') (proofErase (A' :: Γ) C)) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ A') ∧
      ComputedJointCarrierGuard (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A') x y :=
  proofErase_carrier_aligned_recovered_nullary_nested_guard
    (erased_carrier_recovered_union_descent heq hs) erased_carrier_recovered_union_head
    (fun H => erased_carrier_recovered_union_no_rigid heq (henv.projectionRigid hi) hD H rfl)
    hi hx hp HT hΓ hf R H EA hadm Hfields

end Lean4Lean.VEnv.Strengthening
