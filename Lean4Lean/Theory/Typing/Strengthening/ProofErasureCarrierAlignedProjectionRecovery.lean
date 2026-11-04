import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNullaryExposure

/-! # Native projection recovery with retained universe alignment

The native type of a major may compute to a different universe instance from
its assigned nullary family. Exposure retains the universe comparison, and the
dependent projection recipe then retains a structural comparison with its
source recipe. The recovered field type need not equal the assigned syntax.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Native recovery aligned with a nullary assigned family exposes an actual
family instance and retains both its native certificate and universe relation.
Only computation is used to change the native recovery output. -/
theorem proofErase_carrier_aligned_recovered_nullary_instance
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family ls))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.const family ls))) :
    ∃ ls', env.HasType univs Γ m (.const family ls') ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m) (.const family ls') ∧
      (∀ l ∈ ls', l.WF univs) ∧ List.Forall₂ (· ≈ ·) ls ls' := by
  obtain ⟨A, hmA, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hm rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using R)
  simp only [List.length_nil, ProofShape.liftN_zero] at EA
  obtain ⟨u, hfamily⟩ := hm.isType henv hΓ
  obtain ⟨v, hA⟩ := hmA.isType henv hΓ
  have Efamily : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hfamily)
  obtain ⟨ls', RA, HL⟩ := proofErase_carrier_aligned_nullary_levels_exposure hstep hn hΓ
    hfamily hA (by simpa only [EA] using H.symm) Efamily
  obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl RA
  obtain rfl := erase_const_inv EA'
  refine ⟨ls', hmA.defeqU_r henv hΓ ⟨_, HA⟩, ?_, ?_, HL⟩
  · exact R.convert (by simpa only [EA] using RA)
  · exact (StructureReplay.family_instance_levels hi hΓ HA.hasType.2).1

/-- A retained projection recovers a native field type structurally aligned
with the source constructor's entire dependent recipe. The source and selected
universe instances may differ literally, and earlier fields may occur in the
template. An initial native recovery and alignment for the major remain inputs. -/
theorem proofErase_carrier_aligned_native_projection_recipe
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs family info ls doms result)
    (hj : info.nparams + j < doms.length)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family ls))
    (ht : env.HasType univs Γ (.proj family j m) F)
    (hproj : ¬ IsProof Γ (.proj family j m))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.const family ls))) :
    ∃ G, env.HasType univs Γ (.proj family j m) G ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.proj family j m)) (proofErase Γ G) ∧
      StructuralVariant (projectionType family info doms j hj [] (proofErase Γ m)) (proofErase Γ G) := by
  obtain ⟨ls', hm', RM, hw', HL⟩ := proofErase_carrier_aligned_recovered_nullary_instance
    hstep hn hi hΓ hm R H
  obtain ⟨_, hfamily⟩ := hm.isType henv hΓ
  have hw := (StructureReplay.family_instance_levels hi hΓ hfamily).1
  obtain ⟨doms', result', HT'⟩ := projection_telescope_exists hi hw'
  obtain ⟨hj', G, hG, EG⟩ := proofErase_projection_at_recovered_family
    hΓ hi HT' ht hproj (args := []) hm'
  have EG' : proofErase Γ G = projectionType family info doms' j hj' [] (proofErase Γ m) := by
    simpa only [projectionType, List.take_nil, List.map_nil] using EG
  refine ⟨G, hG, ?_, ?_⟩
  · rw [show proofErase Γ (.proj family j m) = .proj family j (proofErase Γ m) from if_neg hproj, EG']
    exact .proj hi HT' hj' (args := []) (by simp [hp, hx]) RM
  · rw [EG']
    exact proofErase_carrier_aligned_projection_type_variant HT HT' hw hw' HL hj hj'

/-- When the assigned field is already expressed by its source projection
recipe, native projection recovery retains an inferred-mode comparison to it.
This output is suitable as the input alignment for a further projection. -/
theorem proofErase_carrier_aligned_native_projection
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs family info ls doms result)
    (hj : info.nparams + j < doms.length)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family ls))
    (ht : env.HasType univs Γ (.proj family j m) F)
    (hproj : ¬ IsProof Γ (.proj family j m))
    (EF : proofErase Γ F = projectionType family info doms j hj [] (proofErase Γ m))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.const family ls))) :
    ∃ G, env.HasType univs Γ (.proj family j m) G ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.proj family j m)) (proofErase Γ G) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ G) (proofErase Γ F) := by
  obtain ⟨G, hG, RG, HV⟩ := proofErase_carrier_aligned_native_projection_recipe
    hstep hn hi hp hx HT hj hΓ hm ht hproj R H
  rw [← EF] at HV
  exact ⟨G, hG, RG, .computed (.symm HV.computed)⟩

/-- The full recovered-carrier union supplies the primitive interface for
native projection recovery. Projection registration itself supplies family
rigidity; declarations must leave that family head unexpanded. -/
theorem proofErase_carrier_aligned_union_native_projection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (HT : ProjTele env univs family info ls doms result)
    (hj : info.nparams + j < doms.length)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family ls))
    (ht : env.HasType univs Γ (.proj family j m) F)
    (hproj : ¬ IsProof Γ (.proj family j m))
    (EF : proofErase Γ F = projectionType family info doms j hj [] (proofErase Γ m))
    (R : ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ m) T)
    (H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode T (proofErase Γ (.const family ls))) :
    ∃ G, env.HasType univs Γ (.proj family j m) G ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ (.proj family j m)) (proofErase Γ G) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false (proofErase Γ G) (proofErase Γ F) :=
  proofErase_carrier_aligned_native_projection (erased_carrier_recovered_union_descent heq hs)
    (fun H => erased_carrier_recovered_union_no_rigid heq (henv.projectionRigid hi) hD H rfl)
    hi hp hx HT hj hΓ hm ht hproj EF R H

end Lean4Lean.VEnv.Strengthening
