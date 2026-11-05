import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionSelected

/-! # Whole-family return from one selected closed header

The native premise is one actual closed exposure, not an assigned-type coverage
principle. All future contexts and all whole-application computation paths are
handled by the proof. The common output uses the exposed annotation unchanged.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- One native exposure of the closed family suffices for every whole-family
continuation at a unit-function lookup to return to the same selected annotation.
The family is ordinarily assigned (Unit -> Unit) -> Sort v; neither its stored
header nor the selected annotation must literally use Unit. -/
theorem family_return_selected
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hf₀ : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam A (.const info.ctorName []))) := by
  letI := AtomicControl.Atom.ofRigid (henv.projectionRigid hi) hS
  let V : AtomicControl.Sets := fun j t o => j = i ∧ t = .arrow .atom .atom ∧ o = .app [] .pi
  have hx₀ : env.HasType univs Γ (.bvar i) (.forallE (.const s []) (.const s [])) := .bvar hl
  have EX : proofErase Γ (.bvar i) = .bvar i :=
    if_neg (AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓ hx₀)
  have HX : AtomicControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.arrow .atom .atom) := ⟨Γ, _, hΓ, rfl, hx₀, EX⟩
  have hf : env.HasType univs Γ (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)) := hf₀.weak0 henv.ordered
  have EF : proofErase Γ (.const r []) = .const r [] := if_neg (not_isProof_function_to_sort hΓ hf)
  have ht : env.HasType univs Γ (.app (.const r []) (.bvar i)) (.sort v) := .app hf hx₀
  have EE : proofErase Γ (.app (.const r []) (.bvar i)) = .app (.const r []) (.bvar i) := by
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓ ht), EF, EX]
  have HV : V.Typed (proofEraseCtx Γ) := by rintro j t o ⟨rfl, rfl, rfl⟩; exact HX
  have HK : AtomicControl.Demand (.arrow .atom .atom) (.app [] .pi) :=
    .fn (by simp) .atom
  have HO : Obs info.ctorName r v (proofEraseCtx Γ) V
      (.app (.const r []) (.bvar i)) (.sort v) .pi := by
    refine .app ⟨Γ, _, hΓ, rfl, ht, EE⟩ (.rigid ⟨Γ, _, hΓ, rfl, hf, EF⟩) ?_
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var HX HK ⟨rfl, rfl, rfl⟩
  have H := HO.static_structure_union heq hs hi hz rfl (henv.projectionCtorRigid hi) hD hr hDr R HV
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (.forallE (.const s []) (.const s [])) := by
    have RR := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
      hΓ hl (AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓ hx₀) .refl
    rwa [EX, unit_arrow_erasure hS hΓ] at RR
  obtain ⟨HC, HA⟩ := closed_selected_header heq hs hf₀ RF
  have HR := H.world_computes (union_world_rename heq hs) (fun t τ => selectedCanonical_subst HA t)
    (target := selectedCanonical info.ctorName r A) rfl
    (fun HF => family_world_selected heq hs HF (selected_family_native_world heq hs HC RF))
    ContextRenaming.identity.interpretation (σ := Subst.id) (by
      rintro j t key ⟨rfl, rfl, rfl⟩
      exact native_unit_function_world_of_target heq hs hi hp hx hz RN rfl)
  simpa only [ProofShape.subst_id, WorldComputes, selectedCanonical] using HR

/-- Independent whole-family paths share the output fixed by one selected
closed header. No alignment between their intermediate annotations is needed. -/
theorem family_join_selected
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hf₀ : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hli : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (hlj : Lookup Γ j (.forallE (.const s []) (.const s [])))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar i)) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar j)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.lam A (.const info.ctorName []))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.lam A (.const info.ctorName []))) :=
  ⟨family_return_selected heq hs hi hp hx hz hD hS hr hDr hf₀ RF hΓ hli RL,
    family_return_selected heq hs hi hp hx hz hD hS hr hDr hf₀ RF hΓ hlj RR⟩

/-- An instantiated stored header with two displayed Pis supplies a native
exposure directly. Its domain and codomain are arbitrary actual expressions;
ordinary assigned typing will enforce the needed conversions separately. -/
theorem nested_stored_family_native
    (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (.forallE A₀ B₀) C₀) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE (proofErase [] A₀) (proofErase [A₀] B₀))
        (proofErase [.forallE A₀ B₀] C₀)) := by
  have HF := HasType.const (U := univs) (Γ := []) hc (ls := []) (by simp) (by simp [hU])
  rw [hT] at HF
  obtain ⟨_, HT⟩ := HF.isType henv (by trivial)
  obtain ⟨⟨_, HQ⟩, _⟩ := HT.forallE_inv henv.ordered
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (proofErase [] (ci.type.instL [])) := .const hc (by simp) (by simp [hU])
  rw [hT, show proofErase [] (.forallE (.forallE A₀ B₀) C₀) = .forallE _ _ from
    if_neg (not_isProof_of_sort (by trivial) HT),
    show proofErase [] (.forallE A₀ B₀) = .forallE _ _ from
    if_neg (not_isProof_of_sort (by trivial) HQ)] at RN
  exact RN

/-- Concrete declaration data discharges the native premise for an arbitrary
convertible stored nested-Pi header. No literal Unit domain is required in the
stored declaration; the shared output retains its actual erased domain. -/
theorem family_return_stored
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hf₀ : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (.forallE A₀ B₀) C₀)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam (proofErase [] A₀) (.const info.ctorName []))) :=
  family_return_selected heq hs hi hp hx hz hD hS hr hDr hf₀
    (nested_stored_family_native hc hU hT) hΓ hl R

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
