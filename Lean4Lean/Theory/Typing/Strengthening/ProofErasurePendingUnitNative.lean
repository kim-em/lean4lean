import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePendingUnitCodomain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperNativeOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePositiveHeaderRegistration

/-! # Native return after supplying a pending constructor parameter

Function recovery is inspected before instantiation. Its complete type history
provides an original-context codomain path; the pending unit argument and all
native conversion tails are then covered by the dependent beta-cut theorem.
The concrete registered constructor and its constant-expanded head discharge
the function-history premise from the stored declaration, without a saturated
payload observation or a computed family-header assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A function's native Pi history and an independently computed pending unit
argument suffice for every application output and every later type continuation.
The function-history premise is explicit; this is not yet a theorem preserving
that premise under arbitrary computation of the function term. -/
theorem pending_unit_application_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family []))
    (HF : ∀ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) f (.forallE X Y) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE (.const family []) (.app (.const r []) (.bvar 0)))) (.forallE X Y))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (.app f a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
  exact pending_unit_pi_result_return heq hs hi hp hx hz hD hS hr hDr hΓ hF hl
    (HF X Y RF) RX (RC.trans RT)

/-- A registered positive fieldless constructor supplies its function history
directly from its stored parameter-dependent declaration. No result demand is
required under the fresh parameter binder. -/
theorem registered_unit_constructor_function_history
    (hΓ : OnCtx Γ (env.IsType univs))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0 [.const family []] r c))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (.const c []) out) :
    ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.const family []) (.app (.const r []) (.bvar 0)))) out := by
  have hc := henv.ordered.projectionConstructor hTag
  have hC : env.HasType univs [] (.const c [])
      (.forallE (.const family []) (.app (.const r []) (.bvar 0))) :=
    .const hc (by simp) rfl
  obtain ⟨u, hT⟩ := hC.isType henv (by trivial)
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL (ls := [])) hT hΓ
  change proofErase Γ (.forallE (.const family []) (.app (.const r []) (.bvar 0))) =
    proofErase [] (.forallE (.const family []) (.app (.const r []) (.bvar 0))) at EC
  have R := RN.const_compute hc
  change ScopedCompute _ _
    (proofErase [] (.forallE (.const family []) (.app (.const r []) (.bvar 0)))) out at R
  rw [← EC] at R
  exact R

/-- The exact constructor-head escape from the saturated observer now has a
canonical native return, including independently evolved arguments, arbitrary
native conversions and later type computation. Retention is an ordinary typing
condition on the bare constructor, not an observation or native-history premise. -/
theorem wrapped_unit_constructor_application_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0 [.const family []] r c))
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family [])) (hn : ¬ IsProof Γ (.const c []))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (constantExpansion (.const c [])) a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have hc := henv.ordered.projectionConstructor hTag
  have hC : env.HasType univs Γ (.const c [])
      (.forallE (.const family []) (.app (.const r []) (.bvar 0))) :=
    .const hc (by simp) rfl
  have EC : proofErase Γ (.const c []) = .const c [] := if_neg hn
  apply pending_unit_application_native_return heq hs hi hp hx hz hD hS
    (henv.projectionRigid hTag) hDr hΓ hF hl ?_ RX RN RT
  intro X Y RF
  rw [← EC] at RF
  have RF := (static_structure_constant_expansion_native_iff heq hs hΓ hC hn).1 RF
  rw [EC] at RF
  exact registered_unit_constructor_function_history hΓ hTag RF

end Lean4Lean.VEnv.Strengthening
