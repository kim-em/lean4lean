import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionParameterNative

/-! # Registered constructors with retained unit-function parameters

Actual declaration metadata supplies the original dependent header. Repeated
root constant, native identity and native eta expansions preserve that history.
After supplying an independently computed function parameter, every native
output and later type continuation returns to the selected family instance.
Arbitrary compatible computation of the whole constructor term remains open.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The registered constructor's stored header starts every native selection,
including all native conversion tails. Its fresh function parameter is retained
in the result family rather than replaced by a fixed lower-context type. -/
theorem registered_function_constructor_history
    (hΓ : OnCtx Γ (env.IsType univs))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] r ctor)) :
    NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) (.const ctor []) := by
  have hc := henv.ordered.projectionConstructor hTag
  have hC : env.HasType univs [] (.const ctor [])
      (.forallE (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0))) :=
    .const hc (by simp) rfl
  obtain ⟨_, hT⟩ := hC.isType henv (by trivial)
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL (ls := [])) hT hΓ
  change proofErase Γ (.forallE (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0))) =
    proofErase [] (.forallE (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0))) at EC
  intro out RN
  have R := RN.const_compute hc
  change ScopedCompute _ _
    (proofErase [] (.forallE (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0)))) out at R
  rwa [← EC] at R

/-- Actual registered positive constructor typing discharges the head's
retention and original-header obligations. The development relation allows
unbounded finite root expansions with full-union native guards, but does not
claim closure under arbitrary beta steps inside the generated frames. -/
theorem expanded_function_constructor_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] r ctor))
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (hΓ : OnCtx Γ (env.IsType univs))
    (RH : FunctionHeadExpansion D (proofEraseCtx Γ) (.const ctor []) head) :
    NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) head := by
  let Q : VExpr := .forallE (.const s []) (.const s [])
  have hQ : env.HasType univs Γ Q (.sort (.imax (.succ u) (.succ u))) :=
    .forallE (hS.weak0 henv.ordered) (hS.weak0 henv.ordered)
  have hB : env.HasType univs (Q :: Γ) (.app (.const r []) (.bvar 0)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) (HasType.bvar .zero)
  have hC : env.HasType univs Γ (.const ctor []) (.forallE Q (.app (.const r []) (.bvar 0))) :=
    .const (henv.ordered.projectionConstructor hTag) (by simp) rfl
  have hn : ¬ IsProof Γ (.const ctor []) := by
    rintro ⟨P, hcP, hP⟩
    have hT0 := hP.defeqU_l henv hΓ (hC.uniqU henv hΓ hcP).symm
    have E := ((HasType.forallE hQ hB).uniqU henv hΓ hT0).sort_inv henv hΓ
    have E := congrFun E []
    simp [VLevel.eval, Lean.Nat.imax] at E
  intro out RN
  exact RH.header heq hs hΓ hQ hB hC (if_neg hn)
    (fun R => registered_function_constructor_history hΓ hTag R) RN

/-- Registered constructor metadata discharges head ancestry; actual function
lookup discharges all observation and realization premises. The parameter and
all native/type continuations may compute with the full enriched union. -/
theorem expanded_function_constructor_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] r ctor))
    (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (RH : FunctionHeadExpansion D (proofEraseCtx Γ) (.const ctor []) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam A (.const info.ctorName []))) :=
  lookup_function_native_return heq hs hi hp hx hz hD hS (henv.projectionRigid hTag) hDr hF RF hΓ hl
    (expanded_function_constructor_history heq hs hS hTag hF hΓ RH) RX RN RT

/-- A future constructor native type and an independently computed assigned
family at another function lookup have one explicit common output. This is a
native-versus-assigned join for the head-expansion/application fragment. -/
theorem expanded_function_constructor_assigned_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] r ctor))
    (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hli : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (hlj : Lookup Γ j (.forallE (.const s []) (.const s [])))
    (RH : FunctionHeadExpansion D (proofEraseCtx Γ) (.const ctor []) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const r []) (.bvar j)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const r []) (.lam A (.const info.ctorName []))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const r []) (.lam A (.const info.ctorName []))) :=
  ⟨expanded_function_constructor_native_return heq hs hi hp hx hz hD hS hTag hDr hF RF hΓ hli RH RX RN RT,
    family_return_selected heq hs hi hp hx hz hD hS (henv.projectionRigid hTag) hDr hF RF hΓ hlj RR⟩

/-- Actual environment definitions and a displayed stored family header
eliminate the unfolding and selected-exposure premises. The constructor header
is read independently from projection metadata; the family domain A0 may be
merely convertible to Unit, and is retained as the common output annotation. -/
theorem environment_stored_function_constructor_native_return
    (heq : env.HasCanonicalEq)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0
      [.forallE (.const s []) (.const s [])] r ctor))
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
    (hc : env.constants r = some ci) (hU : ci.uvars = 0)
    (hStored : ci.type.instL [] = .forallE (.forallE A0 B0) C0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (RH : FunctionHeadExpansion EnvironmentCore.definitions (proofEraseCtx Γ) (.const ctor []) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
      (proofEraseCtx Γ) (.bvar i) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
      (proofEraseCtx Γ) (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
      (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      out (.app (.const r []) (.lam (proofErase [] A0) (.const info.ctorName []))) :=
  expanded_function_constructor_native_return heq EnvironmentCore.sound hi hp hx hz
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi)) hS hTag
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hF
    (nested_stored_family_native hc hU hStored) hΓ hl RH RX RN RT

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
