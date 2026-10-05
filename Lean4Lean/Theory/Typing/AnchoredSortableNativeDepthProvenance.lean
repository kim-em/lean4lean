import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth
import Lean4Lean.Theory.Typing.AnchoredNativeDepthProvenance

/-! Earlier source syntax cannot acquire a newer declaration's unfolding
heads through hereditary formation queries. This applies to arbitrary newly
returned rich observers and certificates, including native Boolean Pi rows;
it does not require a depth bound from their semantic producer. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private constants_wrapForalls from Lean4Lean.Theory.Typing.AnchoredNativeDepthProvenance
set_option backward.isDefEq.respectTransparency false
variable {base env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {before declarations : List VDecl} {old : Name → Option NativeRecursorData}
  {first : NativeRegistryHistory base before old}
  {last : NativeRegistryHistory env declarations registry.natives}
  (continuation : NativeRegistryHistory.Prefix first last)
  (current : Name → Bool)
  (quiet : ∀ name value, base.constants name = some value → current name = false)

include continuation quiet in
mutual
theorem SortableCert.nativeDepth_of_constants
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint)
    (known : expression.ConstantsIn base) : certificate.nativeDepth current = 0 := by
  match certificate with
  | .ofCode source _ =>
    simpa only [SortableCert.nativeDepth] using source.nativeDepth_of_constants continuation current quiet known
  | .seed source _ =>
    simpa only [SortableCert.nativeDepth] using source.nativeDepth_of_constants continuation current quiet known
  | .observe source _ =>
    simpa only [SortableCert.nativeDepth] using source.nativeDepth_of_constants known
  | .pi domain _ bodies =>
    simp only [SortableCert.nativeDepth, domain.nativeDepth_of_constants known.1,
      bodies.nativeDepth_of_constants known.2, Nat.max_self]
  | .union left right =>
    simp only [SortableCert.nativeDepth, left.nativeDepth_of_constants known,
      right.nativeDepth_of_constants known, Nat.max_self]
  | .pad source | .sortPad source | .familyPad source | .unpad source | .down source
  | .map _ source | .support _ source | .select source _ | .focusMinimal source _ _ =>
    simpa only [SortableCert.nativeDepth] using source.nativeDepth_of_constants known
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableRows.nativeDepth_of_constants
    (rows : SortableRows env U registry target locals σ A B relevant ambient rowList footprint)
    (known : B.ConstantsIn base) : rows.nativeDepth current = 0 := by
  match rows with
  | .nil => simp only [SortableRows.nativeDepth]
  | .cons _ body _ _ tail =>
    simp only [SortableRows.nativeDepth, body.nativeDepth_of_constants known,
      tail.nativeDepth_of_constants known, Nat.max_self]
termination_by sizeOf rows
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.nativeDepth_of_constants
    (observation : SortableObs env U registry target locals σ expression demand footprint)
    (known : expression.ConstantsIn base) : observation.nativeDepth current = 0 := by
  match observation with
  | .family (name := name) (seedLevels := seedLevels) lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    obtain ⟨value, present⟩ := known
    have same := Option.some.inj ((continuation.le.constants present).symm.trans lookup)
    subst value
    have ordered := (show base.WF from ⟨before, first.history⟩).ordered
    obtain ⟨_, formation⟩ := ordered.constWF present
    have typeKnown := ((formation.strong ordered
      (show OnCtx [] (base.IsType _) from trivial)).constantsIn.1).instL seedLevels
    simp only [SortableObs.nativeDepth, tree.nativeDepth_of_constants typeKnown,
      certificate.nativeDepth_of_constants typeKnown, Nat.max_self]
  | .legacy source =>
    simpa only [SortableObs.nativeDepth] using source.nativeDepth_of_constants continuation current quiet known
  | .code _ source =>
    simpa only [SortableObs.nativeDepth] using source.nativeDepth_of_constants known
  | .app fn arg _ _ =>
    simp only [SortableObs.nativeDepth, fn.nativeDepth_of_constants known.1,
      arg.nativeDepth_of_constants known.2, Nat.max_self]
  | .lam domain _ body _ _ =>
    simp only [SortableObs.nativeDepth, domain.nativeDepth_of_constants known.1,
      body.nativeDepth_of_constants known.2, Nat.max_self]
  | .union left right =>
    simp only [SortableObs.nativeDepth, left.nativeDepth_of_constants known,
      right.nativeDepth_of_constants known, Nat.max_self]
  | .view source _ | .action source _ | .pad source | .unpad source | .rowShift source =>
    simpa only [SortableObs.nativeDepth] using source.nativeDepth_of_constants known
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableFamilyPlan.nativeDepth_of_constants
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint)
    (known : declaredType.ConstantsIn base) : plan.nativeDepth current = 0 := by
  match plan with
  | .terminal _ _ _ captures =>
    simp only [SortableFamilyPlan.nativeDepth]
    apply captures.nativeDepth_of_constants continuation current quiet
    intro expression member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    trivial
  | .binder origin domain _ body _ _ =>
    have domainKnown := constants_wrapForalls (signature.type_eq ▸ known) _ (List.mem_of_getElem? origin)
    simp only [SortableFamilyPlan.nativeDepth, domain.nativeDepth_of_constants domainKnown,
      body.nativeDepth_of_constants known, Nat.max_self]
  | .view source _ | .pad source =>
    simpa only [SortableFamilyPlan.nativeDepth] using source.nativeDepth_of_constants known
termination_by sizeOf plan
decreasing_by all_goals (simp_wf <;> omega)
end

include continuation quiet

theorem SortableObs.nativeDepth_of_original
    (observation : SortableObs env U registry target locals σ expression demand footprint)
    (original : base.IsDefEqStrong sourceU source expression right type) :
    observation.nativeDepth current = 0 :=
  observation.nativeDepth_of_constants continuation current quiet original.constantsIn.1

theorem SortableCert.nativeDepth_of_original
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint)
    (original : base.IsDefEqStrong sourceU source expression right type) :
    certificate.nativeDepth current = 0 :=
  certificate.nativeDepth_of_constants continuation current quiet original.constantsIn.1

end Lean4Lean.AnchoredSource.Adapted
