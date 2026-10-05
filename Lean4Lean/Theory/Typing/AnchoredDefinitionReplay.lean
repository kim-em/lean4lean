import Lean4Lean.Theory.Typing.DefinitionDeclarationProvenance
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture
import Lean4Lean.Theory.Typing.AnchoredTraceTerm

/-! Exact ordinary-definition leaf replay. Both finite source children are
interpreted at their original header; target delta expansion preserves the
stored demand and stored declared-type support. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The only semantic induction premise is the actual earlier header theorem.
The body/type roots themselves are obtained from declaration provenance. -/
theorem definitionSupported
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {declarations : List VDecl} {value : VDefVal}
    (origin : DefinitionDeclarationOrigin env declarations value)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ l r A}, origin.stage.header.IsDefEqStrong U Γ l r A →
      Joint current fuel env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {levels : List VLevel}
    (lookup : registry.definitions value.name = some value)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (lengths : levels.length = value.uvars)
    {demand support : Profile n} {bodyRealization typeRealization : Subst}
    (body : Obs env U registry target [] bodyRealization (value.value.instL levels) demand [])
    (certificate : CodeCert env U registry target [] typeRealization (value.type.instL levels) support [])
    (typed : demand.HasType support)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (certificateBound : certificate.nativeDepth current ≤ fuel) :
    TypeRelated env U registry target (value.type.instL levels) (value.type.instL levels) support ∧
      Related env U registry target (.const value.name levels) (.const value.name levels)
        (value.type.instL levels) demand support := by
  obtain ⟨typeLevel, typeFormation⟩ := origin.typeInstance levelsWF
  have headerType := typeFormation.mono (VEnv.addConsts_le origin.stage.headers)
  have code := certificate.closedTypeCodeBounded henv hscoped hTarget origin.closed.2.instL
    (earlier headerType) certificateBound
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
  have fits : PairedFits current fuel env U registry [] target []
      bodyRealization bodyRealization (fun _ => []) := by
    constructor <;> constructor <;> intro _ _ _ _ lookup <;> cases lookup
  obtain ⟨result⟩ := (earlier (origin.bodyInstance levelsWF) target [] bodyRealization bodyRealization
    (fun _ => []) emptyClosed hTarget .nil fits).1 body bodyBound (by intro _ _ h; cases h)
  have bodyRelated := result.toGradedTransferResult.requestedRelated henv hTarget
  simp only [origin.closed.1.instL.subst_eq (σ := bodyRealization) .zero,
    origin.closed.2.instL.subst_eq (σ := bodyRealization) .zero] at bodyRelated
  have retagged := bodyRelated.retag henv typed code
  have delta : CanonicalHead.Trace registry (.const value.name levels) [] (value.value.instL levels) := by
    refine CanonicalHead.Trace.next (out := ⟨[], value.value.instL levels⟩) ?_ .refl
    simp [CanonicalHead.step, CanonicalHead.spineStep, VExpr.getAppFnArgs,
      VExpr.getAppFnArgs.go, lookup, lengths, VExpr.mkApps]
  have raw : env.IsDefEq U target (.const value.name levels) (value.value.instL levels)
      (value.type.instL levels) := by
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id lengths] using
      (IsDefEq.extra (Γ := target) origin.registered.2 levelsWF lengths)
  exact ⟨code, by
    simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
      Profile.rename_refl] using Related.prependEndpoints (type := value.type.instL levels)
      (value := demand) (support := support) henv hscoped (.traced (CanonicalDataHead.Trace.ofLegacy delta)) (.traced (CanonicalDataHead.Trace.ofLegacy delta))
      (ProofInsertion.refl hTarget)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using raw)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using raw)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl, Profile.rename_refl] using retagged)⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
