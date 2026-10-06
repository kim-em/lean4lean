import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstructorIndices
import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldConsumption
import Lean4Lean.Verify.Inductive.Recursor.CanonicalUniversePair
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel


/-- The one selected consumed constructor is definitionally equal to its
retained raw source model in the original header environment, before the
constructors are installed. -/
theorem CompletedRecursorConstruction.sourceConstructorDefEq
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    R.headerVEnv.IsDefEqU c.lparams.length R.parameterScope.toCtx
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices))
      (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal)
        (VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (VLevel.params decl.uvars))
          (InductiveSignature.vars stats.params.size S.fields.size ++
            H.sourceConstructorIndices owner howner localIndex hlocal))) := by
  let HS := H.sourceMinorSemantics owner howner localIndex hlocal
  obtain ⟨consumed, Hconsumed, _, Heq⟩ := H.constructorConsumedHeaderReplay owner howner localIndex hlocal HS
  have HfixedConsumed := (H.sourceConstructorIndices_replay owner howner localIndex hlocal).1
  have henv := R.headerCheckingAnnotations.1.wf
  have hΔ := R.headerAnonymousParameterWF
  have Hright := Hconsumed.uniq henv (.refl henv hΔ) HfixedConsumed
  simp only [abstractForallContext_toCtx, List.reverse_reverse, VLCtx.toCtx, List.append_nil] at Hright
  have Hctx : OnCtx R.parameterScope.toCtx (R.headerVEnv.IsType c.lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hΔ.toCtx
  exact Heq.trans henv Hctx Hright

end Lean4Lean.VerifyInductive
