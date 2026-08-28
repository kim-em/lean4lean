import Lean4Lean.Verify.Inductive.CompletedBlockCertificate

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem CompletedRecursorPhasesResult.minorPrefixLength_eq
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (owner : Nat)
    (howner : owner ≤ H.recInfos.size) :
    ((H.recInfos.toList.take owner).flatMap
      (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  have hsizes : H.recInfos.size = indTypes.size := by
    calc
      H.recInfos.size = decl.types.length := H.cardinality.records
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < H.recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos H.recInfos owner hrec,
        getElem!_pos indTypes owner hind] using H.minorCounts owner hrec

theorem CompletedRecursorPhasesResult.outVEnvWF
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) : H.outVEnv.WF := by
  have hvalid : CheckingEnv.Valid H.localContext.safety
      H.localContext.env R.context.venv := by
    rw [← H.recursorEnv]
    exact H.recursorWF.checking
  exact (H.installed.valid hvalid).tr.wf

/-- Recursor installation preserves the constructor semantics established at
the completed formation boundary. -/
theorem CompletedRecursorPhasesResult.constructorSemantics
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (Hsource : InductiveConstructorsSemanticallyCoherent
      safety c.env sourceEnv) :
    InductiveConstructorsSemanticallyCoherent safety outEnv H.outVEnv := by
  apply H.installed.preservesConstructorSemantics
  · rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  · rw [H.localExtends.env_eq]
    exact R.constructorSemantics Hsource
  · exact H.generated.nonInductive

theorem CompletedRecursorPhasesResult.productionInductiveOrigins
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    ProductionInductiveOrigins c.env.constants outEnv.constants decl := by
  have hctorOrigins : ProductionInductiveOrigins c.env.constants
      H.localContext.env.constants decl := by
    simpa [H.localExtends.env_eq] using R.productionInductiveOrigins
  apply ProductionInductiveOrigins.addConstants hctorOrigins H.installed
  · rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  · exact H.generated.nonInductive

theorem CompletedRecursorPhasesResult.completedConstructorSemantics
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (Hsource : InductiveConstructorsSemanticallyCoherent
      safety c.env sourceEnv) (rules : List VDefEq) :
    InductiveConstructorsSemanticallyCoherent safety outEnv
      (H.outVEnv.addDefEqRules rules) :=
  (H.constructorSemantics Hsource).mono VEnv.addDefEqRules_le

theorem CompletedRecursorPhasesResult.generatedTelescopeTranslations
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    GeneratedRecursorTelescopeTranslations R.context.venv stats
      H.recInfos H.entries := by
  intro ownerIdx hentry
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [← H.generated.length]
    exact hentry
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  refine ⟨E.info, E.source_eq, ?_⟩
  exact E.telescopeTranslation selections hrecInfo hnoalias

theorem CompletedRecursorPhasesResult.generatedRecursorCommonPrefixBinderDomainAt
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (i : Nat)
    (hi : i < stats.params.size +
      (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size)
    {domain₁ domain₂ : Expr}
    (Hbinder₁ : Expr.ForallBinderAt
      (H.generated.entry owner₁ howner₁).info.type i domain₁)
    (Hbinder₂ : Expr.ForallBinderAt
      (H.generated.entry owner₂ howner₂).info.type i domain₂) :
    domain₁ = domain₂ := by
  have hrecInfo₁ : owner₁ < H.recInfos.size := by
    simpa [H.generated.length] using howner₁
  have hrecInfo₂ : owner₂ < H.recInfos.size := by
    simpa [H.generated.length] using howner₂
  let E₁ := H.generated.entry owner₁ howner₁
  let E₂ := H.generated.entry owner₂ howner₂
  let S₁ := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner₁ hrecInfo₁
  let S₂ := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner₂ hrecInfo₂
  have hnoalias₁ : S₁.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₁ hrecInfo₁
  have hnoalias₂ : S₂.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₂ hrecInfo₂
  by_cases hparam : i < stats.params.size
  · rcases H.params.declarationAt H.localWF i hparam with ⟨D⟩
    have Hcanonical₁ := S₁.parameterBinderAt hnoalias₁ D
    have Hcanonical₂ := S₂.parameterBinderAt hnoalias₂ D
    dsimp only at Hcanonical₁ Hcanonical₂
    rw [← E₁.type] at Hcanonical₁
    rw [← E₂.type] at Hcanonical₂
    exact (Hbinder₁.unique Hcanonical₁).trans
      (Hbinder₂.unique Hcanonical₂).symm
  · let motiveIdx := i - stats.params.size
    by_cases hmotive : motiveIdx < (H.recInfos.map (·.motive)).size
    · rcases H.bindings.motives.declarationAt H.localWF motiveIdx hmotive with
        ⟨D⟩
      have Hcanonical₁ := S₁.motiveBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.motiveBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size + motiveIdx = i := by
        dsimp [motiveIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm
    · let minorIdx := i - stats.params.size -
        (H.recInfos.map (·.motive)).size
      have hminor : minorIdx <
          (H.recInfos.flatMap (·.minors)).size := by
        dsimp [motiveIdx, minorIdx] at hmotive ⊢
        omega
      rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx hminor with
        ⟨D⟩
      have Hcanonical₁ := S₁.minorBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.minorBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size +
          (H.recInfos.map (·.motive)).size + minorIdx = i := by
        dsimp [minorIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm

end VerifyInductive
end Lean4Lean
