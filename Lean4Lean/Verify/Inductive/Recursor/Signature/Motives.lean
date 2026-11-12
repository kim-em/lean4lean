import Lean4Lean.Verify.Typing.Translation
import Lean4Lean.Verify.Inductive.Recursor.Signature.IndexDomains
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Given index domains `indices` that translate the executable index telescope of family
`owner` (`indexDomainSource`), the executable motive type (indices, major, elimination sort,
abstracted over the parameters) translates in the recursor-checking environment to
`∀ indices, (family applied to the bvar spine) → Sort level`, which is a type in the recursor
parameter context. Typehood of the major-and-sort residual comes from the executable's own
check, moved into the index context by conversion. -/
theorem RecursorConstruction.replayMotiveWithIndexDomains
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (hindices : indices.length = H.recInfos[owner]!.indices.size)
    (hlevels : stats.levels.mapM (VLevel.ofLevel
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)) = some levels)
    (hlevel : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some level)
    (Hindex : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      (H.indexDomainSource owner) (VExpr.wrapForalls indices (.sort .zero))) :
    let motive := VExpr.wrapForalls indices (.forallE
      (VExpr.mkApps (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
        levels)
        (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size))) (.sort level))
    TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars) motive ∧
      H.recursorWF.venv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx motive := by
  have henv := H.recursorWF.checking.tr.wf
  obtain ⟨S, oldIndices, oldMajor, oldLevel, holdIndices, _, Htr, Htype, _⟩ :=
    H.unannotatedMotiveDomains owner howner
  have Htel := (S.indicesBound.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
      H.params.fvars
  simp only [Nat.zero_add] at Htel
  have Hprefix := (TrExprS.forallDomainsOnly Htel holdIndices Htr).1
  have hbase : VLCtx.WF H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) := by
    have hp := H.parameterSuffix.parameterWF
    have hctx := abstractForallContext.isDefEq
      (left := H.parameterSuffix.parameterDecls.toCtx.reverse)
      (right := H.parameterSuffix.parameterDecls.toCtx.reverse)
      (by simpa using VEnv.IsDefEqCtx.refl hp.toCtx)
    exact hctx.wf
  have Hcontexts := TrExprS.forallPrefixContextEq henv Htel.domainsOnly
    holdIndices hindices Hprefix Hindex (.refl henv hbase)
  have Htype' : H.recursorWF.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []).toCtx
      (VExpr.wrapForalls oldIndices (.forallE oldMajor (.sort oldLevel))) := by
    simpa [VLCtx.toCtx] using Htype
  obtain ⟨Hres, HresType⟩ := TrExprS.forallTelescope_residual_typed Htel holdIndices Htr Htype'
  obtain ⟨newResult, HnewRes⟩ := Hres.defeqDFC henv Hcontexts
  have HresEq := Hres.uniq henv Hcontexts HnewRes
  have HnewType := (HresType.defeqU_l henv Hcontexts.wf.toCtx HresEq).defeqDFC
    henv.ordered Hcontexts.defeqCtx
  have HmajorTel := ((S.majorBound.mkForall_forallTelescope H.localWF (.sort H.elimLevel)).abstractN
    S.indicesBound.fvars).abstractList H.params.fvars H.recInfos[owner]!.indices.size
  have hsort (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractList fvars k = .sort H.elimLevel :=
    Expr.abstractList_eq_self_of_abstract1 (.sort H.elimLevel)
      (by intro fv depth; simp [Expr.abstract1]) fvars k
  have hsortN (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractN fvars k = .sort H.elimLevel := rfl
  simp only [Array.size_singleton, hsort, hsortN] at HmajorTel
  obtain ⟨majorDomains, residual, hmajorLen, hnewResult, Hsort⟩ :=
    TrExprS.forallTelescope_shape_with_context HmajorTel HnewRes
  cases majorDomains with
  | nil => simp at hmajorLen
  | cons major majorTail =>
    have hnil : majorTail = [] := by simpa using hmajorLen
    subst majorTail
    cases Hsort with
    | sort hsortLevel =>
      rw [hlevel] at hsortLevel
      cases Option.some.inj hsortLevel
      simp only [VExpr.wrapForalls] at hnewResult
      rw [hnewResult] at HnewRes HnewType
      obtain ⟨Hfull, HfullType⟩ := TrExprS.rebuildForallPrefix Htel hindices Hindex HnewRes HnewType
      have HmajorEq := H.unannotatedMotiveMajor owner howner hindices hlevels Hfull
      rw [HmajorEq] at Hfull HfullType
      exact ⟨Hfull, by simpa [VLCtx.toCtx] using HfullType⟩
end Lean4Lean.VerifyInductive
