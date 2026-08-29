import Lean4Lean.Verify.Inductive.Run.SemanticHeaders
import Lean4Lean.Verify.Inductive.Run.LiteralDisjoint

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Header installation, the constructor checker, and constructor
installation composed from the declaration synthesized by those same
executable traversals.  Unlike `formationCore.headersWF`, neither the final
declaration nor its header translation is a caller input. -/
theorem AddInductive.semanticFormationCoreWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name) :
    ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe >>= fun headerEnv =>
        AddInductive.withEnv headerEnv do
          AddInductive.checkConstructors indTypes stats isUnsafe
          AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
      fun outEnv => ∃ decl headerEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ _ : ConstructorPhasesResult Hheaders outEnv, True := by
  have HheadersAndLoop :=
    AddInductive.declareInductiveTypes.semanticConstructorsWF
      Hsemantic hlevels hlevelParams hindicesSize hindices hconsts hparams
      hcommonParams Hcache Hsuffix Hambient hcommon hvisible hnprimTypes
      hconsume
  have Hcombined :
      ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
        isUnsafe >>= fun headerEnv =>
          AddInductive.withEnv headerEnv do
            AddInductive.checkConstructors indTypes stats isUnsafe
            AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
        fun outEnv =>
        ∃ decl headerEnv,
          ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
            isUnsafe depth Hc.venv indTypes headerEnv,
          ∃ _ : ConstructorPhasesResult Hheaders outEnv, True :=
    HheadersAndLoop.bind fun headerEnv Hloop => by
    have Hcheck :
        (AddInductive.checkConstructors indTypes stats isUnsafe
          { c with env := headerEnv }).WF fun _ =>
            ∃ decl,
            ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
              isUnsafe depth Hc.venv indTypes headerEnv,
              CheckedConstructorsResult Hc.venv decl Hheaders.context.venv
                  Hheaders.headers.params stats indTypes c.lparams
                  Hheaders.materialized.parameterScope /\
                CheckedConstructorOwnerNormalForms stats indTypes := by
      rw [AddInductive.checkConstructors]
      change (((liftM TypeChecker.getEnv : AddInductive.M _) >>= fun _ =>
        AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0)
          { c with env := headerEnv }).WF _
      change (((liftM TypeChecker.getEnv : AddInductive.M _)
        { c with env := headerEnv } >>= fun _ =>
          AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
            { c with env := headerEnv }).WF _)
      rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
        { c with env := headerEnv } = .ok headerEnv from rfl]
      intro checkedOut hcheckedOut
      rcases Hloop checkedOut hcheckedOut with ⟨decl, ⟨Hheaders⟩⟩
      have hfull : AddInductive.checkConstructors indTypes stats isUnsafe
          { c with env := headerEnv } = .ok checkedOut := by
        rw [AddInductive.checkConstructors]
        change ((liftM TypeChecker.getEnv : AddInductive.M _)
          { c with env := headerEnv } >>= fun _ =>
            AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
              { c with env := headerEnv }) = .ok checkedOut
        rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
          { c with env := headerEnv } = .ok headerEnv from rfl]
        exact hcheckedOut
      have hlitInstalled := Hheaders.materializedAvailableLiteralDisjoint
      have Hchecked := AddInductive.checkConstructors.checkedWF Hheaders
        hconsume hlitInstalled
        (fun h => Hheaders.translation.isUnsafe.trans h)
        checkedOut hfull
      have Howners :=
        AddInductive.checkConstructors.ownerNormalFormsWF Hheaders
          hconsume hlitInstalled
          checkedOut hfull
      exact ⟨decl, Hheaders, Hchecked, Howners⟩
    have Hphases :
        ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
          AddInductive.declareConstructors stats indTypes isUnsafe)
            { c with env := headerEnv }).WF fun outEnv =>
              ∃ decl,
              ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
                isUnsafe depth Hc.venv indTypes headerEnv,
              ∃ _ : ConstructorPhasesResult Hheaders outEnv, True :=
      Hcheck.bind fun _ Hchecked => by
      rcases Hchecked with ⟨decl, Hheaders, Hchecked, Howners⟩
      exact (AddInductive.declareConstructors.WF Hheaders
        Hchecked.checked hvisible hnprimCtors).mono fun outEnv Hdeclared => by
          rcases Hdeclared with ⟨Hdeclared, _⟩
          let R : ConstructorPhasesResult Hheaders outEnv := {
            checked := Hchecked.checked
            parameterPrefixes := Hchecked.parameterPrefixes
            constructorTails := Hchecked.constructorTails
            ownerNormalForms := Howners
            declared := Hdeclared
            formation := Hheaders.formation Hchecked
            core := Lean4Lean.VerifyInductive.TrInductDeclCore.ofPhases
              Hheaders.translation Hdeclared.translation }
          exact ⟨decl, Hheaders, R, trivial⟩
    have Hphases' :
        ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
          AddInductive.declareConstructors stats indTypes isUnsafe)
            { c with env := headerEnv }).WF fun outEnv =>
          ∃ decl headerEnv',
            ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
              isUnsafe depth Hc.venv indTypes headerEnv',
            ∃ _ : ConstructorPhasesResult Hheaders outEnv, True := by
      intro outEnv hout
      have Hresult := Hphases outEnv hout
      rcases Hresult with ⟨decl, Hheaders, R, _⟩
      exact ⟨decl, headerEnv, Hheaders, R, trivial⟩
    change ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun _ =>
      AddInductive.declareConstructors stats indTypes isUnsafe)
        { c with env := headerEnv }).WF _
    exact Hphases'
  exact Hcombined

end VerifyInductive
end Lean4Lean
