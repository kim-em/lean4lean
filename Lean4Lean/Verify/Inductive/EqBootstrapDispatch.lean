import Lean4Lean.Verify.Inductive.EqBootstrap
import Lean4Lean.Verify.Inductive.OrdinaryFinalDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

set_option linter.unusedSimpArgs false in
/-- Nested-inductive lowering is a literal no-op for the bootstrap `Eq`
syntax: its recursive constructor occurrence is the family currently being
defined, not a nested occurrence through another inductive. -/
theorem ElimNestedInductive.run'.eqBootstrapNoop
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (res : ElimNestedInductive.Result)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe)
    (hAbsent : env.find? ``Eq = none)
    (hout : ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }) = .ok res) :
    res.types = types ∧ res.aux2nested.size = 0 := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  have hctorInstantiate (fv : FVarId) :
      (Expr.forallE reflValueName (.bvar 0)
        (.app (.app (.app (.const ``Eq [.param u]) (.bvar 1)) (.bvar 0))
          (.bvar 0)) .default).instantiate1' (.fvar fv) =
        Expr.forallE reflValueName (.fvar fv)
          (.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.bvar 0))
            (.bvar 0)) .default := by
    rfl
  have hclose (id : FVarId) :
      (({} : LocalContext).mkLocalDecl id reflAlphaName
          (.sort (.param u)) .implicit).mkForall #[.fvar id]
          (.forallE reflValueName (.fvar id)
            (.app (.app (.app (.const ``Eq [.param u]) (.fvar id))
              (.bvar 0)) (.bvar 0)) .default) =
        eqBootstrapReflType u reflAlphaName reflValueName := by
    let lctx := ({} : LocalContext).mkLocalDecl id reflAlphaName
      (.sort (.param u)) .implicit
    have hmapWF : ({} : PersistentHashMap FVarId LocalDecl).WF := .empty
    have hid : lctx.find? id = some (.cdecl 0 id reflAlphaName
        (.sort (.param u)) .implicit .default) := by
      simp only [lctx, LocalContext.mkLocalDecl, LocalContext.find?]
      rw [hmapWF.find?_insert]
      simp
    have hfind : ∀ x ∈ [id], ∃ decl, lctx.find? x = some decl := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact ⟨_, hid⟩
    rw [LocalContext.mkForall]
    change LocalContext.mkBinding false _
      ⟨[id].map Expr.fvar⟩ _ = _
    rw [LocalContext.mkBinding_eq]
    rw [LocalContext.mkBindingList_eq_fold hfind (by simp)]
    simp [LocalContext.mkBindingList1, hid, Expr.abstract1,
      eqBootstrapReflType]
  cases fuel with
  | zero =>
    simp [eqBootstrapType, eqBootstrapReflType, hAbsent, Lean.mkFreshId,
      getNGen, setNGen, StateT.run', ElimNestedInductive.run,
      ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
      ElimNestedInductive.run.loop, MonadExcept.throw,
      instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
      StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
      MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
      ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
      ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
      StateT.get, StateT.set, StateT.modifyGet, getThe, modifyGetThe,
      MonadState.get, MonadState.set, MonadState.modifyGet,
      MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet,
      instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
      instMonadStateOfStateTOfMonad, _root_.modify,
      Bind.bind, Monad.toBind, ReaderT.instMonad, StateT.instMonad,
      Except.instMonad, Pure.pure, Applicative.toPure,
      Applicative.toFunctor, Monad.toApplicative,
      Functor.map, StateT.map, Except.bind, Except.pure, Except.map] at hout
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [eqBootstrapType, eqBootstrapReflType, hctorInstantiate, hAbsent, Lean.mkFreshId,
        getNGen, setNGen, StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.run.loop, ElimNestedInductive.withParams,
        ElimNestedInductive.withParams.loop,
        ElimNestedInductive.lowerNext, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
        StateT.get, StateT.modifyGet, getThe, modifyGetThe,
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, instMonadStateOfMonadStateOf,
        instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
        _root_.modify, Bind.bind, Monad.toBind, ReaderT.instMonad,
        StateT.instMonad, Except.instMonad, Pure.pure,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        Except.bind, Except.pure, Except.map, Functor.map,
        ElimNestedInductive.lowerInductive,
        ElimNestedInductive.lowerConstructor,
        ElimNestedInductive.replaceAllNested,
        ElimNestedInductive.replaceIfNested,
        ElimNestedInductive.isNestedInductiveApp?,
        ElimNestedInductive.isNestedInductiveAppConst?, Expr.replaceM,
        Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
        Expr.getAppArgs] at hout
    | succ fuel =>
      simp [eqBootstrapType, eqBootstrapReflType, hctorInstantiate, hAbsent, Lean.mkFreshId,
        getNGen, setNGen, StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.run.loop, ElimNestedInductive.withParams,
        ElimNestedInductive.withParams.loop,
        ElimNestedInductive.lowerNext, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
        StateT.get, StateT.modifyGet, StateT.map, getThe, modifyGetThe,
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, instMonadStateOfMonadStateOf,
        instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
        _root_.modify, Bind.bind, Monad.toBind, ReaderT.instMonad,
        StateT.instMonad, Except.instMonad, Pure.pure,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        Except.bind, Except.pure, Except.map, Functor.map,
        ElimNestedInductive.lowerInductive,
        ElimNestedInductive.lowerConstructor,
        ElimNestedInductive.replaceAllNested,
        ElimNestedInductive.replaceIfNested,
        ElimNestedInductive.isNestedInductiveApp?,
        ElimNestedInductive.isNestedInductiveAppConst?, Expr.replaceM,
        Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
        Expr.getAppArgs] at hout
      subst res
      have habstract (e : Expr) : e.abstract #[] = e := by
        simpa using Expr.abstract_eq e []
      simp [eqBootstrapType, eqBootstrapReflType, habstract]
      constructor
      · exact hclose _
      · rfl

/-- Predicate-transformer form of the exact `Eq` lowering no-op. -/
theorem ElimNestedInductive.run'.eqBootstrapNoopWF
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe)
    (hAbsent : env.find? ``Eq = none) :
    ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }).WF fun res =>
        res.types = types ∧ res.aux2nested.size = 0 :=
  fun res hout => eqBootstrapNoop env fuel lparams nparams types isUnsafe res
    Hshape hAbsent hout

/-- The exact bootstrap `Eq` syntax is necessarily dispatched through the
ordinary branch: it has one universe parameter and one inductive parameter,
whereas primitive Bool/Nat recognition requires both lists to be empty. -/
theorem checkPrimitiveInductive_eq_false_of_eqBootstrapShape
    (env : Environment)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe) :
    Environment.checkPrimitiveInductive env lparams nparams types isUnsafe =
      .ok false := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  simp [Environment.checkPrimitiveInductive]
  rfl

/-- Source-aligned ordinary execution of the exact safe bootstrap `Eq`
declaration establishes the first canonical equality environment. -/
theorem VerifiedSemanticInductiveRunResultSourceAligned.extendEqBootstrap
    {ves : VEnvs}
    (Hrun : VerifiedSemanticInductiveRunResultSourceAligned source sourceEnv
      nparams types numNested outEnv)
    (wf : ves.WF source.env)
    (hAbsent : source.env.constants.find? ``Eq = none)
    (hsafety : source.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (Hshape : EqBootstrapShape source.lparams nparams types
      (source.safety != .safe)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (InductiveSpecificationResult sourceEnv source.lparams
        nparams types (source.safety != .safe)) := by
  have hnonempty : types ≠ [] := by
    rcases Hshape with
      ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
        _hlparams, _hnparams, _hunsafe, htypes⟩
    rw [htypes]
    simp
  have Hspec := Hrun.independentSpecification hnonempty
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hcSafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hphases⟩
  have wf' : ves.WF c'.env := by
    rw [henv]
    exact wf
  have hAbsent' : c'.env.constants.find? ``Eq = none := by
    rwa [henv]
  have hcSafety' : c'.safety = .safe := hcSafety.trans hsafety
  have hcVEnv : Hc'.venv = ves.venv .safe := hvenv.trans hsource
  have Hshape' : EqBootstrapShape c'.lparams nparams
      types.toArray.toList (source.safety != .safe) := by
    simpa [hlparams] using Hshape
  rcases Hphases.extendSafeEqBootstrap wf' hAbsent' hcSafety' hcVEnv
      Hshape' with ⟨ves', wf', hEq', hle⟩
  exact ⟨ves', wf', hEq', hle, Hspec⟩

/-- Complete `AddInductive.run` refinement for the exact bootstrap `Eq`
declaration, without assuming canonical equality in the source model. -/
theorem AddInductive.run.eqBootstrapFinalWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hAbsent : c.env.constants.find? ``Eq = none)
    (hsafety : c.safety = .safe)
    (hsource : Hc.venv = ves.venv .safe)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (Hshape : EqBootstrapShape c.lparams nparams types
      (c.safety != .safe))
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth numNested
        types.toArray (c.safety != .safe) Hc') :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (InductiveSpecificationResult Hc.venv c.lparams
          nparams types (c.safety != .safe)) := by
  have hsize : 0 < types.toArray.size := by
    rcases Hshape with
      ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
        _hlparams, _hnparams, _hunsafe, htypes⟩
    rw [htypes]
    change 0 < 1
    decide
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed hctx hsize (by simp [hsafety]) Hinputs).mono fun _ Hrun =>
      Hrun.extendEqBootstrap wf hAbsent hsafety hsource Hshape

/-- Final-model boundary for the zero-auxiliary production branch reached by
the exact bootstrap `Eq` declaration. -/
theorem Environment.addInductiveAfterLowering.eqBootstrapFinalEnvironmentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hAbsent : env.constants.find? ``Eq = none)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      false fuel res).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ EqReadyOrAbsent outEnv ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult (ves.venv .safe) lparams
            nparams types false) := by
  have hisUnsafe : isUnsafe = false := by
    rcases Hshape with
      ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
        _hlparams, _hnparams, hunsafe, _htypes⟩
    exact hunsafe
  subst isUnsafe
  let c := initialContext env lparams .safe false fuel
  let Hc : ContextWF c := by
    simpa [c, initialContext] using
      ContextWF.initial wf .safe lparams false fuel
  have hsource : Hc.venv = ves.venv .safe := rfl
  have Hshape' : EqBootstrapShape c.lparams nparams res.types
      (c.safety != .safe) := by
    simpa [c, initialContext, htypes] using Hshape
  have Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth 0
        res.types.toArray (c.safety != .safe) Hc' := by
    intro c' stats depth commonParams commonLevel Hc' hallow _hfuel _Hsemantic
    exact SemanticRunVerificationInputs.ofAllowPrimitiveFalse
      (by simpa [c, initialContext] using hallow)
  have Hrun := AddInductive.run.eqBootstrapFinalWF
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hAbsent
    (by rfl) hsource wf.inductivesClosed (by rfl) Hshape' Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  simpa [c, initialContext] using Hrun.mono fun _ h => by
    rcases h with ⟨ves', wf', hEq', hle, Hspec⟩
    have Hspec' : Nonempty (InductiveSpecificationResult
        (ves.venv .safe) lparams nparams types false) := by
      rw [hsource] at Hspec
      simpa [c, initialContext, htypes] using Hspec
    exact ⟨ves', wf', EqReadyOrAbsent.ofCanonical hEq', hle, Hspec'⟩

/-- End-to-end production `addInductive` boundary for the ordinary bootstrap
`Eq` declaration.  Source checks and the exact lowering no-op are composed
with the same source-aligned run that installs canonical abstract equality. -/
theorem Environment.addInductive.eqBootstrapFinalEnvironmentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hAbsent : env.constants.find? ``Eq = none)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe false fuel).WF
      fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ EqReadyOrAbsent outEnv ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult (ves.venv .safe) lparams
            nparams types false) := by
  have hAbsentFind : env.find? ``Eq = none := by
    rw [Lean.Kernel.Environment.find?,
      (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hAbsent
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.eqBootstrapNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape hAbsentFind
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.eqBootstrapFinalEnvironmentWF env
        lparams nparams types isUnsafe fuel res ves wf hAbsent Hshape
        Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Checked `addDecl` dispatch for the exact non-primitive bootstrap `Eq`
declaration.  The actual primitive precheck is proved to return `false`, so
the theorem follows the production branch rather than assuming it. -/
theorem addInductiveDeclaration.eqBootstrapFinalEnvironmentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hAbsent : env.constants.find? ``Eq = none)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ EqReadyOrAbsent outEnv ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult (ves.venv .safe) lparams
            nparams types false) := by
  have Hrun := Environment.addInductive.eqBootstrapFinalEnvironmentWF env
    lparams nparams types isUnsafe fuel ves wf hAbsent Hshape
  have hcheck := checkPrimitiveInductive_eq_false_of_eqBootstrapShape env Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
