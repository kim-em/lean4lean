import Lean4Lean.Verify.Inductive.Nested.GeneratedFamilyConstruction
import Lean4Lean.Verify.Inductive.Nested.GeneratedConstructorProvenance
import Lean4Lean.Verify.Inductive.Nested.GeneratedQueueOrigins
import Lean4Lean.Verify.Inductive.Recursor.TelescopeApplication
import Lean4Lean.Verify.TypeChecker.AlphaLocality

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Exact construction provenance for generated constructors -/

/-- Simultaneous free-variable closure commutes with substitution for one
bound variable at an arbitrary binder depth.  This is the list-facing form
needed for the parameter specialization performed by the auxiliary builder. -/
theorem Expr.abstractList_instantiate1'_alpha
    (body value : Expr) (fvars : List FVarId) (d : Nat) :
    (body.instantiate1' value d).abstractList fvars d =
      (body.abstractList fvars (d + 1)).instantiate1'
        (value.abstractList fvars) d := by
  induction fvars generalizing body value with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [Lean4Lean.TypeChecker.Expr.abstract1_instantiate1'_alpha]
    exact ih (body.abstract1 fv (d + 1)) (value.abstract1 fv)

/-- Closing a residual and all of the arguments used to consume its outer
binders commutes with the complete telescope substitution. -/
theorem Expr.abstractList_instantiateForallBody
    (body : Expr) (args : List Expr) (fvars : List FVarId) :
    (Expr.instantiateForallBody body args).abstractList fvars =
      Expr.instantiateForallBody
        (body.abstractList fvars args.length)
        (args.map fun arg => arg.abstractList fvars) := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.instantiateForallBody, List.length_cons, List.map_cons]
    rw [ih, Expr.abstractList_instantiate1'_alpha]
    simp only [List.length_map]

/-- Universe substitution does not affect de Bruijn scope. -/
theorem _root_.Lean4Lean.Closed.instantiateLevelParams
    (H : Closed e k) (params : List Name) (levels : List Level) :
    Closed (e.instantiateLevelParams params levels) k := by
  rw [Expr.instantiateLevelParams_eq]
  induction e generalizing k <;>
    simp_all [Expr.instantiateLevelParamsCore', Lean4Lean.Closed]

/-- Removing a forall prefix from a closed type exposes a residual scoped by
exactly the removed binders. -/
theorem Expr.ForallTelescope.resultClosed
    (H : Expr.ForallTelescope outer arity result)
    (Houter : Closed outer depth) :
    Closed result (depth + arity) := by
  induction H generalizing depth with
  | nil => simpa using Houter
  | cons _ ih =>
    have Hbody := Houter.2
    have Hresult := ih Hbody
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hresult

/-- The level-substitution core preserves and reflects the outer forall
telescope.  The result witness is useful when producer evidence records a
telescope only after specializing its universe parameters. -/
theorem Expr.ForallTelescope.reflect_instantiateLevelParamsCore'
    (H : Expr.ForallTelescope
      (Expr.instantiateLevelParamsCore' red subst outer) arity result) :
    ∃ sourceResult,
      Expr.ForallTelescope outer arity sourceResult ∧
      Expr.instantiateLevelParamsCore' red subst sourceResult = result := by
  generalize hinst :
    Expr.instantiateLevelParamsCore' red subst outer = instantiated at H
  induction H generalizing outer with
  | nil body =>
    exact ⟨outer, .nil outer, hinst⟩
  | @cons body arity result name domain bi Htail ih =>
    cases outer <;> simp [Expr.instantiateLevelParamsCore'] at hinst
    case forallE sourceName sourceDomain sourceBody sourceBi =>
      rcases hinst with ⟨_hname, _hdomain, hbody, _hbi⟩
      rcases ih (outer := sourceBody) hbody
        with ⟨sourceResult, Hsource, hresult⟩
      exact ⟨sourceResult, .cons Hsource, hresult⟩

/-- Universe instantiation changes only levels, hence reflects any retained
outer forall telescope back to the unspecialized source type. -/
theorem Expr.ForallTelescope.reflect_instantiateLevelParams
    (H : Expr.ForallTelescope
      (outer.instantiateLevelParams levelParams levels) arity result) :
    ∃ sourceResult,
      Expr.ForallTelescope outer arity sourceResult ∧
      sourceResult.instantiateLevelParams levelParams levels = result := by
  rw [Expr.instantiateLevelParams_eq] at H
  rcases H.reflect_instantiateLevelParamsCore' with
    ⟨sourceResult, Hsource, hresult⟩
  exact ⟨sourceResult, Hsource, by
    simpa only [Expr.instantiateLevelParams_eq] using hresult⟩

/-- A concrete forall telescope has the same leading binder prefix as
itself, with its residual deliberately ignored. -/
theorem Expr.ForallTelescope.sameForallPrefixSelf
    (H : Expr.ForallTelescope source arity residual) :
    Expr.SameForallPrefix arity source source := by
  induction H with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

/-- The specification-side and application-proof-side names for consuming a
forall telescope are extensionally identical. -/
theorem VExpr.applyForallType_eq_instantiateForallPrefix
    (type : VExpr) (args : List VExpr) :
    VExpr.applyForallType type args =
      VExpr.instantiateForallPrefix type args := by
  induction args generalizing type with
  | nil => rfl
  | cons arg args ih =>
    cases type <;>
      simp [VExpr.applyForallType, VExpr.instantiateForallPrefix, ih]

/-- Universe substitution preserves the number of exposed abstract forall
binders. -/
theorem SameTelescopeArity.instL
    (H : SameTelescopeArity arity left right) (levels : List VLevel) :
    SameTelescopeArity arity (left.instL levels) (right.instL levels) := by
  induction H with
  | zero => exact .zero _ _
  | @succ leftDomain rightDomain left right arity H ih =>
    apply SameTelescopeArity.succ
    exact ih

/-- A binder-by-binder translation exposes the same abstract telescope
arity on its target. -/
theorem Expr.ForallTelescopeTypeTranslation.targetArity
    (H : Expr.ForallTelescopeTypeTranslation env Us ctx source arity target) :
    SameTelescopeArity arity target target := by
  induction H with
  | nil => exact .zero _ _
  | cons _ _ _ ih => exact .succ _ _ _ _ ih

/-- Raw expression translation preserves the outer forall shape exposed by
a concrete telescope. -/
theorem TrExprS.targetArityOfForallTelescope
    (Htr : TrExprS env Us ctx source target)
    (Htel : Expr.ForallTelescope source arity residual) :
    SameTelescopeArity arity target target := by
  induction Htel generalizing ctx target with
  | nil => exact .zero _ _
  | cons Htail ih =>
    cases Htr with
    | forallE _ _ _ Hbody => exact .succ _ _ _ _ (ih Hbody)

/-- Two independently obtained self-shape certificates of the same arity
can be crossed. -/
theorem SameTelescopeArity.cross
    (Hleft : SameTelescopeArity arity left left)
    (Hright : SameTelescopeArity arity right right) :
    SameTelescopeArity arity left right := by
  induction arity generalizing left right with
  | zero =>
    cases Hleft
    cases Hright
    exact .zero _ _
  | succ arity ih =>
    cases Hleft with
    | succ _ _ _ _ Hleft =>
      cases Hright with
      | succ _ _ _ _ Hright => exact .succ _ _ _ _ (ih Hleft Hright)

/-- The constructor residual emitted by the auxiliary builder is literally
the source constructor telescope consumed by the translated cached argument
spine.  Closedness of the raw arguments is recovered from the translation of
their closure, so it is retained producer evidence rather than a premise. -/
theorem GeneratedFamilyInstalledContainer.BuiltConstructorTranslation.sourceResidual
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux concrete H)
    (B : C.BuiltConstructorTranslation i hi)
    (lparams : List Name) (parameterDomains baseArgs : List VExpr)
    (Hbase : List.Forall₂
      (TrExprS (ves.venv safety) lparams
        (abstractForallContext parameterDomains []))
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars))
      baseArgs)
    (hdomains : parameterDomains.length = H.selection.fvars.length) :
    (B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars =
      Expr.instantiateForallBody B.sourceTail
        ((H.args.toList.take H.nestedNParams).map
          (fun arg => arg.abstractList H.selection.fvars)) := by
  let rawArgs := H.args.toList.take H.nestedNParams
  have HrawClosed : ∀ arg ∈ rawArgs, arg.Closed 0 := by
    intro arg harg
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hbase
        (arg.abstractList H.selection.fvars) (by
          exact List.mem_map.mpr ⟨arg, harg, rfl⟩) with
      ⟨targetArg, _htargetArg, Harg⟩
    have Hclosed := Harg.closed
    have Hclosed' : Closed (arg.abstractList H.selection.fvars)
        H.selection.fvars.length := by
      simpa only [abstractForallContext_bvars, VLCtx.bvars, Nat.add_zero,
        hdomains] using Hclosed
    exact Expr.closed_of_abstractList
      (fvars := H.selection.fvars) (depth := 0) (by
        simpa only [Nat.zero_add] using Hclosed')
  have HsourceClosed : Closed
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels) 0 :=
    B.sourceTranslation.2.2.closed.instantiateLevelParams _ _
  have HtailClosed : Closed B.sourceTail H.nestedNParams := by
    simpa using B.sourceTelescope.resultClosed HsourceClosed
  have HsourceFVars :
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels).FVarsIn (fun _ => False) := by
    have Hsource :=
      B.sourceTranslation.2.2.fvarsIn.instantiateLevelParams
        (levelParams := B.sourceInfo.levelParams)
        (levels := H.levels) H.levelsNoMVars
    simpa [VLCtx.fvars] using Hsource
  have HtailFVars : B.sourceTail.FVarsIn (fun _ => False) :=
    B.sourceTelescope.resultFVarsIn HsourceFVars
  have hrawLength : rawArgs.length = H.nestedNParams := by
    simp [rawArgs, Nat.min_eq_left H.argsArity]
  have HtailAbstract :
      B.sourceTail.abstractList H.selection.fvars rawArgs.length =
        B.sourceTail := by
    rw [hrawLength]
    exact (HtailFVars.mono fun _ hfalse => False.elim hfalse).abstractList_eq_self
      HtailClosed
  have Hspecialize :=
    Lean4Lean.VerifyInductive.Expr.instantiateForallBody_eq_instantiateRevList
      B.sourceTail rawArgs HrawClosed
  have Hrange :
      B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args =
        B.sourceTail.instantiateRevList rawArgs := by
    rw [Expr.instantiateRevRange_eq, Expr.instantiateRev_eq,
      Expr.instantiate_eq, Array.toList_reverse,
      Expr.instantiateList_reverse]
    congr 1
    simp [rawArgs, Array.toList_extract, List.extract_eq_take_drop,
      Nat.min_eq_left H.argsArity]
  rw [Hrange, ← Hspecialize,
    Expr.abstractList_instantiateForallBody, HtailAbstract]

/-- The generated family residual is the installed source-family telescope
consumed by the exact cached parameter spine. -/
theorem GeneratedFamilyInstalledContainer.familySourceResidual
    (C : GeneratedFamilyInstalledContainer prodEnv venv
      params nestedAux concrete H)
    (lparams : List Name) (parameterDomains baseArgs : List VExpr)
    (sourceTail : Expr)
    (HsourceTelescope : Expr.ForallTelescope
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels) H.nestedNParams sourceTail)
    (Hbase : List.Forall₂
      (TrExprS venv lparams
        (abstractForallContext parameterDomains []))
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars))
      baseArgs)
    (hdomains : parameterDomains.length = H.selection.fvars.length) :
    (sourceTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars =
      Expr.instantiateForallBody sourceTail
        ((H.args.toList.take H.nestedNParams).map
          (fun arg => arg.abstractList H.selection.fvars)) := by
  let rawArgs := H.args.toList.take H.nestedNParams
  have HrawClosed : ∀ arg ∈ rawArgs, arg.Closed 0 := by
    intro arg harg
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hbase
        (arg.abstractList H.selection.fvars) (by
          exact List.mem_map.mpr ⟨arg, harg, rfl⟩) with
      ⟨targetArg, _htargetArg, Harg⟩
    have Hclosed := Harg.closed
    have Hclosed' : Closed (arg.abstractList H.selection.fvars)
        H.selection.fvars.length := by
      simpa only [abstractForallContext_bvars, VLCtx.bvars, Nat.add_zero,
        hdomains] using Hclosed
    exact Expr.closed_of_abstractList
      (fvars := H.selection.fvars) (depth := 0) (by
        simpa only [Nat.zero_add] using Hclosed')
  have HsourceClosed : Closed
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels) 0 :=
    C.familyTranslation.2.2.closed.instantiateLevelParams _ _
  have HtailClosed : Closed sourceTail H.nestedNParams := by
    simpa using HsourceTelescope.resultClosed HsourceClosed
  have HsourceFVars :
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels).FVarsIn (fun _ => False) := by
    have Hsource := C.familyTranslation.2.2.fvarsIn.instantiateLevelParams
      (levelParams := H.sourceInfo.levelParams) (levels := H.levels)
      H.levelsNoMVars
    simpa [VLCtx.fvars, ConstantInfo.type, ConstantInfo.toConstantVal,
      InductiveVal.toConstantVal] using Hsource
  have HtailFVars : sourceTail.FVarsIn (fun _ => False) :=
    HsourceTelescope.resultFVarsIn HsourceFVars
  have hrawLength : rawArgs.length = H.nestedNParams := by
    simp [rawArgs, Nat.min_eq_left H.argsArity]
  have HtailAbstract :
      sourceTail.abstractList H.selection.fvars rawArgs.length = sourceTail := by
    rw [hrawLength]
    exact (HtailFVars.mono fun _ hfalse => False.elim hfalse).abstractList_eq_self
      HtailClosed
  have Hspecialize :=
    Lean4Lean.VerifyInductive.Expr.instantiateForallBody_eq_instantiateRevList
      sourceTail rawArgs HrawClosed
  have Hrange :
      sourceTail.instantiateRevRange 0 H.nestedNParams H.args =
        sourceTail.instantiateRevList rawArgs := by
    rw [Expr.instantiateRevRange_eq, Expr.instantiateRev_eq,
      Expr.instantiate_eq, Array.toList_reverse,
      Expr.instantiateList_reverse]
    congr 1
    simp [rawArgs, Array.toList_extract, List.extract_eq_take_drop,
      Nat.min_eq_left H.argsArity]
  rw [Hrange, ← Hspecialize,
    Expr.abstractList_instantiateForallBody, HtailAbstract]

/-- The header translated by the ordinary checker for an exact generated
family is definitionally the canonical specialization of its installed
container family.  Every premise is retained by the builder, installed
container certificate, header checker, or cached source application. -/
theorem GeneratedFamilyInstalledContainer.directAuxiliaryFamilyType
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux concrete H)
    (henv : (ves.venv safety).WF)
    (lparams : List Name) (parameterDomains baseArgs : List VExpr)
    (abstractLevels : List VLevel)
    (Hlevels : H.levels.mapM (VLevel.ofLevel lparams) =
      some abstractLevels)
    (Hbase : List.Forall₂
      (TrExprS (ves.venv safety) lparams
        (abstractForallContext parameterDomains []))
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars))
      baseArgs)
    (hdomains : parameterDomains.length = H.selection.fvars.length)
    (hparams : OnCtx parameterDomains.reverse
      ((ves.venv safety).IsType lparams.length))
    (familyTarget : VExpr)
    (Hfamily : TrExprS (ves.venv safety) lparams [] concrete.type
      (VExpr.wrapForalls parameterDomains familyTarget))
    (HfamilyApps : VExpr.WF (ves.venv safety) lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
          abstractLevels)
        baseArgs))
    (hlevelsLength : abstractLevels.length = C.container.uvars) :
    (ves.venv safety).IsDefEqU lparams.length []
        (VExpr.wrapForalls parameterDomains familyTarget)
        (VExpr.wrapForalls parameterDomains
          (VExpr.instantiateForallPrefix
            ((C.container.types[C.familyIdx]'C.familyIdx_lt).type.instL
              abstractLevels) baseArgs)) ∧
      (ves.venv safety).HasType lparams.length
        (abstractForallContext parameterDomains []).toCtx
        (VExpr.mkApps
          (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
            abstractLevels)
          baseArgs)
        (VExpr.instantiateForallPrefix
          ((C.container.types[C.familyIdx]'C.familyIdx_lt).type.instL
            abstractLevels) baseArgs) := by
  let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
  have hbaseLength : baseArgs.length = C.container.nparams := by
    have hlength := Lean4Lean.List.Forall₂.length_eq Hbase
    have hsourceLength :
        ((H.args.toList.take H.nestedNParams).map
          (fun arg => arg.abstractList H.selection.fvars)).length =
            H.nestedNParams := by
      simp [Nat.min_eq_left H.argsArity]
    exact hlength.symm.trans (hsourceLength.trans C.nestedNParams)
  have hsourceLevelLength : H.sourceInfo.levelParams.length = H.levels.length := by
    calc
      H.sourceInfo.levelParams.length = C.container.uvars := C.levelParams
      _ = abstractLevels.length := hlevelsLength.symm
      _ = H.levels.length :=
        (checkPositivityStep.List.mapM_some_length Hlevels).symm
  have hlevelsWF : ∀ level ∈ abstractLevels,
      level.WF lparams.length :=
    VLevel.WF.of_mapM_ofLevel Hlevels
  have Hinst := C.familyTranslation.2.2.instL henv (by trivial) Hlevels
    hsourceLevelLength
  rcases Hinst with ⟨instFamilyType, HinstTranslation, HinstDefEq⟩
  have Hlookup : (ves.venv safety).constants containerFamily.name =
      some containerFamily.toVConstant := by
    rw [show containerFamily.name = H.sourceName by
      simpa [containerFamily] using (C.lookupName.trans C.familyName).symm]
    exact C.familyLookup
  have Hconst₀ : (ves.venv safety).HasType lparams.length []
      (.const containerFamily.name abstractLevels)
      (containerFamily.type.instL abstractLevels) := by
    apply VEnv.HasType.const Hlookup hlevelsWF
    simpa [containerFamily] using hlevelsLength.trans C.familyUvars.symm
  have HcanonicalType : (ves.venv safety).IsType lparams.length []
      (containerFamily.type.instL abstractLevels) :=
    Hconst₀.isType henv.ordered (by trivial)
  have HinstType : (ves.venv safety).IsType lparams.length []
      instFamilyType :=
    HcanonicalType.defeqU_l henv (by trivial) HinstDefEq.symm
  have hctx : OnCtx (abstractForallContext parameterDomains []).toCtx
      ((ves.venv safety).IsType lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hparams
  have W : Ctx.LiftN parameterDomains.length 0 []
      (abstractForallContext parameterDomains []).toCtx := by
    simpa only [abstractForallContext_toCtx, VLCtx.toCtx] using
      (Ctx.LiftN.zero (n := parameterDomains.length) (Γ := [])
        parameterDomains.reverse (by simp))
  have HinstTranslation₀ : TrExprS (ves.venv safety) lparams []
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels) instFamilyType := by
    simpa [VLCtx.instL, ConstantInfo.type, ConstantInfo.toConstantVal,
      InductiveVal.toConstantVal] using HinstTranslation
  have HinstDefEq₀ : (ves.venv safety).IsDefEqU lparams.length []
      instFamilyType (containerFamily.type.instL abstractLevels) := by
    simpa [VLCtx.instL, VLCtx.toCtx, containerFamily] using HinstDefEq
  have HsourceClosed : Closed
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels) 0 :=
    C.familyTranslation.2.2.closed.instantiateLevelParams _ _
  rcases HinstType with ⟨instTypeLevel, HinstTypeHas⟩
  have HinstClosed := HinstTypeHas.closedN henv.ordered (by trivial)
  have HinstTranslationCtx : TrExprS (ves.venv safety) lparams
      (abstractForallContext parameterDomains [])
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels) instFamilyType := by
    have Hweak := HinstTranslation₀.weakBV henv.ordered
      (abstractForallContext.bvLift parameterDomains [])
    have hsourceLift :
        (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
          H.levels).liftLooseBVars' 0 parameterDomains.length =
        H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
          H.levels :=
      Expr.liftLooseBVars_eq_self HsourceClosed.looseBVarRange_le
    rw [hsourceLift, HinstClosed.liftN_eq (Nat.zero_le _)] at Hweak
    exact Hweak
  have HinstTypeCtx : (ves.venv safety).IsType lparams.length
      (abstractForallContext parameterDomains []).toCtx instFamilyType := by
    have Hweak := HinstTypeHas.weakN henv.ordered W
    rw [HinstClosed.liftN_eq (Nat.zero_le _)] at Hweak
    exact ⟨instTypeLevel, by simpa [VExpr.liftN] using Hweak⟩
  rcases H.built.generatedFamilyTelescope H.selection with
    ⟨sourceTail, HsourceTelescope, HgeneratedTelescope⟩
  have HtypedTelescope := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    HsourceTelescope HinstTranslationCtx HinstTypeCtx
  have Hfn : (ves.venv safety).HasType lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (.const containerFamily.name abstractLevels) instFamilyType := by
    have Hweak := Hconst₀.weakN henv.ordered W
    rcases HcanonicalType with ⟨_canonicalLevel, HcanonicalTypeHas⟩
    have Hclosed := HcanonicalTypeHas.closedN henv.ordered (by trivial)
    rw [Hclosed.liftN_eq (Nat.zero_le _)] at Hweak
    have Hweak' : (ves.venv safety).HasType lparams.length
        (abstractForallContext parameterDomains []).toCtx
        (.const containerFamily.name abstractLevels)
        (containerFamily.type.instL abstractLevels) := by
      simpa [VExpr.liftN] using Hweak
    exact Hweak'.defeqU_r henv hctx
      (HinstDefEq₀.symm.weak0 henv.ordered)
  have hsourceArgsLength :
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars)).length =
          H.nestedNParams := by
    simp [Nat.min_eq_left H.argsArity]
  have HtypedTelescopeArgs : Expr.ForallTelescopeTypeTranslation
      (ves.venv safety) lparams (abstractForallContext parameterDomains [])
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels)
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars)).length
      instFamilyType := by
    simpa only [hsourceArgsLength] using HtypedTelescope
  have HsourceTelescopeArgs : Expr.ForallTelescope
      (H.sourceInfo.type.instantiateLevelParams H.sourceInfo.levelParams
        H.levels)
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars)).length sourceTail := by
    simpa only [hsourceArgsLength] using HsourceTelescope
  have Happlied := HtypedTelescopeArgs.applyTranslatedArguments henv hctx
    HsourceTelescopeArgs Hfn Hbase HfamilyApps
  have hresidual := C.familySourceResidual lparams parameterDomains baseArgs
    sourceTail HsourceTelescope Hbase hdomains
  have HresidualTranslation : TrExprS (ves.venv safety) lparams
      (abstractForallContext parameterDomains [])
      ((sourceTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars)
      (VExpr.applyForallType instFamilyType baseArgs) := by
    rw [hresidual]
    exact Happlied.1
  have HresidualType : (ves.venv safety).IsType lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.applyForallType instFamilyType baseArgs) :=
    Happlied.2.isType henv.ordered hctx
  have HfamilyTelescope : Expr.ForallTelescope concrete.type H.As.size
      ((sourceTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars) := by
    simpa only [H.family_eq, H.built.arity] using HgeneratedTelescope
  have hparameterArity : parameterDomains.length = H.As.size :=
    hdomains.trans H.selection.size.symm
  have HwholeTranslation :=
    HfamilyTelescope.sameForallPrefixSelf.replaceTranslatedResidual
      HfamilyTelescope HfamilyTelescope henv (by trivial) hparameterArity
        Hfamily HresidualTranslation HresidualType
  have HwholeEq : (ves.venv safety).IsDefEqU lparams.length []
      (VExpr.wrapForalls parameterDomains familyTarget)
      (VExpr.wrapForalls parameterDomains
        (VExpr.applyForallType instFamilyType baseArgs)) :=
    Hfamily.uniq henv (.refl henv (by trivial)) HwholeTranslation
  rcases HsourceTelescope.reflect_instantiateLevelParams with
    ⟨sourceRawTail, HsourceRawTelescope, _hsourceRawTail⟩
  have HcanonicalArity : SameTelescopeArity H.nestedNParams
      (containerFamily.type.instL abstractLevels)
      (containerFamily.type.instL abstractLevels) := by
    have HrawShape :=
      Lean4Lean.VerifyInductive.TrExprS.targetArityOfForallTelescope
        C.familyTranslation.2.2 HsourceRawTelescope
    simpa [containerFamily, ConstantInfo.type, ConstantInfo.toConstantVal,
      InductiveVal.toConstantVal] using HrawShape.instL abstractLevels
  have Hshape : SameTelescopeArity baseArgs.length instFamilyType
      (containerFamily.type.instL abstractLevels) := by
    rw [hbaseLength, ← C.nestedNParams]
    exact HtypedTelescope.targetArity.cross HcanonicalArity
  have HresultEq : (ves.venv safety).IsDefEqU lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.applyForallType instFamilyType baseArgs)
      (VExpr.applyForallType (containerFamily.type.instL abstractLevels)
        baseArgs) :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqU.applyForallType henv hctx Hshape
      (HinstDefEq₀.weak0 henv.ordered) Hfn HfamilyApps
  rcases HresidualType with ⟨residualLevel, HresidualType'⟩
  have HresultEq' : (ves.venv safety).IsDefEq lparams.length
      parameterDomains.reverse
      (VExpr.applyForallType instFamilyType baseArgs)
      (VExpr.applyForallType (containerFamily.type.instL abstractLevels)
        baseArgs) (.sort residualLevel) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
      HresultEq.of_l henv hctx HresidualType'
  have HsameContext : VEnv.IsDefEqCtx (ves.venv safety) lparams.length []
      parameterDomains.reverse parameterDomains.reverse := .refl hparams
  rcases VEnv.IsDefEqCtx.closeHeads HsameContext parameterDomains.length
      (by simp) HresultEq' with ⟨wholeLevel, HclosedEq⟩
  have HcanonicalWhole : (ves.venv safety).IsDefEqU lparams.length []
      (VExpr.wrapForalls parameterDomains
        (VExpr.applyForallType instFamilyType baseArgs))
      (VExpr.wrapForalls parameterDomains
        (VExpr.applyForallType (containerFamily.type.instL abstractLevels)
          baseArgs)) := by
    have htake : parameterDomains.reverse.take parameterDomains.length =
        parameterDomains.reverse := by
      simpa using (List.take_length (l := parameterDomains.reverse))
    have hdrop : parameterDomains.reverse.drop parameterDomains.length = [] := by
      simpa using (List.drop_length (l := parameterDomains.reverse))
    refine ⟨.sort wholeLevel, ?_⟩
    rw [hdrop, htake, List.reverse_reverse] at HclosedEq
    exact HclosedEq
  have Hfinal := HwholeEq.trans henv (by trivial) HcanonicalWhole
  refine ⟨?_, ?_⟩
  · simpa [containerFamily,
      VExpr.applyForallType_eq_instantiateForallPrefix] using Hfinal
  · have HcanonicalApplication :=
      Happlied.2.defeqU_r henv hctx HresultEq
    simpa [containerFamily,
      VExpr.applyForallType_eq_instantiateForallPrefix] using
        HcanonicalApplication

/-- One constructor emitted by the auxiliary builder has a source-facing
translation whose target is definitionally the canonical specialization of
the corresponding constructor in the installed container.  The translated
target itself is allowed to be the normal form selected by `TrExprS`; the
formation relation asks only for the resulting definitional equality.

All inputs describe the actual translated family header and cached argument
spine.  No constructor translation or compatibility callback is supplied. -/
theorem GeneratedFamilyInstalledContainer.BuiltConstructorTranslation.directAuxiliary
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux concrete H)
    (B : C.BuiltConstructorTranslation i hi)
    (henv : (ves.venv safety).WF)
    (lparams : List Name) (parameterDomains baseArgs : List VExpr)
    (abstractLevels : List VLevel)
    (Hlevels : H.levels.mapM (VLevel.ofLevel lparams) =
      some abstractLevels)
    (Hbase : List.Forall₂
      (TrExprS (ves.venv safety) lparams
        (abstractForallContext parameterDomains []))
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars))
      baseArgs)
    (hdomains : parameterDomains.length = H.selection.fvars.length)
    (hparams : OnCtx parameterDomains.reverse
      ((ves.venv safety).IsType lparams.length))
    (familyTarget : VExpr)
    (Hfamily : TrExprS (ves.venv safety) lparams [] concrete.type
      (VExpr.wrapForalls parameterDomains familyTarget))
    (HfamilyApps : VExpr.WF (ves.venv safety) lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
          abstractLevels)
        baseArgs))
    (hlevelsLength : abstractLevels.length = C.container.uvars)
    (numIndices : Nat) (resultLevel : VLevel) :
    let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
    let auxiliaryFamily := VInductiveType.directAuxiliary parameterDomains
      baseArgs abstractLevels containerFamily H.auxName lparams.length
        numIndices resultLevel
    ∃ target : VConstVal,
      TrSourceConstRaw (ves.venv safety) lparams
        (concrete.ctors[i]'(by
          simpa [H.family_eq] using B.targetIdx_lt)).name
        (concrete.ctors[i]'(by
          simpa [H.family_eq] using B.targetIdx_lt)).type target ∧
      VInductDecl.DirectAuxConstructor (ves.venv safety) lparams.length
        parameterDomains baseArgs abstractLevels containerFamily
          auxiliaryFamily
        (containerFamily.ctors[i]'B.abstractIdx_lt) target := by
  dsimp only
  let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
  let abstractCtor := containerFamily.ctors[i]'B.abstractIdx_lt
  have hconcreteCtor : i < concrete.ctors.length := by
    simpa [H.family_eq] using B.targetIdx_lt
  have hbaseLength : baseArgs.length = C.container.nparams := by
    have hlength := Lean4Lean.List.Forall₂.length_eq Hbase
    have hsourceLength :
        ((H.args.toList.take H.nestedNParams).map
          (fun arg => arg.abstractList H.selection.fvars)).length =
            H.nestedNParams := by
      simp [Nat.min_eq_left H.argsArity]
    exact hlength.symm.trans (hsourceLength.trans C.nestedNParams)
  have hsourceLevelLength : B.sourceInfo.levelParams.length = H.levels.length := by
    calc
      B.sourceInfo.levelParams.length = abstractCtor.uvars :=
        B.sourceTranslation.2.1
      _ = C.container.uvars := by
        simpa [abstractCtor, containerFamily] using
          C.constructorUvars i B.abstractIdx_lt
      _ = abstractLevels.length := hlevelsLength.symm
      _ = H.levels.length :=
        (checkPositivityStep.List.mapM_some_length Hlevels).symm
  have hlevelsWF : ∀ level ∈ abstractLevels,
      level.WF lparams.length :=
    VLevel.WF.of_mapM_ofLevel Hlevels
  have Hinst := B.sourceTranslation.2.2.instL henv (by trivial) Hlevels
    hsourceLevelLength
  rcases Hinst with ⟨instCtorType, HinstTranslation, HinstDefEq⟩
  have HabstractLookup : (ves.venv safety).constants abstractCtor.name =
      some abstractCtor.toVConstant := by
    simpa [abstractCtor, containerFamily] using
      installedInductCertificate_constructorLookup C.installed C.familyIdx i
        C.familyIdx_lt B.abstractIdx_lt
  have HabstractConst : (ves.venv safety).HasType lparams.length []
      (.const abstractCtor.name abstractLevels)
      (abstractCtor.type.instL abstractLevels) := by
    apply VEnv.HasType.const HabstractLookup hlevelsWF
    simpa [abstractCtor, containerFamily] using hlevelsLength.trans
      (C.constructorUvars i B.abstractIdx_lt).symm
  have HabstractType : (ves.venv safety).IsType lparams.length []
      (abstractCtor.type.instL abstractLevels) :=
    HabstractConst.isType henv.ordered (by trivial)
  have HinstType : (ves.venv safety).IsType lparams.length []
      instCtorType :=
    HabstractType.defeqU_l henv (by trivial) HinstDefEq.symm
  have hctx : OnCtx (abstractForallContext parameterDomains []).toCtx
      ((ves.venv safety).IsType lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hparams
  have W : Ctx.LiftN parameterDomains.length 0 []
      (abstractForallContext parameterDomains []).toCtx := by
    simpa only [abstractForallContext_toCtx, VLCtx.toCtx] using
      (Ctx.LiftN.zero (n := parameterDomains.length) (Γ := [])
        parameterDomains.reverse (by simp))
  have HinstTranslation₀ : TrExprS (ves.venv safety) lparams []
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels) instCtorType := by
    simpa [VLCtx.instL] using HinstTranslation
  have HinstDefEq₀ : (ves.venv safety).IsDefEqU lparams.length []
      instCtorType (abstractCtor.type.instL abstractLevels) := by
    simpa [VLCtx.instL, VLCtx.toCtx, abstractCtor, containerFamily] using
      HinstDefEq
  have HsourceClosed : Closed
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels) 0 :=
    B.sourceTranslation.2.2.closed.instantiateLevelParams _ _
  rcases HinstType with ⟨instTypeLevel, HinstTypeHas⟩
  have HinstClosed := HinstTypeHas.closedN henv.ordered (by trivial)
  have HinstTranslationCtx : TrExprS (ves.venv safety) lparams
      (abstractForallContext parameterDomains [])
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels) instCtorType := by
    have Hweak := HinstTranslation₀.weakBV henv.ordered
      (abstractForallContext.bvLift parameterDomains [])
    have hsourceLift :
        (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
          H.levels).liftLooseBVars' 0 parameterDomains.length =
        B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
          H.levels :=
      Expr.liftLooseBVars_eq_self HsourceClosed.looseBVarRange_le
    rw [hsourceLift, HinstClosed.liftN_eq (Nat.zero_le _)] at Hweak
    exact Hweak
  have HinstTypeCtx : (ves.venv safety).IsType lparams.length
      (abstractForallContext parameterDomains []).toCtx instCtorType := by
    have Hweak := HinstTypeHas.weakN henv.ordered W
    rw [HinstClosed.liftN_eq (Nat.zero_le _)] at Hweak
    exact ⟨instTypeLevel, by simpa [VExpr.liftN] using Hweak⟩
  have HtypedTelescope := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    B.sourceTelescope HinstTranslationCtx HinstTypeCtx
  have Hfn : (ves.venv safety).HasType lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (.const abstractCtor.name abstractLevels) instCtorType := by
    have Hweak := HabstractConst.weakN henv.ordered W
    rcases HabstractType with ⟨_abstractLevel, HabstractTypeHas⟩
    have Hclosed := HabstractTypeHas.closedN henv.ordered (by trivial)
    rw [Hclosed.liftN_eq (Nat.zero_le _)] at Hweak
    have Hweak' : (ves.venv safety).HasType lparams.length
        (abstractForallContext parameterDomains []).toCtx
        (.const abstractCtor.name abstractLevels)
        (abstractCtor.type.instL abstractLevels) := by
      simpa [VExpr.liftN] using Hweak
    exact Hweak'.defeqU_r henv hctx
      (HinstDefEq₀.symm.weak0 henv.ordered)
  have Hcanonical := C.specializedConstructorApplicationHasType henv i
    B.abstractIdx_lt abstractLevels hlevelsWF hlevelsLength
      (abstractForallContext parameterDomains []).toCtx hctx baseArgs
      hbaseLength HfamilyApps
  have hsourceArgsLength :
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars)).length =
          H.nestedNParams := by
    simp [Nat.min_eq_left H.argsArity]
  have HtypedTelescopeArgs : Expr.ForallTelescopeTypeTranslation
      (ves.venv safety) lparams (abstractForallContext parameterDomains [])
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels)
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars)).length
      instCtorType := by
    simpa only [hsourceArgsLength] using HtypedTelescope
  have HsourceTelescopeArgs : Expr.ForallTelescope
      (B.sourceInfo.type.instantiateLevelParams B.sourceInfo.levelParams
        H.levels)
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars)).length B.sourceTail := by
    simpa only [hsourceArgsLength] using B.sourceTelescope
  have Happlied := HtypedTelescopeArgs.applyTranslatedArguments henv hctx
    HsourceTelescopeArgs Hfn Hbase ⟨_, Hcanonical⟩
  have hresidual :=
    GeneratedFamilyInstalledContainer.BuiltConstructorTranslation.sourceResidual
      C B lparams parameterDomains baseArgs Hbase hdomains
  have HresidualTranslation : TrExprS (ves.venv safety) lparams
      (abstractForallContext parameterDomains [])
      ((B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars)
      (VExpr.applyForallType instCtorType baseArgs) := by
    rw [hresidual]
    exact Happlied.1
  have HresidualType : (ves.venv safety).IsType lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.applyForallType instCtorType baseArgs) :=
    Happlied.2.isType henv.ordered hctx
  rcases H.built.generatedFamilyTelescope H.selection with
    ⟨familyTail, _HsourceFamilyTelescope, HgeneratedFamilyTelescope⟩
  have hparameterArity : parameterDomains.length = H.As.size :=
    hdomains.trans H.selection.size.symm
  have HfamilyTelescope : Expr.ForallTelescope concrete.type
      H.As.size
      ((familyTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars) := by
    simpa only [H.family_eq, H.built.arity] using
      HgeneratedFamilyTelescope
  have HctorTelescope : Expr.ForallTelescope
      (concrete.ctors[i]'hconcreteCtor).type H.As.size
      ((B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args).abstractList
        H.selection.fvars) := by
    have HtargetTelescope := H.selection.forallTelescope
      (B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args)
    have htargetType : (concrete.ctors[i]'hconcreteCtor).type =
        H.lctx.mkForall H.As
          (B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args) := by
      have hctors : concrete.ctors = H.data.type.ctors :=
        congrArg InductiveType.ctors H.family_eq
      simpa [hctors] using B.targetType
    rw [htargetType]
    exact HtargetTelescope
  have HwholeTranslation := B.sameForallPrefix.replaceTranslatedResidual
    HfamilyTelescope HctorTelescope henv (by trivial) hparameterArity Hfamily
      HresidualTranslation HresidualType
  have HresultEq : (ves.venv safety).IsDefEqU lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.applyForallType instCtorType baseArgs)
      (VExpr.applyForallType (abstractCtor.type.instL abstractLevels)
        baseArgs) :=
    Happlied.2.uniqU henv hctx Hcanonical
  rcases HresidualType with ⟨residualLevel, HresidualType'⟩
  have HresultEq' : (ves.venv safety).IsDefEq lparams.length
      parameterDomains.reverse
      (VExpr.applyForallType instCtorType baseArgs)
      (VExpr.applyForallType (abstractCtor.type.instL abstractLevels)
        baseArgs) (.sort residualLevel) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
      HresultEq.of_l henv hctx HresidualType'
  have HsameContext : VEnv.IsDefEqCtx (ves.venv safety) lparams.length []
      parameterDomains.reverse parameterDomains.reverse :=
    .refl hparams
  rcases VEnv.IsDefEqCtx.closeHeads HsameContext parameterDomains.length
      (by simp) HresultEq' with ⟨wholeLevel, HwholeEq⟩
  have HdirectType : (ves.venv safety).IsDefEqU lparams.length []
      (VExpr.wrapForalls parameterDomains
        (VExpr.applyForallType instCtorType baseArgs))
      (VExpr.wrapForalls parameterDomains
        (VExpr.applyForallType (abstractCtor.type.instL abstractLevels)
          baseArgs)) := by
    have htake : parameterDomains.reverse.take parameterDomains.length =
        parameterDomains.reverse := by
      simpa using (List.take_length (l := parameterDomains.reverse))
    have hdrop : parameterDomains.reverse.drop parameterDomains.length = [] := by
      simpa using (List.drop_length (l := parameterDomains.reverse))
    refine ⟨.sort wholeLevel, ?_⟩
    rw [hdrop, htake, List.reverse_reverse] at HwholeEq
    exact HwholeEq
  let target : VConstVal := {
    uvars := lparams.length
    name := (concrete.ctors[i]'hconcreteCtor).name
    type := VExpr.wrapForalls parameterDomains
      (VExpr.applyForallType instCtorType baseArgs) }
  refine ⟨target, ?_, ?_⟩
  · exact {
      uvars := rfl
      name := rfl
      type := HwholeTranslation }
  · refine {
      name := ?_
      uvars := rfl
      type := ?_ }
    · dsimp [target, abstractCtor, containerFamily]
      have hctors : concrete.ctors = H.data.type.ctors :=
        congrArg InductiveType.ctors H.family_eq
      calc
        (concrete.ctors[i]'hconcreteCtor).name =
            (H.data.type.ctors[i]'B.targetIdx_lt).name := by simp [hctors]
        _ = H.sourceInfo.ctors[i].replacePrefix H.sourceName H.auxName :=
          B.targetName
        _ = abstractCtor.name.replacePrefix containerFamily.name H.auxName := by
          rw [C.constructorName i hi, C.lookupName, C.familyName]
    · simpa [target, VConstVal.directAuxiliary,
        VExpr.applyForallType_eq_instantiateForallPrefix] using HdirectType

/-- Assemble all generated constructor targets in the builder's literal
order.  Pointwise targets are chosen from the exact environment lookup and
builder position; the two `Forall₂` traces prove that the same list is both
the raw source translation and the canonical installed-container
specialization. -/
theorem GeneratedFamilyInstalledContainer.directAuxiliaryConstructors
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux concrete H)
    (wf : ves.WF prodEnv)
    (henv : (ves.venv safety).WF)
    (lparams : List Name) (parameterDomains baseArgs : List VExpr)
    (abstractLevels : List VLevel)
    (Hlevels : H.levels.mapM (VLevel.ofLevel lparams) =
      some abstractLevels)
    (Hbase : List.Forall₂
      (TrExprS (ves.venv safety) lparams
        (abstractForallContext parameterDomains []))
      ((H.args.toList.take H.nestedNParams).map
        (fun arg => arg.abstractList H.selection.fvars))
      baseArgs)
    (hdomains : parameterDomains.length = H.selection.fvars.length)
    (hparams : OnCtx parameterDomains.reverse
      ((ves.venv safety).IsType lparams.length))
    (familyTarget : VExpr)
    (Hfamily : TrExprS (ves.venv safety) lparams [] concrete.type
      (VExpr.wrapForalls parameterDomains familyTarget))
    (HfamilyApps : VExpr.WF (ves.venv safety) lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
          abstractLevels)
        baseArgs))
    (hlevelsLength : abstractLevels.length = C.container.uvars)
    (numIndices : Nat) (resultLevel : VLevel) :
    let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
    let auxiliaryFamily := VInductiveType.directAuxiliary parameterDomains
      baseArgs abstractLevels containerFamily H.auxName lparams.length
        numIndices resultLevel
    ∃ targets,
      List.Forall₂
        (fun ctor target => TrSourceConstRaw (ves.venv safety) lparams
          ctor.name ctor.type target)
        concrete.ctors targets ∧
      List.Forall₂
        (VInductDecl.DirectAuxConstructor (ves.venv safety) lparams.length
          parameterDomains baseArgs abstractLevels containerFamily
            auxiliaryFamily)
        containerFamily.ctors targets := by
  dsimp only
  let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
  let auxiliaryFamily := VInductiveType.directAuxiliary parameterDomains
    baseArgs abstractLevels containerFamily H.auxName lparams.length
      numIndices resultLevel
  have Hpoint : ∀ i (hi : i < H.sourceInfo.ctors.length),
      ∃ target : VConstVal,
        TrSourceConstRaw (ves.venv safety) lparams
          (concrete.ctors[i]'(by
            have htarget : i < H.data.type.ctors.length := by
              simpa [← H.built.constructors_length] using hi
            simpa [H.family_eq] using htarget)).name
          (concrete.ctors[i]'(by
            have htarget : i < H.data.type.ctors.length := by
              simpa [← H.built.constructors_length] using hi
            simpa [H.family_eq] using htarget)).type target ∧
        VInductDecl.DirectAuxConstructor (ves.venv safety) lparams.length
          parameterDomains baseArgs abstractLevels containerFamily
            auxiliaryFamily
          (containerFamily.ctors[i]'(by simpa [containerFamily, ← C.constructors]
            using hi)) target := by
    intro i hi
    rcases C.builtConstructorTranslation wf i hi with ⟨B⟩
    simpa only [containerFamily, auxiliaryFamily] using
      B.directAuxiliary C henv lparams parameterDomains baseArgs
        abstractLevels Hlevels Hbase hdomains hparams familyTarget Hfamily
          HfamilyApps hlevelsLength numIndices resultLevel
  let target (i : Fin H.sourceInfo.ctors.length) : VConstVal :=
    Classical.choose (Hpoint i i.isLt)
  have Htarget (i : Fin H.sourceInfo.ctors.length) :=
    Classical.choose_spec (Hpoint i i.isLt)
  let targets : List VConstVal := List.ofFn target
  refine ⟨targets, ?_, ?_⟩
  · have hlength : concrete.ctors.length = H.sourceInfo.ctors.length := by
      calc
        concrete.ctors.length = H.data.type.ctors.length := by
          simpa using congrArg (fun type => type.ctors.length) H.family_eq
        _ = H.sourceInfo.ctors.length := H.built.constructors_length.symm
    apply List.forall₂_of_getElem
    · simp [targets, hlength]
    · intro i hconcrete htargets
      have hi : i < H.sourceInfo.ctors.length := by simpa [← hlength] using hconcrete
      simpa [targets, target] using (Htarget ⟨i, hi⟩).1
  · have hlength :
        (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors.length =
          H.sourceInfo.ctors.length := C.constructors.symm
    apply List.forall₂_of_getElem
    · simp [targets, hlength]
    · intro i hcontainer htargets
      have hi : i < H.sourceInfo.ctors.length := by
        simpa [← hlength] using hcontainer
      simpa [targets, target] using (Htarget ⟨i, hi⟩).2

/-- One final constructor of a generated queue family, connected at the same
array position to all three producer-owned stages:

* the source constructor selected by `BuiltAuxiliary`;
* the concrete generated constructor before recursive lowering; and
* the final constructor after the queue's lowering step.

`translation` additionally connects that exact source position to the
constructor of the finitely installed abstract container. -/
structure FinalLoweredGeneratedFamilyOrigin.BuiltConstructorTranslation
    {ves : VEnvs}
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      target)
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params finalState.nestedAux H.source H.generated)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (Hmap : NestedAuxMapModels result finalState)
    (i : Nat) (hi : i < target.ctors.length) where
  sourceCtor : Name
  generatedCtor : Constructor
  finalCtor : Constructor
  before : Lean4Lean.ElimNestedInductive.State
  after : Lean4Lean.ElimNestedInductive.State
  sourceIdx_lt : i < H.generated.sourceInfo.ctors.length
  sourceLookup : H.generated.sourceInfo.ctors[i]? = some sourceCtor
  generatedLookup : H.source.ctors[i]? = some generatedCtor
  finalLookup : target.ctors[i]? = some finalCtor
  built : BuiltAuxConstructor prodEnv H.generated.lctx H.generated.As
    H.generated.levels H.generated.nestedNParams H.generated.args
    H.generated.sourceName H.generated.auxName sourceCtor generatedCtor
  lowering : LoweredConstructorMapping prodEnv params nparams result
    generatedCtor before (finalCtor, after)
  translation : C.BuiltConstructorTranslation i sourceIdx_lt

/-- The actual final queue mapping and persistent environment alignment
construct the complete positional package above.  In particular, no source
constructor translation or residual is supplied by a caller. -/
theorem FinalLoweredGeneratedFamilyOrigin.builtConstructorTranslation
    {ves : VEnvs}
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      target)
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params finalState.nestedAux H.source H.generated)
    (wf : ves.WF prodEnv)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (Hmap : NestedAuxMapModels result finalState)
    (i : Nat) (hi : i < target.ctors.length) :
    Nonempty (H.BuiltConstructorTranslation C result Hmap i hi) := by
  have Hmapping := H.finalMapping Hmap
  rcases H.generated.loweredConstructorAt Hmapping i hi with
    ⟨sourceCtor, generatedCtor, finalCtor, before, after, hsource,
      hsourceLookup, hgeneratedLookup, hfinalLookup, Hbuilt, Hlowering⟩
  rcases C.builtConstructorTranslation wf i hsource with ⟨Htranslation⟩
  exact ⟨{
    sourceCtor := sourceCtor
    generatedCtor := generatedCtor
    finalCtor := finalCtor
    before := before
    after := after
    sourceIdx_lt := hsource
    sourceLookup := hsourceLookup
    generatedLookup := hgeneratedLookup
    finalLookup := hfinalLookup
    built := Hbuilt
    lowering := Hlowering
    translation := Htranslation }⟩

end VerifyInductive
end Lean4Lean
