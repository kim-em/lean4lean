import Init.Data.Array.Lemmas
import Init.Data.List.Sublist
import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Environment.Checker
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem VExpr.getAppFnArgs_mkApps
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs =
      let (head, prior) := fn.getAppFnArgs
      (head, prior ++ args) := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args from rfl, ih]
      simp [List.append_assoc]

/-- Rebuilding an expression from its application head and left-to-right
argument list is exact. -/
theorem VExpr.mkApps_getAppFnArgs (e : VExpr) :
    let (fn, args) := e.getAppFnArgs
    VExpr.mkApps fn args = e := by
  have go : ∀ (e : VExpr) (suffix : List VExpr),
      let (fn, args) := VExpr.getAppFnArgs.go e suffix
      VExpr.mkApps fn args = VExpr.mkApps e suffix := by
    intro e
    induction e with
    | app fn arg ihFn _ =>
      intro suffix
      change (let (head, args) :=
        VExpr.getAppFnArgs.go fn (arg :: suffix)
        VExpr.mkApps head args = VExpr.mkApps (.app fn arg) suffix)
      simpa [VExpr.mkApps] using ihFn (arg :: suffix)
    | bvar | sort | const => intro suffix; rfl
    | lam | forallE => intro suffix; rfl
  simpa [VExpr.getAppFnArgs, VExpr.mkApps] using go e []

@[simp] theorem VExpr.getAppFnArgs_mkApps_bvar
    (index : Nat) (args : List VExpr) :
    (VExpr.mkApps (.bvar index) args).getAppFnArgs = (.bvar index, args) := by
  simpa [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] using
    VExpr.getAppFnArgs_mkApps (.bvar index) args

theorem VExpr.IsFieldApp.mkApps
    (hfield : field ∈ fieldVars) (args : List VExpr) :
    (VExpr.mkApps (.bvar (field + depth)) args).IsFieldApp fieldVars depth := by
  exact ⟨field, hfield, args, VExpr.getAppFnArgs_mkApps_bvar _ _⟩

theorem VExpr.liftN_mkApps
    (fn : VExpr) (args : List VExpr) (n k : Nat) :
    (VExpr.mkApps fn args).liftN n k =
      VExpr.mkApps (fn.liftN n k) (args.map fun arg => arg.liftN n k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simpa [VExpr.mkApps, VExpr.liftN] using ih (.app fn arg)

theorem VExpr.IsFieldApp.lift
    {e : VExpr}
    (H : e.IsFieldApp fieldVars depth) (n : Nat) :
    (e.liftN n 0).IsFieldApp fieldVars (depth + n) := by
  rcases H with ⟨field, hfield, args, hspine⟩
  have hrebuild := VExpr.mkApps_getAppFnArgs e
  rw [hspine] at hrebuild
  rw [← hrebuild, VExpr.liftN_mkApps]
  have hhead : (VExpr.bvar (field + depth)).liftN n 0 =
      .bvar (field + (depth + n)) := by
    simp [VExpr.liftN, liftVar]
    omega
  rw [hhead]
  exact VExpr.IsFieldApp.mkApps hfield _

theorem VExpr.IsFieldApp.appendApps
    {e : VExpr}
    (H : e.IsFieldApp fieldVars depth) (more : List VExpr) :
    (VExpr.mkApps e more).IsFieldApp fieldVars depth := by
  rcases H with ⟨field, hfield, args, hspine⟩
  refine ⟨field, hfield, args ++ more, ?_⟩
  simpa [hspine] using VExpr.getAppFnArgs_mkApps e more

theorem VExpr.bvarHead?_eq_some
    {e : VExpr} {field : Nat}
    (h : e.bvarHead? = some field) :
    ∃ args, e.getAppFnArgs = (.bvar field, args) := by
  unfold VExpr.bvarHead? at h
  cases hspine : e.getAppFnArgs with
  | mk head args =>
    rw [hspine] at h
    cases head <;> simp at h
    rename_i index
    cases h
    exact ⟨args, rfl⟩

/-- Every recursive argument whose application head is a de Bruijn variable
is, by construction, designated by `IotaRule.fieldVars`. -/
theorem VExpr.IsFieldApp.ofRecursiveArg
    {arg : VExpr} {recursiveArgs : List VExpr} {field : Nat}
    (harg : arg ∈ recursiveArgs)
    (hhead : arg.bvarHead? = some field) :
    arg.IsFieldApp (recursiveArgs.filterMap VExpr.bvarHead?) 0 := by
  rcases VExpr.bvarHead?_eq_some hhead with ⟨args, hspine⟩
  refine ⟨field, ?_, args, by simpa using hspine⟩
  exact List.mem_filterMap.mpr ⟨arg, harg, hhead⟩

/-- Expressions containing none of the installed recursor names satisfy the
iota guard structurally. This is the ordinary-expression half of the guard;
actual recursive calls are introduced only through `GuardedIota.recCall`. -/
theorem VExpr.GuardedIota.ofContainsAnyConstFalse
    {e : VExpr} {recursors : List Name} {fieldVars : List Nat}
    {depth : Nat}
    (h : e.containsAnyConst recursors = false) :
    e.GuardedIota recursors fieldVars depth := by
  induction e generalizing depth with
  | bvar => exact .bvar
  | sort => exact .sort
  | const name levels =>
      apply VExpr.GuardedIota.const
      intro hmem
      simp [VExpr.containsAnyConst] at h
      exact h hmem
  | app fn arg ihFn ihArg =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .app (ihFn h.1) (ihArg h.2)
  | lam dom body ihDom ihBody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .lam (ihDom h.1) (ihBody h.2)
  | forallE dom body ihDom ihBody =>
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
      exact .forallE (ihDom h.1) (ihBody h.2)

/-- Closing a guarded body over recursor-free domains preserves the guard,
with the body checked beneath exactly the number of introduced binders. -/
theorem VExpr.GuardedIota.wrapLams
    {recursors : List Name} {fieldVars : List Nat}
    {domains : List VExpr} {body : VExpr} {depth : Nat}
    (hdomains : ∀ dom ∈ domains,
      dom.containsAnyConst recursors = false)
    (hbody : body.GuardedIota recursors fieldVars
      (depth + domains.length)) :
    (VExpr.wrapLams domains body).GuardedIota recursors fieldVars depth := by
  induction domains generalizing depth with
  | nil => simpa [VExpr.wrapLams] using hbody
  | cons dom domains ih =>
      simp only [VExpr.wrapLams, List.foldr_cons]
      apply VExpr.GuardedIota.lam
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse
          (hdomains dom (by simp))
      · apply ih
        · intro inner hinner
          exact hdomains inner (by simp [hinner])
        · simpa [Nat.add_assoc, Nat.add_comm 1 domains.length] using hbody

/-- If a lambda telescope contains none of the selected constants, neither
its binder domains nor its residual body contain one. -/
theorem VExpr.containsAnyConst_wrapLams_false
    {domains : List VExpr} {body : VExpr} {names : List Name}
    (hfree : (VExpr.wrapLams domains body).containsAnyConst names = false) :
    (∀ dom ∈ domains, dom.containsAnyConst names = false) ∧
      body.containsAnyConst names = false := by
  induction domains with
  | nil => simpa [VExpr.wrapLams] using hfree
  | cons dom domains ih =>
    simp only [VExpr.wrapLams, List.foldr_cons, VExpr.containsAnyConst,
      Bool.or_eq_false_iff] at hfree
    rcases ih hfree.2 with ⟨hdomains, hbody⟩
    exact ⟨by
      intro current hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hfree.1
      · exact hdomains current hmem, hbody⟩

theorem VExpr.GuardedIota.mkApps
    {recursors : List Name} {fieldVars : List Nat} {depth : Nat}
    {fn : VExpr} {args : List VExpr}
    (hfn : fn.GuardedIota recursors fieldVars depth)
    (hargs : ∀ arg ∈ args,
      arg.GuardedIota recursors fieldVars depth) :
    (VExpr.mkApps fn args).GuardedIota recursors fieldVars depth := by
  induction args generalizing fn with
  | nil => simpa [VExpr.mkApps] using hfn
  | cons arg args ih =>
      rw [VExpr.mkApps]
      apply ih
      · exact .app hfn (hargs arg (by simp))
      · intro inner hinner
        exact hargs inner (by simp [hinner])

/-- The executable iota RHS applies a minor variable first to every
constructor field and then to the generated recursive results. Once those
two argument groups are guarded, the complete spine is guarded. -/
theorem VExpr.GuardedIota.minorRhs
    {recursors : List Name} {fieldVars : List Nat} {depth minorVar : Nat}
    {fieldArgs recursiveResults : List VExpr}
    (hfields : ∀ arg ∈ fieldArgs,
      arg.GuardedIota recursors fieldVars depth)
    (hresults : ∀ result ∈ recursiveResults,
      result.GuardedIota recursors fieldVars depth) :
    (VExpr.mkApps (.bvar minorVar) (fieldArgs ++ recursiveResults)).GuardedIota
      recursors fieldVars depth := by
  apply VExpr.GuardedIota.mkApps .bvar
  intro arg harg
  rcases List.mem_append.mp harg with hfield | hresult
  · exact hfields arg hfield
  · exact hresults arg hresult

/-- Canonical guarded shape of a generated higher-order recursive result:
zero or more recursor-free lambda domains close a recursor application whose
major premise is an application of a designated constructor field. -/
theorem VExpr.GuardedIota.recCallWrapped
    {recursors : List Name} {fieldVars : List Nat} {depth : Nat}
    {domains : List VExpr} {recursor : Name} {levels : List VLevel}
    {init : List VExpr} {major : VExpr}
    (hdomains : ∀ dom ∈ domains,
      dom.containsAnyConst recursors = false)
    (hrecursor : recursor ∈ recursors)
    (hargs : ∀ arg ∈ init ++ [major],
      arg.GuardedIota recursors fieldVars (depth + domains.length))
    (hmajor : major.IsFieldApp fieldVars (depth + domains.length)) :
    (VExpr.wrapLams domains <|
      VExpr.mkApps (.const recursor levels) (init ++ [major])).GuardedIota
      recursors fieldVars depth := by
  apply VExpr.GuardedIota.wrapLams hdomains
  exact .recCall hrecursor hargs hmajor

/-- Semantic image of one higher-order recursive result emitted by
`mkRecRules.loopU`.  This is deliberately independent of the executable
syntax: the generator-facing proof only has to show that translating one
`GeneratedRecursiveCall` produces this shape. -/
structure IotaRecursiveResultCertificate
    (recursors : List Name) (fieldVars : List Nat)
    (_recursiveArg result : VExpr) where
  domains : List VExpr
  recursor : Name
  levels : List VLevel
  init : List VExpr
  major : VExpr
  result_eq : result = (VExpr.wrapLams domains <|
    VExpr.mkApps (.const recursor levels) (init ++ [major]))
  domains_recursor_free : ∀ dom ∈ domains,
    dom.containsAnyConst recursors = false
  recursor_mem : recursor ∈ recursors
  arguments_guarded : ∀ arg ∈ init ++ [major],
    arg.GuardedIota recursors fieldVars domains.length
  major_is_field : major.IsFieldApp fieldVars domains.length

theorem IotaRecursiveResultCertificate.guarded
    (H : IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) :
    result.GuardedIota recursors fieldVars 0 := by
  rw [H.result_eq]
  exact VExpr.GuardedIota.recCallWrapped H.domains_recursor_free
    H.recursor_mem (by simpa using H.arguments_guarded)
      (by simpa using H.major_is_field)

/-- Pointwise alignment of selected recursive constructor arguments with the
translated recursive results supplied to the minor premise. -/
structure IotaRecursiveResultsCertificate
    (recursors : List Name) (fieldVars : List Nat)
    (recursiveArgs recursiveResults : List VExpr) : Prop where
  aligned : List.Forall₂ (fun major result =>
    Nonempty (IotaRecursiveResultCertificate
      recursors fieldVars major result)) recursiveArgs recursiveResults

theorem IotaRecursiveResultsCertificate.length
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults) :
    recursiveResults.length = recursiveArgs.length := by
  rcases H with ⟨aligned⟩
  induction aligned with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem IotaRecursiveResultsCertificate.results_guarded
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults) :
    ∀ result ∈ recursiveResults,
      result.GuardedIota recursors fieldVars 0 := by
  rcases H with ⟨aligned⟩
  induction aligned with
  | nil => simp
  | cons hhead _ ih =>
    intro result hresult
    simp only [List.mem_cons] at hresult
    rcases hresult with rfl | htail
    · rcases hhead with ⟨cert⟩
      exact cert.guarded
    · exact ih result htail

/-- Once ordinary constructor arguments are recursor-free, the aligned
recursive-result certificate discharges guardedness of the complete minor
application used on an iota right-hand side. -/
theorem IotaRecursiveResultsCertificate.minorRhs
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults)
    (hfields : ∀ arg ∈ fieldArgs,
      arg.containsAnyConst recursors = false) :
    (VExpr.mkApps (.bvar minorVar)
      (fieldArgs ++ recursiveResults)).GuardedIota
        recursors fieldVars 0 := by
  apply VExpr.GuardedIota.minorRhs
  · intro arg harg
    exact VExpr.GuardedIota.ofContainsAnyConstFalse (hfields arg harg)
  · exact H.results_guarded

/-- Complete right-hand-side fragment of an iota rule. The executable minor
application is represented once; its spine, field/result split, cardinality,
and guardedness are derived below. -/
structure IotaRhsCertificate
    (recursors : List Name) (domains fieldArgs recursiveArgs : List VExpr)
    (rhsBody : VExpr) where
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  recursiveResults : List VExpr
  rhs_eq : rhsBody = VExpr.mkApps (.bvar minorVar)
    (fieldArgs ++ recursiveResults)
  fieldVars : List Nat
  fieldVars_eq : fieldVars =
    recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  fields_recursor_free : ∀ arg ∈ fieldArgs,
    arg.containsAnyConst recursors = false
  recursive_results : IotaRecursiveResultsCertificate
    recursors fieldVars recursiveArgs recursiveResults

theorem IotaRhsCertificate.rhs_spine
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    rhsBody.getAppFnArgs =
      (.bvar H.minorVar, fieldArgs ++ H.recursiveResults) := by
  rcases H with ⟨minorVar, hminor, results, hrhs, fieldVars,
    hfieldVars, hfieldsScope, hfieldsFree, hresults⟩
  change rhsBody.getAppFnArgs =
    (.bvar minorVar, fieldArgs ++ results)
  rw [hrhs]
  exact VExpr.getAppFnArgs_mkApps_bvar _ _

theorem IotaRhsCertificate.field_args
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    (fieldArgs ++ H.recursiveResults).take fieldArgs.length = fieldArgs := by
  simp

theorem IotaRhsCertificate.results_length
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    ((fieldArgs ++ H.recursiveResults).drop fieldArgs.length).length =
      recursiveArgs.length := by
  simpa using H.recursive_results.length

theorem IotaRhsCertificate.guarded
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    rhsBody.GuardedIota recursors H.fieldVars 0 := by
  rcases H with ⟨minorVar, hminor, results, hrhs, fieldVars,
    hfieldVars, hfieldsScope, hfieldsFree, hresults⟩
  change rhsBody.GuardedIota recursors fieldVars 0
  rw [hrhs]
  exact hresults.minorRhs hfieldsFree

/-- Completed output of the mutual-header traversal. -/
structure HeaderCertificate (env : VEnv) (decl : VInductDecl) where
  params : List VExpr
  resultLevel : VLevel
  commonLevels : ∀ type ∈ decl.types, type.resultLevel ≈ resultLevel
  typeShapes : ∀ type ∈ decl.types, decl.TypeShape env params type

theorem typeShape_mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.TypeShape env decl params type) :
    VInductDecl.TypeShape env' decl params type := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, hindicesTake, hparams, hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnormalized.mono henv, hparamsTake, hindicesTake,
    hparams.mono henv, hresult.mono henv⟩

def HeaderCertificate.mono {env env' : VEnv} (henv : env ≤ env')
    (H : HeaderCertificate env decl) : HeaderCertificate env' decl where
  params := H.params
  resultLevel := H.resultLevel
  commonLevels := H.commonLevels
  typeShapes type htype := typeShape_mono henv (H.typeShapes type htype)

/-- Prefix invariant threaded through `checkInductiveTypes.loopInd`. -/
structure HeaderPrefixCertificate (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) (done : Nat) : Prop where
  commonLevels : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.types[i].resultLevel ≈ resultLevel
  typeShapes : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.TypeShape env params decl.types[i]

/-- The prefix evidence together with the translation of the concrete common
result level retained in `InductiveStats`. -/
structure HeaderLoopCertificate (env : VEnv) (lparams : List Name)
    (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (done : Nat) where
  resultLevel : VLevel
  commonLevel : VLevel.ofLevel lparams stats.resultLevel = some resultLevel
  headerPrefix : HeaderPrefixCertificate env decl params resultLevel done

theorem HeaderPrefixCertificate.empty (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) :
    HeaderPrefixCertificate env decl params resultLevel 0 where
  commonLevels _ h := by omega
  typeShapes _ h := by omega

theorem HeaderPrefixCertificate.push
    (H : HeaderPrefixCertificate env decl params resultLevel done)
    (hindex : done < decl.types.length)
    (hlevel : decl.types[done].resultLevel ≈ resultLevel)
    (hshape : decl.TypeShape env params decl.types[done]) :
    HeaderPrefixCertificate env decl params resultLevel (done + 1) where
  commonLevels i hidone hi := by
    by_cases h : i = done
    · subst i; exact hlevel
    · exact H.commonLevels i (by omega) hi
  typeShapes i hidone hi := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.typeShapes i (by omega) hi

/-- Initialize the accumulator with the first checked mutual header. -/
theorem HeaderPrefixCertificate.first
    (hindex : 0 < decl.types.length)
    (hshape : decl.TypeShape env params decl.types[0]) :
    HeaderPrefixCertificate env decl params decl.types[0].resultLevel 1 := by
  exact (HeaderPrefixCertificate.empty env decl params
    decl.types[0].resultLevel).push hindex (by rfl) hshape

/-- Convert the executable common-universe guard into the abstract level
equivalence stored by the header-prefix invariant. -/
theorem HeaderPrefixCertificate.pushOfIsEquiv
    (H : HeaderPrefixCertificate env decl params resultLevel done)
    (hindex : done < decl.types.length)
    (hguard : currentLevel.isEquiv commonLevel = true)
    (hcurrent : VLevel.ofLevel lparams currentLevel =
      some decl.types[done].resultLevel)
    (hcommon : VLevel.ofLevel lparams commonLevel = some resultLevel)
    (hshape : decl.TypeShape env params decl.types[done]) :
    HeaderPrefixCertificate env decl params resultLevel (done + 1) :=
  H.push hindex (Level.isEquiv_wf hguard hcurrent hcommon) hshape

def HeaderPrefixCertificate.complete
    (H : HeaderPrefixCertificate env decl params resultLevel decl.types.length) :
    HeaderCertificate env decl where
  params := params
  resultLevel := resultLevel
  commonLevels type htype := by
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    exact H.commonLevels i hi hi
  typeShapes type htype := by
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    exact H.typeShapes i hi hi

/-- Completed output of the flattened constructor traversal. -/
structure ConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  shapes : ∀ owned ∈ decl.ownedConstructors,
    decl.CtorShape envTypes params owned.1 owned.2

/-- Prefix invariant for constructor checking in the exact flattened order
used by recursor-minor and iota-rule generation. -/
structure ConstructorPrefixCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) (done : Nat) : Prop where
  shapes : ∀ i, i < done → (hi : i < decl.ownedConstructors.length) →
    decl.CtorShape envTypes params decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2

theorem ConstructorPrefixCertificate.empty (env : VEnv)
    (decl : VInductDecl) (envTypes : VEnv) (params : List VExpr) :
    ConstructorPrefixCertificate env decl envTypes params 0 where
  shapes _ h := by omega

theorem ConstructorPrefixCertificate.push
    (H : ConstructorPrefixCertificate env decl envTypes params done)
    (hindex : done < decl.ownedConstructors.length)
    (hshape : decl.CtorShape envTypes params
      decl.ownedConstructors[done].1 decl.ownedConstructors[done].2) :
    ConstructorPrefixCertificate env decl envTypes params (done + 1) where
  shapes i hidone hi := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.shapes i (by omega) hi

theorem ConstructorPrefixCertificate.complete
    (H : ConstructorPrefixCertificate env decl envTypes params
      decl.ownedConstructors.length) :
    ConstructorCertificate env decl envTypes params where
  shapes owned howned := by
    rcases List.mem_iff_getElem.1 howned with ⟨i, hi, rfl⟩
    exact H.shapes i hi hi

theorem ConstructorCertificate.ctorShape
    (H : ConstructorCertificate env decl envTypes params)
    (htype : type ∈ decl.types) (hctor : ctor ∈ type.ctors) :
    decl.CtorShape envTypes params type ctor := by
  apply H.shapes (type, ctor)
  simp [VInductDecl.ownedConstructors, htype, hctor]

/-- Shapes accumulated by the inner constructor loop for one family. -/
structure ConstructorTypePrefix (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) (done : Nat) : Prop where
  covered : done ≤ target.ctors.length
  shapes : ∀ i, i < done → (hi : i < target.ctors.length) →
    decl.CtorShape envTypes params target target.ctors[i]

theorem ConstructorTypePrefix.empty (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) :
    ConstructorTypePrefix envTypes decl params target 0 where
  covered := Nat.zero_le _
  shapes _ h := by omega

theorem ConstructorTypePrefix.push
    (H : ConstructorTypePrefix envTypes decl params target done)
    (hi : done < target.ctors.length)
    (hshape : decl.CtorShape envTypes params target target.ctors[done]) :
    ConstructorTypePrefix envTypes decl params target (done + 1) where
  covered := by omega
  shapes i hidone hi' := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.shapes i (by omega) hi'

/-- Shapes accumulated by the outer family loop. -/
structure ConstructorTypesPrefix (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (done : Nat) : Prop where
  covered : done ≤ decl.types.length
  shapes : ∀ i, i < done → (hi : i < decl.types.length) →
    ∀ j (hj : j < decl.types[i].ctors.length),
      decl.CtorShape envTypes params decl.types[i] decl.types[i].ctors[j]

theorem ConstructorTypesPrefix.empty (envTypes : VEnv)
    (decl : VInductDecl) (params : List VExpr) :
    ConstructorTypesPrefix envTypes decl params 0 where
  covered := Nat.zero_le _
  shapes _ h := by omega

theorem ConstructorTypesPrefix.push
    (H : ConstructorTypesPrefix envTypes decl params done)
    (hi : done < decl.types.length)
    (Htype : ConstructorTypePrefix envTypes decl params decl.types[done]
      decl.types[done].ctors.length) :
    ConstructorTypesPrefix envTypes decl params (done + 1) where
  covered := by omega
  shapes i hidone hi' j hj := by
    by_cases h : i = done
    · subst i; exact Htype.shapes j hj hj
    · exact H.shapes i (by omega) hi' j hj

theorem ConstructorTypesPrefix.complete
    (H : ConstructorTypesPrefix envTypes decl params decl.types.length) :
    ConstructorCertificate env decl envTypes params where
  shapes owned howned := by
    rcases List.mem_flatMap.1 howned with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    simp only [List.mem_map] at hctor
    rcases hctor with ⟨ctor, hctor, hpair⟩
    cases hpair
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, hctorEq⟩
    cases hctorEq
    simpa using H.shapes i hi hi j hj

/-- Exact name-set state reached by the production inner constructor loop. -/
inductive ConstructorNameState (ctors : List Constructor) :
    Nat → NameSet → Prop
  | zero : ConstructorNameState ctors 0 {}
  | succ (H : ConstructorNameState ctors i found)
      (hi : i < ctors.length) :
      ConstructorNameState ctors (i + 1) (found.insert ctors[i].name)

/-- Fielded aggregation target for the executable header and constructor
traversals. The public specification remains `VInductDecl.FormationWF`; this
certificate gives the refinement proof stable, named obligations instead of
repeatedly unpacking a large existential. -/
structure FormationCertificate (env : VEnv) (decl : VInductDecl) where
  headers : HeaderCertificate env decl
  envTypes : VEnv
  typesInstalled : env.addConsts decl.typeConstants = some envTypes
  constructors : ConstructorCertificate env decl envTypes headers.params

theorem FormationCertificate.formationWF
    (H : FormationCertificate env decl) : decl.FormationWF env := by
  exact ⟨H.headers.params, H.headers.resultLevel, H.envTypes, H.typesInstalled,
    fun type htype => ⟨H.headers.commonLevels type htype,
      H.headers.typeShapes type htype⟩,
    fun type htype ctor hctor => H.constructors.ctorShape htype hctor⟩

theorem FormationCertificate.declWF
    (H : FormationCertificate env decl) (hsource : decl.SourceWF env) :
    decl.WF env :=
  ⟨hsource, H.formationWF⟩

def FormationCertificate.ofPrefixes
    (Hheaders : HeaderLoopCertificate env lparams decl params stats
      decl.types.length)
    (envTypes : VEnv)
    (htypes : env.addConsts decl.typeConstants = some envTypes)
    (Hctors : ConstructorPrefixCertificate env decl envTypes params
      decl.ownedConstructors.length) :
    FormationCertificate env decl where
  headers := Hheaders.headerPrefix.complete
  envTypes := envTypes
  typesInstalled := htypes
  constructors := Hctors.complete

/-- Build ordered relational coverage from equal lengths and pointwise array-
style evidence. This is the common bridge used by recursor and rule loops. -/
theorem List.forall₂_of_getElem
    {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (hlen : as.length = bs.length)
    (H : ∀ i (ha : i < as.length) (hb : i < bs.length),
      R as[i] bs[i]) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil =>
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst bs
    exact .nil
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have htail : as.length = bs.length := by simpa using hlen
      apply List.Forall₂.cons (H 0 (by simp) (by simp))
      apply ih htail
      intro i ha hb
      have h := H (i + 1) (by simpa) (by simpa)
      change R as[i] bs[i] at h
      exact h

theorem List.Forall₂.getElem
    {R : α → β → Prop} {as : List α} {bs : List β}
    (H : List.Forall₂ R as bs) (i : Nat)
    (ha : i < as.length) (hb : i < bs.length) :
    R as[i] bs[i] := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i (by simpa using ha) (by simpa using hb)

theorem List.Forall₂.length_eq'
    (H : List.Forall₂ R as bs) : as.length = bs.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.Forall₂.append'
    (H₁ : List.Forall₂ R as bs) (H₂ : List.Forall₂ R as' bs') :
    List.Forall₂ R (as ++ as') (bs ++ bs') := by
  induction H₁ with
  | nil => exact H₂
  | cons h _ ih => exact .cons h ih

theorem List.Forall₂.unsnoc
    (H : List.Forall₂ R (as ++ [a]) bs) :
    ∃ bs' b, bs = bs' ++ [b] ∧ List.Forall₂ R as bs' ∧ R a b := by
  have Hrev : List.Forall₂ R (a :: as.reverse) bs.reverse := by
    simpa using List.Forall₂.reverse.mpr H
  rcases List.forall₂_cons_left_iff.mp Hrev with
    ⟨b, tail, hab, Htail, hreverse⟩
  refine ⟨tail.reverse, b, ?_, ?_, hab⟩
  · have := congrArg List.reverse hreverse
    simpa using this
  · exact List.Forall₂.reverse.mp (by simpa using Htail)

/-- Two pointwise translations of a syntactically unique source spine have
the same target spine. -/
theorem List.Forall₂.targets_eq_of_unique
    (H₁ : List.Forall₂ (TrExprS env Us Δ) source target₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ) source target₂)
    (Hunique : ∀ e ∈ source, TrExprS.IsUnique e) : target₁ = target₂ := by
  induction H₁ generalizing target₂ with
  | nil => cases H₂; rfl
  | @cons sourceHead targetHead sourceTail targetTail Hhead Htail ih =>
    cases H₂ with
    | cons Hhead' Htail' =>
      have hheadEq := TrExprS.unique
        (Hunique sourceHead (by simp)) Hhead Hhead'
      have htailEq := ih Htail' (by
        intro e he
        exact Hunique e (by simp [he]))
      rw [hheadEq, htailEq]

theorem Expr.getAppFn_mkAppN (fn : Expr) (args : Array Expr) :
    (mkAppN fn args).getAppFn = fn.getAppFn := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons]
    simpa [Expr.getAppFn] using ih (.app fn arg)

theorem Expr.getAppArgsList_mkAppN (fn : Expr) (args : Array Expr) :
    (mkAppN fn args).getAppArgsList = fn.getAppArgsList ++ args.toList := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [Expr.getAppArgsList_app, List.append_assoc]

theorem Expr.getAppArgsList_const (name : Name) (levels : List Level) :
    (Expr.const name levels).getAppArgsList = [] := rfl

theorem OnCtx.append_right
    (H : OnCtx (xs ++ ys) P) : OnCtx ys P := by
  induction xs with
  | nil => exact H
  | cons x xs ih =>
    exact ih H.1

/-- Remove equally long outer prefixes from a context conversion.  Since
`IsDefEqCtx` is built from the shared innermost suffix outwards, the proof is
just inversion through the two prefixes. -/
theorem VEnv.IsDefEqCtx.dropPrefixes
    (H : VEnv.IsDefEqCtx env U [] (xs ++ Γ₁) (ys ++ Γ₂))
    (hlen : xs.length = ys.length) :
    VEnv.IsDefEqCtx env U [] Γ₁ Γ₂ := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simpa [this] using H
  | cons _ xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons _ ys =>
      simp only [List.cons_append] at H
      cases H with
      | succ H _ =>
        apply ih H
        simpa using Nat.succ.inj hlen

theorem VInductDecl.paramsDefEq_reflOfAppend
    {decl : VInductDecl} {env : VEnv} {indices params : List VExpr}
    (H : OnCtx (indices.reverse ++ params.reverse)
      (env.IsType decl.uvars)) :
    decl.ParamsDefEq env params params := by
  exact VEnv.IsDefEqCtx.refl (OnCtx.append_right H)

theorem TrInductDeclSkeletonCore.types_length
    (H : TrInductDeclSkeletonCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    types.length = decl.types.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.types

theorem TrInductDeclSkeletonCore.typeAt
    (H : TrInductDeclSkeletonCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    TrInductiveTypeSkeleton env envTypes lparams
      types[i] decl.types[i] :=
  Lean4Lean.VerifyInductive.List.Forall₂.getElem H.types i
    hsource htarget

theorem TrInductDeclSkeletonCore.typeNameAt
    (H : TrInductDeclSkeletonCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    types[i].name = decl.types[i].name :=
  (Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.typeAt
    H i hsource htarget).header.name.symm

theorem TrInductDeclSkeleton.types_length
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl) :
    types.length = decl.types.length := by
  rcases H with ⟨_, _, _, _, _, _, _, _, htypes⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes

theorem TrInductDeclSkeleton.typeAt
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    ∃ envTypes, env.addConsts decl.typeConstants = some envTypes ∧
      TrInductiveTypeSkeleton env envTypes lparams
        types[i] decl.types[i] := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypesAdded,
    hctorsAdded, htypes⟩
  exact ⟨envTypes, htypesAdded,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem htypes i
      hsource htarget⟩

theorem TrInductDeclSkeleton.typeNameAt
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    types[i].name = decl.types[i].name := by
  rcases Lean4Lean.VerifyInductive.TrInductDeclSkeleton.typeAt
    H i hsource htarget with ⟨_, _, Htype⟩
  exact Htype.header.name.symm

theorem TrInductiveTypeSkeleton.materialized
    (H : TrInductiveTypeSkeleton env envTypes lparams type target) :
    TrInductiveType env envTypes lparams type
      (target.toVInductiveType numIndices resultLevel) where
  header := H.header
  ctors := H.ctors

/-- Once the executable header metadata has been collected, the metadata-free
source translation becomes the ordinary declaration translation expected by
the later constructor, compilation, and environment-extension layers. -/
theorem TrInductDeclSkeleton.materialized
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe skeleton)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    TrInductDecl env lparams nparams types isUnsafe decl := by
  rcases H with ⟨hsource, huvars, hnparams, hunsafe,
    envTypes, envCtors, htypesAdded, hctorsAdded, htypes⟩
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have herase := VInductDeclSkeleton.materialize_toSkeleton Hmaterialize
  have htypeConstants : decl.typeConstants = skeleton.typeConstants := by
    rw [← VInductDecl.toSkeleton_typeConstants decl, herase]
  have hconstructorConstants :
      decl.constructorConstants = skeleton.constructorConstants := by
    rw [← VInductDecl.toSkeleton_constructorConstants decl, herase]
  refine ⟨hsource metadata decl Hmaterialize,
    hfields.1.trans huvars,
    hfields.2.1.trans hnparams,
    hfields.2.2.1.trans hunsafe,
    envTypes, envCtors, ?_, ?_, ?_⟩
  · simpa [htypeConstants] using htypesAdded
  · simpa [hconstructorConstants] using hctorsAdded
  · have hlength : types.length = decl.types.length := by
      calc
        types.length = skeleton.types.length :=
          Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes
        _ = decl.types.length := hfields.2.2.2.symm
    apply List.forall₂_of_getElem hlength
    intro i hsourceIdx htargetIdx
    have hskeletonIdx : i < skeleton.types.length := by
      rw [← Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes]
      exact hsourceIdx
    have htranslated := Lean4Lean.VerifyInductive.List.Forall₂.getElem
      htypes i hsourceIdx hskeletonIdx
    rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize
        hskeletonIdx with ⟨data, hdata, htarget⟩
    have htarget' : decl.types[i] =
        skeleton.types[i].toVInductiveType data.1 data.2 := by
      simpa [List.getElem?_eq_getElem htargetIdx] using htarget
    rw [htarget']
    exact Lean4Lean.VerifyInductive.TrInductiveTypeSkeleton.materialized
      htranslated

/-- Recovering arity metadata changes neither translated source constants nor
their staging environments, so skeleton-core translation materializes to the
complete declaration-core relation without importing `SourceWF`. -/
theorem TrInductDeclSkeletonCore.materialized
    (H : TrInductDeclSkeletonCore env lparams nparams types isUnsafe skeleton
      envTypes envCtors)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors := by
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have herase := VInductDeclSkeleton.materialize_toSkeleton Hmaterialize
  have htypeConstants : decl.typeConstants = skeleton.typeConstants := by
    rw [← VInductDecl.toSkeleton_typeConstants decl, herase]
  have hconstructorConstants :
      decl.constructorConstants = skeleton.constructorConstants := by
    rw [← VInductDecl.toSkeleton_constructorConstants decl, herase]
  refine {
    uvars := hfields.1.trans H.uvars
    nparams := hfields.2.1.trans H.nparams
    isUnsafe := hfields.2.2.1.trans H.isUnsafe
    typesAdded := by simpa [htypeConstants] using H.typesAdded
    ctorsAdded := by simpa [hconstructorConstants] using H.ctorsAdded
    types := ?_ }
  have hlength : types.length = decl.types.length := by
    calc
      types.length = skeleton.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length H
      _ = decl.types.length := hfields.2.2.2.symm
  apply List.forall₂_of_getElem hlength
  intro i hsourceIdx htargetIdx
  have hskeletonIdx : i < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length H]
    exact hsourceIdx
  have htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.typeAt
      H i hsourceIdx hskeletonIdx
  rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize
      hskeletonIdx with ⟨data, hdata, htarget⟩
  have htarget' : decl.types[i] =
      skeleton.types[i].toVInductiveType data.1 data.2 := by
    simpa [List.getElem?_eq_getElem htargetIdx] using htarget
  rw [htarget']
  exact Lean4Lean.VerifyInductive.TrInductiveTypeSkeleton.materialized
    htranslated

theorem TrInductDecl.types_length
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    types.length = decl.types.length := by
  rcases H with ⟨_, _, _, _, _, _, _, _, htypes⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes

/-- Pointwise original-source translations already contain all typing and
universe facts required by `SourceWF`. Thus the aggregate source judgment
adds only nonemptiness and global name uniqueness, both enforced by the
outer declaration traversal. -/
theorem TrInductDeclCore.sourceWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ [])
    (hnames : decl.sourceNames.Nodup) :
    decl.SourceWF env := by
  have hproperties : ∀ target ∈ decl.types,
      target.uvars = decl.uvars ∧
      target.toVConstant.WF env ∧
      ∀ ctor ∈ target.ctors,
        ctor.uvars = decl.uvars ∧
        ctor.toVConstant.WF envTypes := by
    intro target htarget
    rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
      ⟨source, _, Htarget⟩
    refine ⟨Htarget.header.uvars.trans H.uvars.symm,
      Htarget.header.wf, ?_⟩
    intro ctor hctor
    rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ctor hctor with
      ⟨sourceCtor, _, Hctor⟩
    exact ⟨Hctor.uvars.trans H.uvars.symm, Hctor.wf⟩
  refine ⟨hnonempty, hnames, ?_, ?_, envTypes, envCtors,
    H.typesAdded, H.ctorsAdded, ?_, ?_⟩
  · intro target htarget
    exact (hproperties target htarget).1
  · intro ctor hctor
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    exact (hproperties target htarget).2.2 ctor hctor |>.1
  · intro target htarget
    exact (hproperties target htarget).2.1
  · intro ctor hctor
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    exact (hproperties target htarget).2.2 ctor hctor |>.2

theorem TrInductDeclCore.toTrInductDecl
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ [])
    (hnames : decl.sourceNames.Nodup) :
    TrInductDecl env lparams nparams types isUnsafe decl := by
  exact ⟨TrInductDeclCore.sourceWF H hnonempty hnames,
    H.uvars, H.nparams, H.isUnsafe,
    envTypes, envCtors, H.typesAdded, H.ctorsAdded, H.types⟩

theorem TrInductDeclCore.nonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ []) :
    decl.types ≠ [] := by
  intro htarget
  have hlength :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.types
  rw [htarget] at hlength
  exact hsource (List.eq_nil_of_length_eq_zero hlength)

theorem TrInductDeclCore.types_length
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    types.length = decl.types.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.types

theorem TrInductDeclCore.typeAt
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    TrInductiveType env envTypes lparams types[i] decl.types[i] :=
  Lean4Lean.VerifyInductive.List.Forall₂.getElem H.types i hsource htarget

theorem TrInductDecl.typeAt
    (H : TrInductDecl env lparams nparams types isUnsafe decl)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    ∃ envTypes, env.addConsts decl.typeConstants = some envTypes ∧
      TrInductiveType env envTypes lparams types[i] decl.types[i] := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypesAdded,
    hctorsAdded, htypes⟩
  exact ⟨envTypes, htypesAdded,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem htypes i hsource htarget⟩

theorem TrInductiveType.ctors_length
    (H : TrInductiveType env envTypes lparams type target) :
    type.ctors.length = target.ctors.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.ctors

theorem TrInductiveType.ctorAt
    (H : TrInductiveType env envTypes lparams type target)
    (i : Nat) (hsource : i < type.ctors.length)
    (htarget : i < target.ctors.length) :
    TrSourceConst envTypes lparams type.ctors[i].name type.ctors[i].type
      target.ctors[i] :=
  Lean4Lean.VerifyInductive.List.Forall₂.getElem H.ctors i hsource htarget

/-- Inductive metadata does not affect translation of the source header:
only visibility, universe parameters, name, and type cross the production /
abstract boundary. -/
theorem TrSourceConst.inductInfo
    (H : TrSourceConst env lparams name type ci')
    (hlevelParams : info.levelParams = lparams)
    (hname : info.name = name)
    (htype : info.type = type)
    (hvisible : safety ≤
      (if info.isUnsafe then DefinitionSafety.unsafe else .safe)) :
    TrConstVal safety env (.inductInfo info) ci' := by
  subst lparams
  subst name
  subst type
  constructor
  · exact ⟨by simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hvisible,
      H.uvars.symm, H.type⟩
  · exact H.name.symm

/-- The complete metadata-enriched production header array still translates
pointwise to the abstract mutual type constants. -/
theorem AddInductive.inductiveTypeInfos.translated
    {decl : VInductDecl}
    (Htypes : List.Forall₂
      (TrInductiveType env envTypes lparams)
      indTypes.toList decl.types)
    (hindices : stats.nindices.toList = decl.types.map (·.numIndices))
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    List.Forall₂
      (fun info (type : VInductiveType) =>
        TrConstVal safety env (.inductInfo info) type.toVConstVal ∧
          type.toVConstant.WF env)
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).toList
      decl.types := by
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
  have hindicesLength : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, hindices, List.length_map]
    simpa using htypesLength.symm
  have hinfosLength :
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).toList.length = decl.types.length := by
    simp [AddInductive.inductiveTypeInfos, hindicesLength, htypesLength]
  apply List.forall₂_of_getElem hinfosLength
  intro i hiInfo hiTarget
  have hiSource : i < indTypes.toList.length := by
    simpa [htypesLength] using hiTarget
  have Htype := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes i
    hiSource hiTarget
  constructor
  · apply Lean4Lean.VerifyInductive.TrSourceConst.inductInfo Htype.header
    · simp [AddInductive.inductiveTypeInfos]
    · simp [AddInductive.inductiveTypeInfos]
    · simp [AddInductive.inductiveTypeInfos]
    · simpa [AddInductive.inductiveTypeInfos, hindicesLength] using hvisible
  · exact Htype.header.wf

def ownedConstructors
    (types : List InductiveType) : List (InductiveType × Constructor) :=
  types.flatMap fun type => type.ctors.map (type, ·)

def TrOwnedConstructor (env envTypes : VEnv) (lparams : List Name) :
    (InductiveType × Constructor) →
      (VInductiveType × VConstVal) → Prop
  | (type, ctor), (target, ctor') =>
    TrInductiveType env envTypes lparams type target ∧
      TrSourceConst envTypes lparams ctor.name ctor.type ctor'

theorem TrInductiveType.ownedConstructors
    (H : TrInductiveType env envTypes lparams type target) :
    List.Forall₂ (TrOwnedConstructor env envTypes lparams)
      (type.ctors.map (type, ·)) (target.ctors.map (target, ·)) := by
  have aux : ∀ {ctors ctors'},
      List.Forall₂ (fun ctor ctor' =>
        TrSourceConst envTypes lparams ctor.name ctor.type ctor')
        ctors ctors' →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (ctors.map (type, ·)) (ctors'.map (target, ·)) := by
    intro ctors ctors' hctors
    induction hctors with
    | nil => exact .nil
    | cons h _ ih => exact .cons ⟨H, h⟩ ih
  exact aux H.ctors

theorem TrInductDecl.ownedConstructors
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    ∃ envTypes,
      env.addConsts decl.typeConstants = some envTypes ∧
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (Lean4Lean.VerifyInductive.ownedConstructors types)
        decl.ownedConstructors := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypesAdded,
    hctorsAdded, htypes⟩
  refine ⟨envTypes, htypesAdded, ?_⟩
  have aux : ∀ {types targets},
      List.Forall₂ (TrInductiveType env envTypes lparams) types targets →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (Lean4Lean.VerifyInductive.ownedConstructors types)
        (targets.flatMap fun target => target.ctors.map (target, ·)) := by
    intro types targets htypes
    induction htypes with
    | nil => exact .nil
    | cons h _ ih =>
      simpa [Lean4Lean.VerifyInductive.ownedConstructors] using
        Lean4Lean.VerifyInductive.List.Forall₂.append'
          (Lean4Lean.VerifyInductive.TrInductiveType.ownedConstructors h) ih
  simpa [VInductDecl.ownedConstructors] using aux htypes

theorem TrInductDeclCore.ownedConstructors
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    List.Forall₂ (TrOwnedConstructor env envTypes lparams)
      (Lean4Lean.VerifyInductive.ownedConstructors types)
      decl.ownedConstructors := by
  have aux : ∀ {types targets},
      List.Forall₂ (TrInductiveType env envTypes lparams) types targets →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (Lean4Lean.VerifyInductive.ownedConstructors types)
        (targets.flatMap fun target => target.ctors.map (target, ·)) := by
    intro types targets htypes
    induction htypes with
    | nil => exact .nil
    | cons h _ ih =>
      simpa [Lean4Lean.VerifyInductive.ownedConstructors] using
        Lean4Lean.VerifyInductive.List.Forall₂.append'
          (Lean4Lean.VerifyInductive.TrInductiveType.ownedConstructors h) ih
  simpa [VInductDecl.ownedConstructors] using aux H.types

theorem TrInductDeclCore.ownedConstructors_length
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    (Lean4Lean.VerifyInductive.ownedConstructors types).length =
      decl.ownedConstructors.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors H)

theorem TrInductDecl.ownedConstructors_length
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    (Lean4Lean.VerifyInductive.ownedConstructors types).length =
      decl.ownedConstructors.length := by
  rcases Lean4Lean.VerifyInductive.TrInductDecl.ownedConstructors H with
    ⟨_, _, hctors⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' hctors

theorem TrInductDecl.ownedConstructorAt
    (H : TrInductDecl env lparams nparams types isUnsafe decl)
    (i : Nat)
    (hsource : i < (Lean4Lean.VerifyInductive.ownedConstructors types).length)
    (htarget : i < decl.ownedConstructors.length) :
    ∃ envTypes, env.addConsts decl.typeConstants = some envTypes ∧
      TrOwnedConstructor env envTypes lparams
        (Lean4Lean.VerifyInductive.ownedConstructors types)[i]
        decl.ownedConstructors[i] := by
  rcases Lean4Lean.VerifyInductive.TrInductDecl.ownedConstructors H with
    ⟨envTypes, htypes, hctors⟩
  exact ⟨envTypes, htypes,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem hctors i hsource htarget⟩

/-- Indexed output certificate for one recursor per mutual-family member. -/
structure RecursorCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  length : recursors.length = decl.types.length
  shapes : ∀ i (htype : i < decl.types.length)
      (hrec : i < recursors.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

/-- Append-oriented invariant matching the recursor-generation loop. -/
structure RecursorBuildCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  covered : recursors.length ≤ decl.types.length
  shapes : ∀ i (hrec : i < recursors.length)
      (htype : i < decl.types.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

theorem RecursorBuildCertificate.empty (decl : VInductDecl) :
    RecursorBuildCertificate decl [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

theorem RecursorBuildCertificate.push
    (H : RecursorBuildCertificate decl recursors)
    (hnext : recursors.length < decl.types.length)
    (hshape : Nonempty
      (decl.RecursorShape decl.types[recursors.length] recursor)) :
    RecursorBuildCertificate decl (recursors ++ [recursor]) where
  covered := by simp; omega
  shapes i hrec htype := by
    by_cases hi : i < recursors.length
    · simpa [List.getElem_append, hi] using H.shapes i hi htype
    · have hieq : i = recursors.length := by simp at hrec; omega
      subst i
      simpa using hshape

theorem RecursorBuildCertificate.complete
    (H : RecursorBuildCertificate decl recursors)
    (hcomplete : recursors.length = decl.types.length) :
    RecursorCertificate decl recursors where
  length := hcomplete
  shapes i htype hrec := H.shapes i hrec htype

theorem RecursorCertificate.forall₂
    (H : RecursorCertificate decl recursors) :
    List.Forall₂ (fun type recursor =>
      Nonempty (decl.RecursorShape type recursor))
      decl.types recursors := by
  apply List.forall₂_of_getElem H.length.symm
  intro i htype hrec
  exact H.shapes i htype hrec

/-- Indexed output certificate for exactly one iota rule per owned
constructor, in the same flattened order used for minors. -/
structure IotaCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) : Prop where
  length : block.rules.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < block.rules.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 block.rules[i])

theorem IotaCertificate.forall₂
    (H : IotaCertificate env decl block) :
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule env block owned.1 owned.2 rule))
      decl.ownedConstructors block.rules := by
  apply List.forall₂_of_getElem H.length.symm
  intro i hctor hrule
  exact H.rules i hctor hrule

/-- Rule-list certificate used when nested restoration appends auxiliary
rules after the primary rules corresponding to source constructors. -/
structure IotaListCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) (ruleList : List VDefEq) : Prop where
  length : ruleList.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < ruleList.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 ruleList[i])

/-- Append-oriented iota invariant matching the per-family batches emitted by
`mkRecRules`. The rule list may later become either the complete ordinary
list or the primary prefix retained by nested restoration. -/
structure IotaBuildCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) (rules : List VDefEq) : Prop where
  covered : rules.length ≤ decl.ownedConstructors.length
  shapes : ∀ i (hrule : i < rules.length)
      (hctor : i < decl.ownedConstructors.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 rules[i])

theorem IotaBuildCertificate.empty
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) :
    IotaBuildCertificate env decl block [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

theorem IotaBuildCertificate.push
    (H : IotaBuildCertificate env decl block rules)
    (hnext : rules.length < decl.ownedConstructors.length)
    (hshape : Nonempty (decl.IotaRule env block
      decl.ownedConstructors[rules.length].1
      decl.ownedConstructors[rules.length].2 rule)) :
    IotaBuildCertificate env decl block (rules ++ [rule]) where
  covered := by simp; omega
  shapes i hrule hctor := by
    by_cases hold : i < rules.length
    · simpa [List.getElem_append, hold] using H.shapes i hold hctor
    · have hi : i = rules.length := by simp at hrule; omega
      subst i
      simpa using hshape

theorem IotaBuildCertificate.append
    (H : IotaBuildCertificate env decl block rules)
    (hlen : newRules.length + rules.length ≤
      decl.ownedConstructors.length)
    (hshapes : ∀ i (hi : i < newRules.length),
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[rules.length + i].1
        decl.ownedConstructors[rules.length + i].2 newRules[i])) :
    IotaBuildCertificate env decl block (rules ++ newRules) := by
  induction newRules generalizing rules with
  | nil => simpa using H
  | cons rule newRules ih =>
      have hnext : rules.length < decl.ownedConstructors.length := by
        simp at hlen
        omega
      have hhead := hshapes 0 (by simp)
      have Hpush := H.push hnext (by simpa using hhead)
      have Htail := ih Hpush (by
          simp at hlen ⊢
          omega) (by
          intro i hi
          have h := hshapes (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using h)
      simpa [List.append_assoc] using Htail

theorem IotaBuildCertificate.complete
    (H : IotaBuildCertificate env decl block rules)
    (hcomplete : rules.length = decl.ownedConstructors.length) :
    IotaListCertificate env decl block rules where
  length := hcomplete
  rules i hctor hrule := H.shapes i hrule hctor

theorem IotaBuildCertificate.completeBlock
    (H : IotaBuildCertificate env decl block block.rules)
    (hcomplete : block.rules.length = decl.ownedConstructors.length) :
    IotaCertificate env decl block where
  length := hcomplete
  rules i hctor hrule := H.shapes i hrule hctor

theorem IotaListCertificate.forall₂
    (H : IotaListCertificate env decl block ruleList) :
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule env block owned.1 owned.2 rule))
      decl.ownedConstructors ruleList := by
  apply List.forall₂_of_getElem H.length.symm
  intro i hctor hrule
  exact H.rules i hctor hrule

/-- Generator-facing form of ordinary compilation. Its indexed fields match
the loops in `mkRecInfos` and `mkRecRules`; `ordinary` below converts them to
the independent list-relational specification. -/
structure OrdinaryCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  recursors : RecursorCertificate decl block.recursors
  rules : IotaCertificate env decl block
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- The executable block-name check contains the original type and
constructor names as an exact prefix. Consequently its global freshness
certificate supplies precisely the name-uniqueness field of `SourceWF`. -/
theorem sourceNames_nodup_ofBlock
    {block : VInductBlock} {decl : VInductDecl}
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    decl.sourceNames.Nodup := by
  rw [htypes, hctors] at hnames
  simp only [List.map_append] at hnames
  exact (List.nodup_append.mp hnames).1

theorem OrdinaryCompilationCertificate.sourceNames_nodup
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.sourceNames.Nodup :=
  sourceNames_nodup_ofBlock H.types H.ctors H.names

theorem TrInductDeclCore.toTrInductDeclOfOrdinaryCompilation
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ [])
    (Hcompile : OrdinaryCompilationCertificate env decl block) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDecl H
    (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty H hsource)
    Hcompile.sourceNames_nodup

theorem OrdinaryCompilationCertificate.ordinary
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.OrdinaryCompilation env block where
  types := H.types
  ctors := H.ctors
  recursors := H.recursors.forall₂
  rules := H.rules.forall₂
  names := H.names

theorem OrdinaryCompilationCertificate.compilesTo
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.CompilesTo env block :=
  .ordinary H.ordinary

/-- Indexed, generator-facing form of nested compilation. The primary
recursors and rules use the same certificates as ordinary compilation, while
the restoration-only suffix is isolated to deterministic names and guarded
right-hand sides. -/
structure NestedCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) where
  main : VInductiveType
  rest : List VInductiveType
  types_source : decl.types = main :: rest
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  primaryRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  recursors_eq : block.recursors = primaryRecursors ++ auxiliaryRecursors
  primary_recursors : RecursorCertificate decl primaryRecursors
  auxiliary_names : auxiliaryRecursors.map (·.name) =
    (List.range auxiliaryRecursors.length).map fun i =>
      (decl.recursorName main).appendIndexAfter (i + 1)
  primaryRules : List VDefEq
  auxiliaryRules : List VDefEq
  rules_eq : block.rules = primaryRules ++ auxiliaryRules
  primary_rules : IotaListCertificate env decl block primaryRules
  auxiliary_guarded : ∀ rule ∈ auxiliaryRules,
    ∃ fieldVars, rule.rhs.GuardedIota
      (block.recursors.map (·.name)) fieldVars 0
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))

theorem NestedCompilationCertificate.sourceNames_nodup
    (H : NestedCompilationCertificate env decl block) :
    decl.sourceNames.Nodup :=
  sourceNames_nodup_ofBlock H.types H.ctors H.names

theorem TrInductDeclCore.toTrInductDeclOfNestedCompilation
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ [])
    (Hcompile : NestedCompilationCertificate env decl block) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDecl H
    (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty H hsource)
    Hcompile.sourceNames_nodup

def NestedCompilationCertificate.nested
    (H : NestedCompilationCertificate env decl block) :
    decl.NestedCompilation env block where
  main := H.main
  rest := H.rest
  types_source := H.types_source
  types := H.types
  ctors := H.ctors
  primaryRecursors := H.primaryRecursors
  auxiliaryRecursors := H.auxiliaryRecursors
  recursors_eq := H.recursors_eq
  primary_recursors := H.primary_recursors.forall₂
  auxiliary_names := H.auxiliary_names
  primaryRules := H.primaryRules
  auxiliaryRules := H.auxiliaryRules
  rules_eq := H.rules_eq
  primary_rules := H.primary_rules.forall₂
  auxiliary_guarded := H.auxiliary_guarded
  names := H.names

theorem NestedCompilationCertificate.compilesTo
    (H : NestedCompilationCertificate env decl block) :
    decl.CompilesTo env block := .nested H.nested

/-- Append-oriented restoration invariant for the auxiliary recursor/rule
suffix. It mirrors `processRec`: recursors receive consecutive `main.recN`
names, while restored auxiliary rules must retain a guarded RHS. -/
structure AuxiliaryRestorationPrefix (decl : VInductDecl)
    (block : VInductBlock) (main : VInductiveType)
    (recursors : List VConstVal) (rules : List VDefEq) : Prop where
  names : recursors.map (·.name) =
    (List.range recursors.length).map fun i =>
      (decl.recursorName main).appendIndexAfter (i + 1)
  guarded : ∀ rule ∈ rules, ∃ fieldVars,
    rule.rhs.GuardedIota (block.recursors.map (·.name)) fieldVars 0

theorem AuxiliaryRestorationPrefix.empty
    (decl : VInductDecl) (block : VInductBlock) (main : VInductiveType) :
    AuxiliaryRestorationPrefix decl block main [] [] where
  names := rfl
  guarded _ h := by simp at h

theorem AuxiliaryRestorationPrefix.pushRecursor
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (hname : recursor.name =
      (decl.recursorName main).appendIndexAfter (recursors.length + 1)) :
    AuxiliaryRestorationPrefix decl block main
      (recursors ++ [recursor]) rules where
  names := by
    simp only [List.map_append, List.map_singleton, List.length_append,
      List.length_singleton, List.range_succ, hname, H.names,
      List.map_concat, Function.comp_apply]
  guarded := H.guarded

theorem AuxiliaryRestorationPrefix.appendRules
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (hnew : ∀ rule ∈ newRules, ∃ fieldVars,
      rule.rhs.GuardedIota (block.recursors.map (·.name)) fieldVars 0) :
    AuxiliaryRestorationPrefix decl block main recursors
      (rules ++ newRules) where
  names := H.names
  guarded rule hrule := by
    rcases List.mem_append.mp hrule with hold | hnewRule
    · exact H.guarded rule hold
    · exact hnew rule hnewRule

/-- Final nested-compilation assembly for the actual restored primary
recursors and rules. Unlike the ordinary shortcut, these need not be the
lowered constants verbatim: restoration may rewrite their telescopes while
preserving the independent recursor/iota specifications. -/
def NestedCompilationCertificate.ofRestoration
    (decl : VInductDecl) (block : VInductBlock)
    (main : VInductiveType) (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (HprimaryRecursors : RecursorCertificate decl primaryRecursors)
    (HprimaryRules : IotaBuildCertificate env decl block primaryRules)
    (hprimaryLength : primaryRules.length =
      decl.ownedConstructors.length)
    (Haux : AuxiliaryRestorationPrefix decl block main
      auxiliaryRecursors auxiliaryRules)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors =
      primaryRecursors ++ auxiliaryRecursors)
    (hrules : block.rules = primaryRules ++ auxiliaryRules)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    NestedCompilationCertificate env decl block where
  main := main
  rest := rest
  types_source := htypesSource
  types := htypes
  ctors := hctors
  primaryRecursors := primaryRecursors
  auxiliaryRecursors := auxiliaryRecursors
  recursors_eq := hrecursors
  primary_recursors := HprimaryRecursors
  auxiliary_names := Haux.names
  primaryRules := primaryRules
  auxiliaryRules := auxiliaryRules
  rules_eq := hrules
  primary_rules := HprimaryRules.complete hprimaryLength
  auxiliary_guarded := Haux.guarded
  names := hnames

/-- Verification state for the outer inductive-construction monad. The local
context is represented by the same `MLCtx` used by the typechecker proof, while
the production reader retains the independently generated `_ind_fresh` names. -/
def MLCtxOnlyLams (m : TypeChecker.MLCtx) : Prop :=
  ∀ d ∈ m.decls, ∃ index fv name type bi kind,
    d = .cdecl index fv name type bi kind

theorem MLCtxOnlyLams.nil : MLCtxOnlyLams .nil := by
  intro d hd
  simp [TypeChecker.MLCtx.decls] at hd

theorem MLCtxOnlyLams.vlam
    (H : MLCtxOnlyLams m) :
    MLCtxOnlyLams (.vlam fv name type type' bi m) := by
  intro d hd
  simp only [TypeChecker.MLCtx.decls, List.mem_cons] at hd
  rcases hd with rfl | hd
  · exact ⟨_, _, _, _, _, _, rfl⟩
  · exact H d hd

structure ContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv

def initialContext (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context where
  env; lparams; safety; allowPrimitive; fuel

def ContextWF.initial {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) (lparams : List Name)
    (allowPrimitive : Bool) (fuel : FuelConfig) :
    ContextWF (initialContext env lparams safety allowPrimitive fuel) where
  venv := ves.venv safety
  checking := (wf.tr (safety := safety)).toCheckingValid
    (wf.hasPrimitives (safety := safety)) wf.safePrimitives
  mlctx := .nil
  mlctx_wf := trivial
  onlyLams := MLCtxOnlyLams.nil
  lctx_eq := rfl
  ngen_prefix := rfl
  indFresh := nofun
  kernelFresh := nofun

/-- Retain the local checker state while moving to a production and abstract
environment pair known to represent the same extension. -/
def ContextWF.withEnv (H : ContextWF c)
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hle : H.venv ≤ venv') :
    ContextWF { c with env := env' } where
  venv := venv'
  checking := hchecking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh

theorem ContextWF.current_not_mem (H : ContextWF c) :
    ⟨c.ngen.curr⟩ ∉ H.mlctx.vlctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.indFresh _ hmem)

theorem ContextWF.kernel_reserves_current (H : ContextWF c) :
    ({} : TypeChecker.State).ngen.Reserves ⟨c.ngen.curr⟩ := by
  apply NameGenerator.Reserves.num_of_prefix_ne
  simp [H.ngen_prefix]

def ContextWF.withLocalDecl (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    ContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := ⟨H.mlctx_wf,
    H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩
  onlyLams := H.onlyLams.vlam
  lctx_eq := by
    change H.mlctx.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi =
      c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    rw [H.lctx_eq]
  ngen_prefix := by
    change c.ngen.namePrefix = `_ind_fresh
    exact H.ngen_prefix
  indFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact c.ngen.next_reserves_self
    · exact (H.indFresh _ hmem).mono NameGenerator.LE.next
  kernelFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact H.kernel_reserves_current
    · exact H.kernelFresh _ hmem

theorem ContextWF.withLocalDecl_venv (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).venv = H.venv := rfl

theorem ContextWF.withLocalDecl_toCtx (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

theorem ContextWF.findCDecl (H : ContextWF c)
    (hmem : fv ∈ H.mlctx.vlctx.fvars) :
    ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
  rcases (H.mlctx_wf.tr.find?_eq_some (fv := fv)).2 hmem with
    ⟨decl, hfind⟩
  have hfindDecls : H.mlctx.decls.find? (fv == ·.fvarId) = some decl := by
    rw [← H.mlctx_wf.find?_eq]
    exact hfind
  have hdeclMem : decl ∈ H.mlctx.decls :=
    List.mem_of_find?_eq_some hfindDecls
  rcases H.onlyLams decl hdeclMem with
    ⟨index, fv', name, type, bi, kind, hdecl⟩
  subst decl
  have hfv : fv' = fv := by
    have hpred := List.find?_some hfindDecls
    have hfv' : fv = fv' := by simpa [LocalDecl.fvarId] using hpred
    exact hfv'.symm
  subst fv'
  refine ⟨index, name, type, bi, kind, ?_⟩
  rw [← H.lctx_eq]
  exact hfind

/-- Operational local-context invariant used by structurally exploded
recursor traversals.  It records exactly what those proofs need in order to
retain generated binders, without claiming semantic typing for their domains. -/
structure BindingContextWF (c : AddInductive.Context) where
  wf : c.lctx.WF
  onlyLams : ∀ d ∈ c.lctx.toList, ∃ index fv name type bi kind,
    d = .cdecl index fv name type bi kind
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  fresh : ∀ fv ∈ c.lctx.fvars, c.ngen.Reserves fv
  findCDecl : ∀ fv ∈ c.lctx.fvars, ∃ index name type bi kind,
    c.lctx.find? fv = some (.cdecl index fv name type bi kind)

theorem ContextWF.toBindingContextWF (H : ContextWF c) :
    BindingContextWF c where
  wf := H.lctx_eq ▸ H.mlctx_wf.tr.1
  onlyLams := by
    intro d hd
    apply H.onlyLams d
    rw [← H.mlctx_wf.toList_eq, H.lctx_eq]
    exact hd
  ngen_prefix := H.ngen_prefix
  fresh := by
    intro fv hfv
    apply H.indFresh fv
    rw [← H.mlctx_wf.tr.fvars_eq, H.lctx_eq]
    exact hfv
  findCDecl fv hfv := H.findCDecl <| by
    rw [← H.mlctx_wf.tr.fvars_eq, H.lctx_eq]
    exact hfv

theorem BindingContextWF.current_not_mem (H : BindingContextWF c) :
    ⟨c.ngen.curr⟩ ∉ c.lctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.fresh _ hmem)

def BindingContextWF.withLocalDecl (H : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    BindingContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  wf := H.wf.mkLocalDecl <| by
    rw [H.wf.find?_eq_find?_toList]
    by_contra hne
    rcases Option.ne_none_iff_exists.mp hne with ⟨d, hfind⟩
    apply H.current_not_mem
    rw [LocalContext.fvars]
    apply List.mem_map.2
    have hfind' := hfind.symm
    refine ⟨d, List.mem_of_find?_eq_some hfind', ?_⟩
    have hp := List.find?_some hfind'
    have heq : ⟨c.ngen.curr⟩ = d.fvarId := by simpa using hp
    exact heq.symm
  onlyLams := by
    intro d hd
    simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨_, _, _, _, _, _, rfl⟩
    · exact H.onlyLams d hd
  ngen_prefix := H.ngen_prefix
  fresh := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact c.ngen.next_reserves_self
    · exact (H.fresh _ hmem).mono NameGenerator.LE.next
  findCDecl := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨c.lctx.decls.size, name, ty, bi, .default, ?_⟩
      simp [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
    · rcases H.findCDecl fv hmem with
        ⟨index, oldName, oldType, oldBi, kind, hfind⟩
      refine ⟨index, oldName, oldType, oldBi, kind, ?_⟩
      simp only [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
      rw [if_neg]
      · exact hfind
      · intro heq
        have hsame : ⟨c.ngen.curr⟩ = fv := LawfulBEq.eq_of_beq heq
        have : fv = ⟨c.ngen.curr⟩ := hsame.symm
        subst fv
        exact H.current_not_mem hmem

theorem withLocalDecl.WF {k : Expr → AddInductive.M α} (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  have _Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  exact Hk

/-- Invert the syntax-directed part of a translated forall while retaining the
definitional equality introduced by normalization.  Header and constructor
loops use this after `whnf`: the production expression is syntactically a
forall, but its abstract translation need only be definitionally equal to one. -/
theorem TrExpr.forallE_source
    (H : TrExpr env Us Δ (.forallE name dom body bi) type') :
    ∃ dom' body',
      TrExprS env Us Δ dom dom' ∧
      TrExprS env Us ((none, .vlam dom') :: Δ) body body' ∧
      env.IsType Us.length Δ.toCtx dom' ∧
      env.IsType Us.length (dom' :: Δ.toCtx) body' ∧
      env.IsDefEqU Us.length Δ.toCtx (.forallE dom' body') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | forallE HdomType HbodyType Hdom Hbody =>
    exact ⟨_, _, Hdom, Hbody, HdomType, HbodyType, Hdefeq⟩

/-- Invert a production sort after normalization, retaining both its universe
translation and its definitional equality to the abstract source tail. -/
theorem TrExpr.sort_source
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEqU Us.length Δ.toCtx (.sort level') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | sort Hlevel => exact ⟨_, Hlevel, Hdefeq⟩

/-- A translated production sort pins the type of the abstract conversion to
the successor sort, not merely to an existentially hidden type. -/
theorem TrExpr.sort_result
    (henv : VEnv.WF env) (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEq Us.length Δ.toCtx type' (.sort level')
        (.sort (.succ level')) := by
  rcases TrExpr.sort_source H with ⟨level', hlevel, typeEq⟩
  exact ⟨level', hlevel, typeEq.symm.of_r henv hctx
    (.sort (.of_ofLevel hlevel))⟩

/-- Aggregates the final `ensureSort` translation with the independently
recorded parameter/index telescope into the public `TypeShape` judgment. -/
theorem TrExpr.typeShape
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : Δ.toCtx = indices.reverse ++ ownParams.reverse)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) result) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, hresult⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars, hctxEq] using hresult⟩

/-- Context-conversion form of `typeShape`.  This is the form needed by the
executable telescope because annotation consumption changes binder domains
definitionally, while preserving the same de Bruijn context shape. -/
theorem TrExpr.typeShapeOfDefEqCtx
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx env Us.length []
      (indices.reverse ++ ownParams.reverse) Δ.toCtx)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) result) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, hresult⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  have hresult' := hresult.defeqDFC henv.ordered (hctxEq.symm henv.ordered)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hresult'⟩

/-- Context- and result-conversion form of `typeShape`.  Repeated executable
`whnf` calls need only remain definitionally equal to the unconsumed source
telescope; they need not choose that telescope's exact syntax. -/
theorem TrExpr.typeShapeOfDefEqCtxResult
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result translatedResult exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx env Us.length []
      (indices.reverse ++ ownParams.reverse) Δ.toCtx)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hresultEq : env.IsDefEqU Us.length Δ.toCtx result translatedResult)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) translatedResult) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, htranslated⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  have hsourceType := htranslated.hasType.1.defeqU_l henv hctx.toCtx
    hresultEq.symm
  have hsourceEqU := hresultEq.trans henv hctx.toCtx ⟨_, htranslated⟩
  have hsourceEq := hsourceEqU.of_l henv hctx.toCtx hsourceType
  have hsourceEq' := hsourceEq.defeqDFC henv.ordered
    (hctxEq.symm henv.ordered)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hsourceEq'⟩

/-- Close a sort-level definitional equality over a dependent forall
telescope.  This is the abstraction step needed when the executable checker
performs a fresh `whnf` after opening each binder. -/
theorem VExpr.wrapForalls_defeq
    {env : VEnv} {U : Nat} {domains Γ : List VExpr}
    {body body' : VExpr} {bodyLevel : VLevel}
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType U))
    (hbody : env.IsDefEq U (domains.reverse ++ Γ)
      body body' (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U Γ
      (VExpr.wrapForalls domains body)
      (VExpr.wrapForalls domains body') (.sort resultLevel) := by
  induction domains generalizing Γ with
  | nil =>
    exact ⟨bodyLevel, by simpa [VExpr.wrapForalls] using hbody⟩
  | cons dom domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (dom :: Γ))
        (env.IsType U) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hdomCtx : OnCtx (dom :: Γ) (env.IsType U) :=
      OnCtx.append_right hctx'
    rcases hdomCtx.2 with ⟨domLevel, hdom⟩
    rcases ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using hbody) with
      ⟨resultLevel, hrest⟩
    exact ⟨.imax domLevel resultLevel, .forallEDF hdom hrest⟩

/-- Opening a source binder with the fresh free variable chosen by the
production checker leaves its abstract body unchanged: the extended `VLCtx`
maps that free variable back to the new outermost de Bruijn variable. -/
theorem ContextWF.instantiateFresh (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam ty') :: Hc.mlctx.vlctx) body body') :
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body' := by
  dsimp only
  rw [Expr.instantiate1_eq]
  exact hbody.inst_fvar Hc.checking.tr.wf.ordered
    (Hc.withLocalDecl htr hty).mlctx_wf.tr.wf

/-- Instantiate a source binder with an existing translated argument whose
cached type is only definitionally equal to the binder domain. -/
theorem ContextWF.instantiateDefEq (Hc : ContextWF c)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (harg : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx arg arg')
    (hargType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      arg' argType')
    (heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' argType') :
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 arg) (body'.inst arg') := by
  have hargType' := hargType.defeqU_r Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq.symm
  rw [Expr.instantiate1_eq]
  exact hbody.inst Hc.checking.tr.wf.ordered hargType' harg

/-- Semantic certificate for the production checker's removal of binder type
annotations.  The consumed syntax may translate to a different abstract term,
but it must remain a type definitionally equal to the source domain. -/
structure ContextWF.ConsumedDomain (Hc : ContextWF c)
    (dom : Expr) (source' consumed' : VExpr) : Prop where
  source : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source'
  consumed : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
    dom.consumeTypeAnnotations consumed'
  isType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx consumed'
  source_defeq : ∃ u, Hc.venv.IsDefEq c.lparams.length Hc.mlctx.vlctx.toCtx
    source' consumed' (.sort u)

theorem Expr.consumeTypeAnnotations_eq_self {dom : Expr}
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false) :
    dom.consumeTypeAnnotations = dom := by
  simp [hopt, hauto, hout, hsemi]

/-- Removing binder annotations only selects subexpressions of the original
domain, so it cannot introduce a new free-variable dependency. -/
theorem Expr.consumeTypeAnnotations_fvarsIn
    (H : FVarsIn P e) : FVarsIn P e.consumeTypeAnnotations := by
  rw (occs := .pos [1]) [Expr.consumeTypeAnnotations_eq]
  split
  · rename_i hannotation
    cases e <;> simp_all [Expr.isOptParam, Expr.isAutoParam,
      Expr.isAppOfArity, Expr.appFn!, Expr.appArg!, FVarsIn,
      -Expr.consumeTypeAnnotations_eq]
    case app fn arg =>
      cases fn <;> simp_all [Expr.isAppOfArity, FVarsIn,
        -Expr.consumeTypeAnnotations_eq]
      case app fn' arg' =>
        exact Expr.consumeTypeAnnotations_fvarsIn H.1.2
  · split
    · cases e <;> simp_all [Expr.isOutParam, Expr.isSemiOutParam,
        Expr.isAppOfArity, Expr.appArg!, FVarsIn,
        -Expr.consumeTypeAnnotations_eq]
      case app fn arg =>
        exact Expr.consumeTypeAnnotations_fvarsIn H.2
    · exact H
termination_by e

/-- Domains without a leading type annotation need no semantic transport. -/
theorem ContextWF.ConsumedDomain.unchanged (Hc : ContextWF c)
    (heq : dom.consumeTypeAnnotations = dom)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom') :
    Hc.ConsumedDomain dom dom' dom' := by
  rcases hty with ⟨u, hty⟩
  exact {
    source := htr
    consumed := heq.symm ▸ htr
    isType := ⟨u, hty⟩
    source_defeq := ⟨u, hty⟩ }

theorem ContextWF.ConsumedDomain.unannotated (Hc : ContextWF c)
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom') :
    Hc.ConsumedDomain dom dom' dom' :=
  .unchanged Hc (Expr.consumeTypeAnnotations_eq_self hopt hauto hout hsemi) htr hty

/-- Transport the source body translation to the annotation-consumed binder
type.  This is the bridge needed before opening the binder with the production
free variable. -/
theorem ContextWF.ConsumedDomain.body
    {c : AddInductive.Context} (Hc : ContextWF c)
    {dom body : Expr} {source' consumed' body' : VExpr}
    (H : Hc.ConsumedDomain dom source' consumed')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam source') :: Hc.mlctx.vlctx) body body') :
    ∃ body'', TrExprS Hc.venv c.lparams
        ((none, .vlam consumed') :: Hc.mlctx.vlctx) body body'' ∧
      Hc.venv.IsDefEqU c.lparams.length
        (source' :: Hc.mlctx.vlctx.toCtx) body' body'' := by
  rcases H.source_defeq with ⟨_, hdom⟩
  have hctx : VLCtx.IsDefEq Hc.venv c.lparams.length
      ((none, .vlam source') :: Hc.mlctx.vlctx)
      ((none, .vlam consumed') :: Hc.mlctx.vlctx) :=
    VLCtx.IsDefEq.cons
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) nofun (.vlam hdom)
  rcases hbody.defeqDFC Hc.checking.tr.wf hctx with ⟨body'', hbody''⟩
  exact ⟨body'', hbody'', hbody.uniq Hc.checking.tr.wf hctx hbody''⟩

/-- Move the source/body conversion produced by `body` into the
annotation-consumed context installed by the executable checker. -/
theorem ContextWF.ConsumedDomain.bodyDefEqConsumed
    {c : AddInductive.Context} (Hc : ContextWF c)
    {dom : Expr} {source' consumed' sourceBody body'' : VExpr}
    (H : Hc.ConsumedDomain dom source' consumed')
    (hbodyEq : Hc.venv.IsDefEqU c.lparams.length
      (source' :: Hc.mlctx.vlctx.toCtx) sourceBody body'') :
    Hc.venv.IsDefEqU c.lparams.length
      (consumed' :: Hc.mlctx.vlctx.toCtx) sourceBody body'' := by
  rcases H.source_defeq with ⟨_, hsource⟩
  have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (source' :: Hc.mlctx.vlctx.toCtx)
      (consumed' :: Hc.mlctx.vlctx.toCtx) :=
    .succ (.refl Hc.mlctx_wf.tr.wf.toCtx) hsource
  exact hbodyEq.defeqDFC Hc.checking.tr.wf.ordered hctx

/-- Semantic compatibility required of Lean's opaque annotation erasure.
It is kept as one named boundary condition until the translations of
`OptParam`, `AutoParam`, and output-parameter wrappers are verified directly. -/
def ConsumeTypeAnnotationsCompat : Prop :=
  ∀ (c : AddInductive.Context) (Hc : ContextWF c)
    {dom : Expr} {source' : VExpr},
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source' →
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx source' →
    ∃ consumed', Hc.ConsumedDomain dom source' consumed'

def ContextWF.typeChecker (H : ContextWF c) : TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC H.checking H.mlctx H.mlctx_wf c.fuel

@[simp] theorem ContextWF.typeChecker_lctx (H : ContextWF c) :
    H.typeChecker.lctx = c.lctx := by
  simp [ContextWF.typeChecker, TypeChecker.VContext.mkCheckingValidMLC, H.lctx_eq]

/-- Reuse a verified typechecker computation inside `AddInductive.M`. -/
theorem liftTypeChecker.WF {x : TypeChecker.M α} (Hc : ContextWF c)
    (Hx : TypeChecker.M.WF Hc.typeChecker {} x fun a _ => Q a) :
    ((monadLift x : AddInductive.M α) c).WF Q := by
  change (TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel x).WF Q
  rw [← Hc.lctx_eq]
  exact TypeChecker.M.WF.runCheckingValidMLC Hc.kernelFresh Hx

theorem checkTypeInContext.WF (Hc : ContextWF c)
    (hfvars : e.FVarsIn (· ∈ Hc.mlctx.vlctx.fvars)) :
    ((monadLift (TypeChecker.checkType e) : AddInductive.M Expr) c).WF fun ty =>
      ∃ e' ty', TrTyping Hc.venv c.lparams Hc.mlctx.vlctx e ty e' ty' :=
  liftTypeChecker.WF Hc (TypeChecker.checkType.WF hfvars)

theorem whnfInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  liftTypeChecker.WF Hc (TypeChecker.whnf.WF he)

/-- `whnf` preserves every admissible free-variable scope of its input, in
addition to preserving the abstract expression up to definitional equality.
The ordinary wrapper above projects this fact away; later mutual headers need
it to show normalization cannot introduce ambient or future cached
parameters. -/
theorem whnfInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.mlctx.vlctx e e₁ ∧
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  liftTypeChecker.WF Hc
    ((TypeChecker.Inner.whnf.WF he).run)

theorem ensureSortInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' ∧ ∃ u, e₁ = .sort u :=
  liftTypeChecker.WF Hc (TypeChecker.ensureSort.WF he)

theorem ensureSortInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF
      fun e₁ => Hc.typeChecker.FVarsBelow e e₁ ∧
        Hc.typeChecker.TrExpr e₁ e' ∧
        ∃ u, e₁ = .sort u := by
  change Hc.typeChecker.TrExprS e e' at he
  apply liftTypeChecker.WF (Q := fun e₁ =>
    Hc.typeChecker.FVarsBelow e e₁ ∧
      Hc.typeChecker.TrExpr e₁ e' ∧
      ∃ u, e₁ = .sort u) Hc
  simpa only [TypeChecker.ensureSort] using
    (TypeChecker.Inner.ensureSortCore.WF he).run.mono
      (fun _ _ _ h => And.intro h.2.2 (And.intro h.2.1 h.1))

theorem ensureTypeInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureType e) : AddInductive.M Expr) c).WF fun sort =>
      ∃ e'', TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e'' ∧
        ∃ u u', sort = .sort u ∧ VLevel.ofLevel c.lparams u = some u' ∧
          Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx e'' (.sort u') :=
  liftTypeChecker.WF Hc (TypeChecker.ensureType.WF he)

theorem isDefEqInContext.WF (Hc : ContextWF c)
    (he₁ : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e₁ e₁')
    (he₂ : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e₂ e₂') :
    ((monadLift (TypeChecker.isDefEq e₁ e₂) : AddInductive.M Bool) c).WF fun b =>
      b → Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx e₁' e₂' :=
  liftTypeChecker.WF Hc (TypeChecker.isDefEq.WF he₁ he₂)

theorem checkNoMVarNoFVar.closed
    (H : Kernel.Environment.checkNoMVarNoFVar env name e = .ok ()) :
    e.FVarsIn fun _ => False := by
  have hm : e.hasMVar = false := by
    cases hm : e.hasMVar
    · rfl
    · have he : Kernel.Environment.checkNoMVar env name e =
          .error (.declHasMVars env name e) := by
        unfold Kernel.Environment.checkNoMVar
        rw [hm]
        change Except.error _ = Except.error _
        rfl
      rw [Kernel.Environment.checkNoMVarNoFVar, he] at H
      contradiction
  have hf : e.hasFVar = false := by
    have hmok : Kernel.Environment.checkNoMVar env name e = .ok () := by
      unfold Kernel.Environment.checkNoMVar
      rw [hm]
      rfl
    cases hf : e.hasFVar
    · rfl
    · have he : Kernel.Environment.checkNoFVar env name e =
          .error (.declHasFVars env name e) := by
        unfold Kernel.Environment.checkNoFVar
        rw [hf]
        change Except.error _ = Except.error _
        rfl
      rw [Kernel.Environment.checkNoMVarNoFVar, hmok, he] at H
      contradiction
  apply Lean4Lean.fvarsIn_iff.mpr
  refine ⟨?_, Lean4Lean.fvarsIn_iff_hasMVar.mpr hm⟩
  · intro fv hmem
    rw [Lean4Lean.fvarsList_eq_nil.2 hf] at hmem
    contradiction

theorem checkClosedType.WF (Hc : ContextWF c) :
    (AddInductive.checkClosedType name type c).WF fun checkedType =>
      ∃ type' checkedType',
        TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
          type checkedType type' checkedType' := by
  change (c.env.checkNoMVarNoFVar name type >>= fun _ =>
    TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel
      (TypeChecker.checkType type)).WF _
  have hno : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := c.env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkTypeInContext.WF Hc (hclosed.mono fun _ h => False.elim h)

namespace checkInductiveTypes.loopType

/-- Abstract images of the concrete parameter cache after `done` parameter
binders and `depth` subsequent index binders.  Its recursive presentation
matches the executable `Array.push` order exactly. -/
def cachedParamVars : Nat → Nat → List VExpr
  | 0, _ => []
  | done + 1, depth =>
    (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
      [.bvar depth]

@[simp] theorem cachedParamVars_zero : cachedParamVars 0 depth = [] := rfl

@[simp] theorem cachedParamVars_succ :
    cachedParamVars (done + 1) depth =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
        [.bvar depth] := rfl

@[simp] theorem cachedParamVars_length :
    (cachedParamVars done depth).length = done := by
  induction done with
  | zero => rfl
  | succ done ih => simp [cachedParamVars_succ, ih]

theorem cachedParamVars_getElem? :
    (cachedParamVars done depth)[i]? =
      if i < done then some (.bvar (depth + (done - 1 - i))) else none := by
  induction done generalizing depth i with
  | zero => simp
  | succ done ih =>
    simp only [cachedParamVars_succ]
    by_cases hprior : i < done
    · rw [List.getElem?_append_left (by simp [hprior])]
      rw [List.getElem?_map, ih]
      simp only [hprior, if_true, Option.map_some]
      simp [VExpr.liftN]
      congr 2
      omega
    · by_cases hcurrent : i < done + 1
      · have hieq : i = done := by omega
        subst i
        simp
      · have hout : done + 1 ≤ i := by omega
        rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
        simp [hcurrent]

@[simp] theorem cachedParamVars_depth_succ :
    cachedParamVars done (depth + 1) =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) := by
  induction done with
  | zero => rfl
  | succ done ih =>
    simp [cachedParamVars_succ, ih, List.map_map, VExpr.liftN,
      Function.comp_def]

theorem cachedParamVars_eq_paramVars (decl : VInductDecl) :
    cachedParamVars decl.nparams depth = decl.paramVars depth := by
  apply List.ext_getElem?
  intro i
  rw [cachedParamVars_getElem?]
  by_cases hi : i < decl.nparams
  · rw [VInductDecl.paramVars, List.getElem?_map]
    rw [List.getElem?_reverse (by simp [hi])]
    have hj : decl.nparams - 1 - i < decl.nparams := by omega
    simp [hi, hj]
  · rw [List.getElem?_eq_none_iff.2 (by
      simp [VInductDecl.paramVars]
      omega)]
    simp [hi]

/-- Local invariant for the first header's common-parameter branch. -/
structure ParameterCachePrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (done depth : Nat) : Prop where
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (cachedParamVars done depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- A concrete cached parameter and the free-variable declaration that owns
it in the retained verifier context. -/
def CachedParameterDecl (param : Expr)
    (entry : Option (FVarId × List FVarId) × VLocalDecl) : Prop :=
  ∃ fv deps type,
    param = .fvar fv ∧ entry = (some (fv, deps), .vlam type)

/-- Structural companion to `ParameterCachePrefix`.  Cached parameter local
declarations form an exact suffix of the retained context; every index added
after the parameter phase belongs to `ambientDecls`.  The reverse is
intentional:
the executable array stores parameters from oldest to newest, while local
declarations are pushed at the head.

This suffix decomposition is what lets later mutual headers discard ambient
indices and not-yet-used cached parameters before applying
`TrExprS.uninstantiateAfterWeakFV`. -/
structure ParameterContextSuffix (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats) (depth : Nat) : Type where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : Hc.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  cached : List.Forall₂ CachedParameterDecl
    stats.params.toList.reverse parameterDecls
  narrowParams : List.Forall₂
    (TrExprS Hc.venv c.lparams parameterDecls)
    stats.params.toList (cachedParamVars stats.params.size 0)

/-- Reindex a parameter cache across statistics updates that leave the
cached parameter array unchanged. -/
def ParameterCachePrefix.reindex
    (H : ParameterCachePrefix env Us Δ stats done depth)
    (hparams : stats'.params = stats.params) :
    ParameterCachePrefix env Us Δ stats' done depth where
  params := by rw [hparams]; exact H.params
  paramFVars := by rw [hparams]; exact H.paramFVars

/-- Reindex the exact cached suffix across a statistics update that changes
only per-header output fields. -/
def ParameterContextSuffix.reindex
    (H : ParameterContextSuffix Hc stats depth)
    (hparams : stats'.params = stats.params) :
    ParameterContextSuffix Hc stats' depth where
  ambientDecls := H.ambientDecls
  parameterDecls := H.parameterDecls
  context := H.context
  prefixLength := H.prefixLength
  cached := by rw [hparams]; exact H.cached
  narrowParams := by rw [hparams]; exact H.narrowParams

@[simp] theorem _root_.Lean4Lean.VExpr.containsAnyConst_liftN
    {e : VExpr} {n k : Nat} {names : List Name} :
    (e.liftN n k).containsAnyConst names = e.containsAnyConst names := by
  induction e generalizing k <;>
    simp [VExpr.liftN, VExpr.containsAnyConst, *]

def _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts
    (names : List Name) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) →
    mapped.containsAnyConst names = false

theorem _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : checkPositivityStep.VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    checkPositivityStep.VLCtx.NoIndConsts names ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    simpa only [VExpr.containsAnyConst_liftN] using H hfind

abbrev _root_.Lean4Lean.VLCtx.NoIndConsts :=
  checkPositivityStep.VLCtx.NoIndConsts

theorem _root_.Lean4Lean.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    VLCtx.NoIndConsts names ((ofv, d) :: Δ) :=
  checkPositivityStep.VLCtx.NoIndConsts.cons H hvalue

theorem ParameterContextSuffix.noIndConsts
    (H : ParameterContextSuffix Hc stats depth) (names : List Name) :
    checkPositivityStep.VLCtx.NoIndConsts names H.parameterDecls := by
  have go : ∀ {params : List Expr} {entries : VLCtx},
      List.Forall₂ CachedParameterDecl params entries →
      checkPositivityStep.VLCtx.NoIndConsts names entries := by
    intro params entries hcached
    induction hcached with
    | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
    | @cons param entry params entries hentry _ ih =>
      rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
      exact checkPositivityStep.VLCtx.NoIndConsts.cons ih rfl
  intro v mapped type hfind
  exact go H.cached hfind

/-- A semantic header scope embedded in the larger executable local context.
`expanded` is the literal weakening of the narrow scope; it is kept separate
from `runtime` because annotation consumption can replace an installed binder
domain by a merely definitionally equal expression. -/
structure NarrowRuntimeScope (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  noIndConsts : ∀ names,
    checkPositivityStep.VLCtx.NoIndConsts names scope

def NarrowRuntimeScope.mono {env env' : VEnv} (henv : env ≤ env')
    (H : NarrowRuntimeScope env Us scope runtime) :
    NarrowRuntimeScope env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  noIndConsts := H.noIndConsts

theorem NarrowRuntimeScope.scopeWF
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF) :
    scope.WF env Us.length :=
  H.lift.wf henv H.context.wf

/-- Restrict a translated concrete expression to its semantic header scope.
The source-side free-variable premise is the deliberate ownership boundary:
ambient declarations retained by the executable loop may not occur. -/
theorem NarrowRuntimeScope.restrict
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ e', TrExprS env Us scope e e' := by
  exact htr.weakFV'_inv henv H.lift
    (H.context.symm henv.ordered) hclosed hfvars

/-- Restriction together with the definitional equality obtained by
weakening the narrowed translation back into the executable context. -/
theorem NarrowRuntimeScope.restrictEq
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ narrow', TrExprS env Us scope e narrow' ∧
      env.IsDefEqU Us.length runtime.toCtx e'
        (narrow'.lift' H.shift) := by
  rcases H.restrict henv htr hclosed hfvars with ⟨narrow', hnarrow⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  exact ⟨narrow', hnarrow,
    htr.uniq henv (H.context.symm henv.ordered) hweak⟩

/-- The abstract target computed in the executable context is the weakening
of the independently translated narrow target. -/
theorem NarrowRuntimeScope.fullTargetEq
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

/-- Restrict a runtime expression translation whose target is already known
in the semantic scope.  This packages the inverse-weakening argument needed
after executable WHNF: restrict the normalized source translation, compare
both weakened targets in the runtime context, then cancel the weakening. -/
theorem NarrowRuntimeScope.restrictTrExpr
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope input narrowTarget)
    (hfullInput : TrExpr env Us runtime input fullTarget)
    (hfullResult : TrExpr env Us runtime result fullTarget)
    (hclosed : Closed result 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) result) :
    TrExpr env Us scope result narrowTarget := by
  rcases hfullResult with ⟨resultFull, hresultFull, hresultTarget⟩
  rcases H.restrictEq henv hresultFull hclosed hfvars with
    ⟨resultNarrow, hresultNarrow, hresultLift⟩
  have htargetLift := H.fullTargetEq henv hnarrow hfullInput
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hlift : env.IsDefEqU Us.length runtime.toCtx
      (resultNarrow.lift' H.shift) (narrowTarget.lift' H.shift) :=
    (hresultLift.symm.trans henv hruntimeWF hresultTarget).trans
      henv hruntimeWF htargetLift.symm
  have hexpanded := hlift.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  have hnarrowEq : env.IsDefEqU Us.length scope.toCtx
      resultNarrow narrowTarget :=
    (VEnv.IsDefEqU.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
      hexpanded
  exact ⟨resultNarrow, hresultNarrow, hnarrowEq⟩

/-- Transfer a runtime typing result for a translated concrete expression
back to its independently translated target in the narrow scope. -/
theorem NarrowRuntimeScope.hasTypeOfFull
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExprS env Us runtime e full')
    (htype : env.HasType Us.length runtime.toCtx full' (.sort u)) :
    env.HasType Us.length scope.toCtx narrow' (.sort u) := by
  have htarget := H.fullTargetEq henv hnarrow
    (hfull.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htarget.symm
  have hexpanded := hliftTyped.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

/-- Move a successful runtime result-sort check back to the independent
narrow header scope.  Both translations are tied to the same concrete
residual, so uniqueness in the runtime context followed by inverse weakening
provides the narrow result equality. -/
theorem NarrowRuntimeScope.resultSort
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full')
    (hsort : TrExpr env Us runtime (.sort level) full') :
    TrExpr env Us scope (.sort level) narrow' := by
  rcases hsort with ⟨sortFull, hsortFull, hsortTarget⟩
  have hclosed : Closed (.sort level) 0 := trivial
  have hfvars : FVarsIn (· ∈ scope.fvars) (.sort level) := by
    simpa [FVarsIn] using hsortFull.fvarsIn
  rcases H.restrictEq henv hsortFull hclosed hfvars with
    ⟨sortNarrow, hsortNarrow, hsortLift⟩
  have htarget := H.fullTargetEq henv hnarrow hfull
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hlift : env.IsDefEqU Us.length runtime.toCtx
      (sortNarrow.lift' H.shift) (narrow'.lift' H.shift) :=
    hsortLift.symm.trans henv hruntimeWF <|
      hsortTarget.trans henv hruntimeWF htarget.symm
  have hexpanded := hlift.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  have hnarrowEq : env.IsDefEqU Us.length scope.toCtx
      sortNarrow narrow' :=
    (VEnv.IsDefEqU.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
      hexpanded
  exact ⟨sortNarrow, hsortNarrow, hnarrowEq⟩

/-- Extend the embedding by a generated index free variable.  The new
runtime domain need only be definitionally equal to the weakened semantic
domain. -/
def NarrowRuntimeScope.withIndex
    (H : NarrowRuntimeScope env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u)) :
    NarrowRuntimeScope env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := by
    change scope.bvars = 0
    exact H.noBV
  noIndConsts := fun names =>
    checkPositivityStep.VLCtx.NoIndConsts.cons
      (H.noIndConsts names) rfl

/-- At the parameter/index boundary, discard the ambient prefix retained
from previously checked mutual headers and keep the exact cached-parameter
suffix as the semantic scope. -/
def NarrowRuntimeScope.ofParameterSuffix
    (Hc : ContextWF c)
    (Hsuffix : ParameterContextSuffix Hc stats depth) :
    NarrowRuntimeScope Hc.venv c.lparams Hsuffix.parameterDecls
      Hc.mlctx.vlctx := by
  have hambient : Hsuffix.ambientDecls.NoBV := by
    apply VLCtx.NoBV.leftOfAppend Hsuffix.ambientDecls
      Hsuffix.parameterDecls
    rw [← Hsuffix.context]
    exact Hc.mlctx.noBV
  let W := VLCtx.FVLift.to_append Hsuffix.parameterDecls hambient
  refine {
    expanded := Hc.mlctx.vlctx
    shift := .skipN .refl Hsuffix.ambientDecls.toCtx.length
    lift := ?_
    context := .refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    upset := ?_
    noBV := ?_
    noIndConsts := Hsuffix.noIndConsts }
  · rw [Hsuffix.context]
    exact W.toFVLift'
  · have hwf : VLCtx.WF Hc.venv c.lparams.length
        (Hsuffix.ambientDecls ++ Hsuffix.parameterDecls) := by
      rw [← Hsuffix.context]
      exact Hc.mlctx_wf.tr.wf
    simpa [Hsuffix.context] using
      (IsFVarUpSet.suffixFVars Hsuffix.parameterDecls
        Hsuffix.ambientDecls hwf)
  · have hfull : (Hsuffix.ambientDecls ++
        Hsuffix.parameterDecls).NoBV := by
      rw [← Hsuffix.context]
      exact Hc.mlctx.noBV
    change Hsuffix.parameterDecls.bvars = 0
    change (Hsuffix.ambientDecls ++
      Hsuffix.parameterDecls).bvars = 0 at hfull
    rw [VLCtx.bvars_append] at hfull
    omega

/-- Relate a domain translated in the semantic scope to the annotation-
consumed domain installed by the executable checker. -/
theorem NarrowRuntimeScope.consumedDomain
    (Hc : ContextWF c)
    (H : NarrowRuntimeScope Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hdom : Hc.ConsumedDomain dom sourceDom consumedDom)
    (hnarrow : TrExprS Hc.venv c.lparams scope dom indexType) :
    ∃ u, Hc.venv.IsDefEq c.lparams.length H.expanded.toCtx
      (indexType.lift' H.shift) consumedDom (.sort u) := by
  have hweak : TrExprS Hc.venv c.lparams H.expanded dom
      (indexType.lift' H.shift) := by
    simpa using hnarrow.weakFV' Hc.checking.tr.wf.ordered H.lift
      H.context.wf
  have hsource := hweak.uniq Hc.checking.tr.wf H.context Hdom.source
  rcases Hdom.source_defeq with ⟨u, hsourceConsumed⟩
  have hsourceConsumed' := hsourceConsumed.defeqDFC
    Hc.checking.tr.wf.ordered
    (H.context.defeqCtx.symm Hc.checking.tr.wf.ordered)
  have hdomainU := hsource.trans Hc.checking.tr.wf H.context.wf.toCtx
    ⟨_, hsourceConsumed'⟩
  exact ⟨u, hdomainU.of_r Hc.checking.tr.wf H.context.wf.toCtx
    hsourceConsumed'.hasType.2⟩

/-- Shape of the CPS-retained runtime context after the first header has fixed
the block-wide parameter telescope.  Header indices form an ambient prefix;
the common parameters remain an exact suffix. -/
structure AmbientParamContext (Hc : ContextWF c) (params : List VExpr)
    (depth : Nat) where
  ambient : List VExpr
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (ambient ++ params.reverse) Hc.mlctx.vlctx.toCtx
  length : ambient.length = depth

/-- The exact cached-parameter suffix represents the common abstract
parameter telescope fixed by the first header.  The ambient prefixes may
differ definitionally, but have the same recorded depth and can be inverted
away from the context conversion. -/
theorem ParameterContextSuffix.paramsDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hambient : AmbientParamContext Hc params depth)
    (hparams : params.length = stats.params.size) :
    VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx := by
  have hcontext : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (Hambient.ambient ++ params.reverse)
      (Hsuffix.ambientDecls.toCtx ++ Hsuffix.parameterDecls.toCtx) := by
    simpa [Hsuffix.context] using Hambient.context
  have hparameterCtx : Hsuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    have hcachedLength : ∀ {ps : List Expr} {decls : VLCtx},
        List.Forall₂ CachedParameterDecl ps decls →
        decls.toCtx.length = ps.length := by
      intro ps decls hcached
      induction hcached with
      | nil => rfl
      | cons h _ ih =>
        rcases h with ⟨fv, deps, type, rfl, rfl⟩
        simp [VLCtx.toCtx, ih]
    simpa using hcachedLength Hsuffix.cached
  have hprefix : Hambient.ambient.length =
      Hsuffix.ambientDecls.toCtx.length := by
    have hlength := hcontext.length_eq
    simp only [List.length_append, List.length_reverse] at hlength
    omega
  exact VEnv.IsDefEqCtx.dropPrefixes hcontext hprefix

/-- Source-side account of the header telescope consumed by `loopType`.
`root` is the original normalized header and `current` is its unconsumed
suffix.  The context relation records that annotation erasure may change a
binder domain without changing the abstract telescope up to definitional
equality. -/
structure HeaderTelescopeCertificate (Hc : ContextWF c)
    (root current : VExpr) (params indices : List VExpr) where
  rebuild : root = VExpr.wrapForalls (params ++ indices) current
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx

theorem HeaderTelescopeCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeCertificate Hc root root [] [] where
  rebuild := by simp [VExpr.wrapForalls]
  context := by simpa using hctx

/-- Consume a common-parameter binder.  This operation is restricted to the
parameter phase, before any index binder has been seen. -/
theorem HeaderTelescopeCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeCertificate Hc root (.forallE sourceDom body)
      params [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body (params ++ [sourceDom]) [] where
  rebuild := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append] using H.rebuild
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceDom :: params.reverse)
      (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx

/-- Consume an index binder after the common parameters. -/
theorem HeaderTelescopeCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeCertificate Hc root (.forallE sourceDom body)
      params indices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body params (indices ++ [sourceDom]) where
  rebuild := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append] using H.rebuild
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceDom :: (indices.reverse ++ params.reverse))
      (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx

theorem HeaderTelescopeCertificate.takeParameters
    (H : HeaderTelescopeCertificate Hc root current params indices)
    (hlen : params.length = nparams) :
    root.takeForalls nparams =
      some (params, VExpr.wrapForalls indices current) := by
  subst nparams
  rw [H.rebuild, VExpr.takeForalls_wrapForalls_append]

theorem HeaderTelescopeCertificate.takeIndices
    (_H : HeaderTelescopeCertificate Hc root current params indices)
    (hlen : indices.length = nindices) :
    (VExpr.wrapForalls indices current).takeForalls nindices =
      some (indices, current) := by
  subst nindices
  exact VExpr.takeForalls_wrapForalls indices current

/-- Type-valued state carried by the executable telescope loop.  It owns the
source parameter and index lists, and synchronizes their lengths with the two
counters maintained by `loopType`. -/
structure HeaderTelescopeLoopCertificate (Hc : ContextWF c)
    (root current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  telescope : HeaderTelescopeCertificate Hc root current params indices
  parameterCount : params.length = i
  indexCount : indices.length = nindices

/-- Definitional, rather than syntactic, header-telescope accumulator.  Its
`header` field relates the independent source header to the telescope
synthesized from every binder exposed by the executable per-binder `whnf`.
This is the state used by the complete loop refinement. -/
structure HeaderSynthesisCertificate (Hc : ContextWF c)
    (target : VInductiveTypeSkeleton) (current : VExpr)
    (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx
  currentType : Hc.venv.IsType c.lparams.length
    (indices.reverse ++ params.reverse) current
  exprType : VExpr
  header : Hc.venv.IsDefEq c.lparams.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def HeaderSynthesisCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c}
    {target : VInductiveTypeSkeleton} {current exprType : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx)
    (hcurrent : Hc.venv.IsType c.lparams.length [] current)
    (hheader : Hc.venv.IsDefEq c.lparams.length []
      target.type current exprType) :
    HeaderSynthesisCertificate Hc target current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  context := by simpa using hctx
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

def HeaderSynthesisCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderSynthesisCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      target body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: H.params.reverse)
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      have hOld : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
          H.params.reverse Hc.mlctx.vlctx.toCtx := by
        simpa [hindices] using H.context
      exact .succ hOld
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (hOld.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [hindices, ContextWF.withLocalDecl_venv] using htype
  exprType := H.exprType
  header := by
    simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv]
      using H.header

def HeaderSynthesisCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderSynthesisCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      target body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: (H.indices.reverse ++ H.params.reverse))
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [List.reverse_append, ContextWF.withLocalDecl_venv] using htype
  exprType := H.exprType
  header := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv] using H.header

/-- Replace the residual telescope by a definitionally equal normal form and
close that equality over every already discovered binder. -/
noncomputable def HeaderSynthesisCertificate.normalize
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target current i nindices)
    (heq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx current next) :
    HeaderSynthesisCertificate Hc target next i nindices := by
  have heq' := heq.defeqDFC Hc.checking.tr.wf.ordered
    (H.context.symm Hc.checking.tr.wf.ordered)
  let currentLevel := Classical.choose H.currentType
  have hcurrent := Classical.choose_spec H.currentType
  have heqTyped := heq'.of_l Hc.checking.tr.wf H.context.isType hcurrent
  have heqTyped' : Hc.venv.IsDefEq c.lparams.length
      ((H.params ++ H.indices).reverse ++ []) current next
      (.sort currentLevel) := by
    simpa [List.reverse_append] using heqTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
      (domains := H.params ++ H.indices) (Γ := [])
      (by simpa [List.reverse_append] using H.context.isType)
      heqTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices
    parameterCount := H.parameterCount
    indexCount := H.indexCount
    context := H.context
    currentType := H.currentType.defeqU_l Hc.checking.tr.wf
      H.context.isType heq'
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r Hc.checking.tr.wf (by trivial)
      (by simpa using hwrapped) }

/-- Definitional header synthesis in a context narrower than the executable
reader context.  Later mutual headers retain indices introduced while
checking earlier family members; those declarations must not become part of
the later header's semantic telescope. -/
structure NarrowHeaderSynthesisCertificate
    (env : VEnv) (Us : List Name) (target : VInductiveTypeSkeleton)
    (scope : VLCtx) (current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  scopeCtx : scope.toCtx = indices.reverse ++ params.reverse
  scopeWF : scope.WF env Us.length
  currentType : env.IsType Us.length scope.toCtx current
  exprType : VExpr
  header : env.IsDefEq Us.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def NarrowHeaderSynthesisCertificate.empty
    {exprType : VExpr}
    (_htarget : env.IsType Us.length [] target.type)
    (hcurrent : env.IsType Us.length [] current)
    (hheader : env.IsDefEq Us.length [] target.type current exprType) :
    NarrowHeaderSynthesisCertificate env Us target [] current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  scopeCtx := rfl
  scopeWF := by trivial
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

/-- Replace the current residual by a definitionally equal forall over the
next cached common-parameter type, then move that binder into the narrow
scope. -/
noncomputable def NarrowHeaderSynthesisCertificate.withParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE sourceDom sourceBody) i 0)
    (hindices : H.indices = [])
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE paramType next)) :
    NarrowHeaderSynthesisCertificate env Us target
      ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0 := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE paramType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hparamsCtx : OnCtx H.params.reverse (env.IsType Us.length) := by
    simpa [hindices, H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length (H.params.reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE paramType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [hindices, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params) (Γ := []) (by simpa using hparamsCtx)
      hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params ++ [paramType]
    indices := []
    parameterCount := by simp [H.parameterCount]
    indexCount := rfl
    scopeCtx := by simp [VLCtx.toCtx, H.scopeCtx, hindices]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append]
        using hwrapped }

/-- Move a definitionally equal residual forall into the narrow index
telescope. -/
noncomputable def NarrowHeaderSynthesisCertificate.withIndex
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE sourceDom sourceBody) i nindices)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE indexType next)) :
    NarrowHeaderSynthesisCertificate env Us target
      ((some (fv, deps), .vlam indexType) :: scope)
      next i (nindices + 1) := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE indexType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hdomainsCtx : OnCtx (H.params ++ H.indices).reverse
      (env.IsType Us.length) := by
    simpa [List.reverse_append, ← H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length
      ((H.params ++ H.indices).reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE indexType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [List.reverse_append, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params ++ H.indices) (Γ := [])
      (by simpa using hdomainsCtx) hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices ++ [indexType]
    parameterCount := H.parameterCount
    indexCount := by simp [H.indexCount]
    scopeCtx := by
      simp [VLCtx.toCtx, H.scopeCtx, List.reverse_append]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
        List.append_assoc] using hwrapped }

/-- Build the semantic parameter transition from the narrowed syntax
translation and the executable comparison/normalization witnesses. -/
theorem NarrowHeaderSynthesisCertificate.consumeParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i 0)
    (hindices : H.indices = [])
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' paramType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam paramType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (paramType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      Nonempty (NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam paramType) :: scope)
        normalized' (i + 1) 0) := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE paramType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      ⟨H.withParameter henv hindices hscopeWF hstep⟩⟩

/-- Build the semantic index transition from the narrowed syntax
translation and the executable comparison/normalization witnesses. -/
theorem NarrowHeaderSynthesisCertificate.consumeIndex
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i
      nindices)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' indexType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam indexType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (indexType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      ∃ H' : NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam indexType) :: scope)
        normalized' i (nindices + 1), H'.params = H.params := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ indexType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam indexType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE indexType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      H.withIndex henv hscopeWF hstep, rfl⟩

theorem NarrowHeaderSynthesisCertificate.typeShape
    {decl : VInductDecl} {target : VInductiveType}
    (H : NarrowHeaderSynthesisCertificate env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env H.params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (env.IsType decl.uvars) := by
    simpa [huvars, ← H.scopeCtx] using H.scopeWF.toCtx
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := H.params) (ownParams := H.params) (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

theorem NarrowHeaderSynthesisCertificate.typeShapeWithParams
    {decl : VInductDecl} {target : VInductiveType}
    {commonParams : List VExpr}
    (H : NarrowHeaderSynthesisCertificate env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hparams : decl.ParamsDefEq env commonParams H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env commonParams target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := commonParams) (ownParams := H.params)
    (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake hparams hlevel hsort

theorem HeaderSynthesisCertificate.typeShapeWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params : List VExpr}
    (H : HeaderSynthesisCertificate Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hparams : decl.ParamsDefEq Hc.venv params H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    huvars H.context
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    hparams hlevel hsort

theorem HeaderSynthesisCertificate.typeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    (H : HeaderSynthesisCertificate Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params target := by
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using H.context.isType
  exact H.typeShapeWithParams huvars
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

/-- Materialize the two semantic header fields from the successful executable
tail.  Unlike `typeShape`, this theorem does not require either field to have
been chosen before the traversal: the index counter and translated sort are
used to construct the target itself. -/
theorem HeaderSynthesisCertificate.synthesizedTypeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveTypeSkeleton}
    (H : HeaderSynthesisCertificate Hc target current
      decl.nparams nindices)
    (huvars : c.lparams.length = decl.uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params
      (target.toVInductiveType nindices resultLevel) := by
  apply H.typeShape (target := target.toVInductiveType nindices resultLevel)
    huvars
  · intro resultLevel' hofLevel'
    rw [hofLevel] at hofLevel'
    cases hofLevel'
    rfl
  · exact hsort

/-- Persistent result of checking one metadata-free source header.  The final
mutual declaration need not exist yet; only its two block-wide counters are
relevant to `TypeShape`.  This lets the outer traversal accumulate checked
headers and materialize the declaration after every family member has
supplied its metadata. -/
structure SynthesizedHeader (env : VEnv) (uvars nparams : Nat)
    (params : List VExpr) (source : VInductiveTypeSkeleton)
    (numIndices : Nat) (resultLevel : VLevel) : Prop where
  parameterCount : params.length = nparams
  typeShape : ∀ decl : VInductDecl,
    decl.uvars = uvars → decl.nparams = nparams →
    decl.TypeShape env params
      (source.toVInductiveType numIndices resultLevel)

theorem NarrowHeaderSynthesisCertificate.synthesizedHeaderWithParams
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : NarrowHeaderSynthesisCertificate env Us source scope current
      nparams nindices)
    (henv : env.WF)
    (huvars : Us.length = uvars)
    (hparams : VEnv.IsDefEqCtx env uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel Us level = some resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    SynthesizedHeader env uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : Us.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq env commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      henv huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

theorem HeaderSynthesisCertificate.synthesizedHeader
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton}
    (H : HeaderSynthesisCertificate Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    SynthesizedHeader Hc.venv uvars nparams H.params source
      nindices resultLevel where
  parameterCount := H.parameterCount
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    subst nparams
    apply H.synthesizedTypeShape (decl := decl)
    · exact huvars'
    · exact hofLevel
    · exact hsort

/-- Later mutual headers use the first header's parameter telescope.  Their
own synthesized domains are connected to it by the successful executable
`isDefEq` checks, represented here independently of the not-yet-materialized
declaration. -/
theorem HeaderSynthesisCertificate.synthesizedHeaderWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : HeaderSynthesisCertificate Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    SynthesizedHeader Hc.venv uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq Hc.venv commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

structure SynthesizedHeaderMetadata (env : VEnv) (uvars nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : VInductiveTypeSkeleton) (data : Nat × VLevel) : Prop where
  header : SynthesizedHeader env uvars nparams params source data.1 data.2
  commonLevel : data.2 ≈ commonLevel

/-- Prefix of the metadata list built by the outer mutual-header traversal.
`Forall₂` fixes both ordering and cardinality, so later materialization cannot
associate a checked arity or universe with the wrong family member. -/
structure SynthesizedHeaderPrefix (env : VEnv)
    (skeleton : VInductDeclSkeleton) (params : List VExpr)
    (commonLevel : VLevel) (metadata : List (Nat × VLevel))
    (done : Nat) : Prop where
  parameterCount : params.length = skeleton.nparams
  covered : done ≤ skeleton.types.length
  checked : List.Forall₂
    (SynthesizedHeaderMetadata env skeleton.uvars skeleton.nparams
      params commonLevel)
    (skeleton.types.take done) metadata

theorem SynthesizedHeaderPrefix.first
    (hindex : 0 < skeleton.types.length)
    (Hheader : SynthesizedHeader env skeleton.uvars skeleton.nparams
      params skeleton.types[0] nindices resultLevel) :
    SynthesizedHeaderPrefix env skeleton params resultLevel
      [(nindices, resultLevel)] 1 where
  parameterCount := Hheader.parameterCount
  covered := by omega
  checked := by
    rw [List.take_succ_eq_append_getElem hindex]
    simp only [List.take_zero, List.nil_append]
    exact .cons ⟨Hheader, by rfl⟩ .nil

theorem SynthesizedHeaderPrefix.push
    (H : SynthesizedHeaderPrefix env skeleton params commonLevel
      metadata done)
    (hindex : done < skeleton.types.length)
    (Hheader : SynthesizedHeader env skeleton.uvars skeleton.nparams
      params skeleton.types[done] nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    SynthesizedHeaderPrefix env skeleton params commonLevel
      (metadata ++ [(nindices, resultLevel)]) (done + 1) where
  parameterCount := H.parameterCount
  covered := by omega
  checked := by
    rw [List.take_succ_eq_append_getElem hindex]
    exact Lean4Lean.VerifyInductive.List.Forall₂.append' H.checked
      (.cons ⟨Hheader, hlevel⟩ .nil)

/-- Once every header has been visited, exact materialization turns the
metadata-prefix invariant into the public formation header certificate. -/
def SynthesizedHeaderPrefix.complete
    (H : SynthesizedHeaderPrefix env skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    HeaderCertificate env decl := by
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have hcheckedLength :
      (skeleton.types.take skeleton.types.length).length = metadata.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.checked
  have hmetadata : metadata.length = skeleton.types.length := by
    simpa using hcheckedLength.symm
  have checkedAt : ∀ i (hi : i < skeleton.types.length),
      SynthesizedHeaderMetadata env skeleton.uvars skeleton.nparams
        params commonLevel skeleton.types[i] metadata[i] := by
    intro i hi
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.getElem H.checked i
      (by simpa using hi) (by simpa [hmetadata] using hi)
  have materializedAt : ∀ i (hi : i < skeleton.types.length),
      decl.types[i]'(by omega) =
        skeleton.types[i].toVInductiveType metadata[i].1 metadata[i].2 := by
    intro i hi
    rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize hi with
      ⟨data, hdata, htarget⟩
    have hmetadataGet : metadata[i]? = some metadata[i] := by
      simp [hmetadata, hi]
    have hdataEq : data = metadata[i] := by
      rw [hmetadataGet] at hdata
      cases hdata
      rfl
    subst data
    rw [List.getElem?_eq_getElem (by omega)] at htarget
    exact Option.some.inj htarget
  refine {
    params := params
    resultLevel := commonLevel
    commonLevels := ?_
    typeShapes := ?_ }
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).commonLevel
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).header.typeShape decl
      hfields.1 hfields.2.1

/-- Exact coverage makes skeleton materialization total and packages the
resulting formation-header certificate. -/
theorem SynthesizedHeaderPrefix.materializes
    (H : SynthesizedHeaderPrefix env skeleton params commonLevel metadata
      skeleton.types.length) :
    ∃ decl, skeleton.materialize metadata = some decl ∧
      Nonempty (HeaderCertificate env decl) := by
  have hmetadata : metadata.length = skeleton.types.length := by
    have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      H.checked
    simpa using hlength.symm
  cases hmaterialize : skeleton.materialize metadata with
  | none => simp [VInductDeclSkeleton.materialize, hmetadata] at hmaterialize
  | some decl => exact ⟨decl, rfl, ⟨H.complete hmaterialize⟩⟩

def HeaderTelescopeLoopCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeLoopCertificate Hc root root 0 0 where
  params := []
  indices := []
  telescope := .empty hctx
  parameterCount := rfl
  indexCount := rfl

def HeaderTelescopeLoopCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeLoopCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  telescope := by
    have Htel := H.telescope
    rw [hindices] at Htel
    exact Htel.withParameter hdom
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount

def HeaderTelescopeLoopCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeLoopCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  telescope := H.telescope.withIndex hdom
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]

theorem HeaderTelescopeLoopCertificate.takeParameters
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices) :
    root.takeForalls i =
      some (H.params, VExpr.wrapForalls H.indices current) :=
  H.telescope.takeParameters H.parameterCount

theorem HeaderTelescopeLoopCertificate.takeIndices
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices) :
    (VExpr.wrapForalls H.indices current).takeForalls nindices =
      some (H.indices, current) :=
  H.telescope.takeIndices H.indexCount

def AmbientParamContext.ofFirst
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : Hc.mlctx.vlctx.toCtx = indices.reverse ++ params.reverse) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := by
    have hwf : OnCtx (indices.reverse ++ params.reverse)
        (Hc.venv.IsType c.lparams.length) := hctx ▸ Hc.mlctx_wf.tr.wf.toCtx
    simpa [hctx] using VEnv.IsDefEqCtx.refl hwf
  length := by simp

def AmbientParamContext.ofFirstDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := hctx
  length := by simp

def AmbientParamContext.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : AmbientParamContext Hc params depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    AmbientParamContext
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      params (depth + 1) where
  ambient := sourceTy :: H.ambient
  context := by
    rcases hsource with ⟨u, hsource⟩
    change VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceTy :: (H.ambient ++ params.reverse))
      (ty' :: Hc.mlctx.vlctx.toCtx)
    exact .succ H.context
      (hsource.defeqDFC Hc.checking.tr.wf.ordered
        (H.context.symm Hc.checking.tr.wf.ordered))
  length := by simp [H.length]

theorem ParameterCachePrefix.empty
    (hparams : stats.params = #[]) :
    ParameterCachePrefix env Us Δ stats 0 depth := by
  refine ⟨?_, ?_⟩
  · simpa [hparams]
  · simp [hparams]

def ParameterContextSuffix.empty
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (hparams : stats.params = #[]) :
    ParameterContextSuffix Hc stats 0 where
  ambientDecls := []
  parameterDecls := []
  context := by simpa using hctx
  prefixLength := rfl
  cached := by simp [hparams]
  narrowParams := by simp [hparams, cachedParamVars]

/-- The first-header parameter branch extends the cached suffix itself.  The
empty-prefix premise records that parameters are all introduced before any
index binder. -/
def ParameterContextSuffix.push
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats 0)
    (hprefix : H.ambientDecls = [])
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      0 := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := []
    parameterDecls := entry :: H.parameterDecls
    context := ?_
    prefixLength := rfl
    cached := ?_
    narrowParams := ?_ }
  · have hcontext := H.context
    rw [hprefix] at hcontext
    change entry :: Hc.mlctx.vlctx = [] ++ entry :: H.parameterDecls
    simp only [List.nil_append]
    simpa using congrArg (entry :: ·) hcontext
  · simp only [Array.toList_push, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    exact .cons ⟨⟨c.ngen.curr⟩, ty.fvarsList, ty', rfl, rfl⟩
      H.cached
  · let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    let W : VLCtx.FVLift H.parameterDecls
        (entry :: H.parameterDecls) 0 1 0 :=
      .skip_fvar _ _ .refl
    have hscope : Hc.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    have hnarrowWF : VLCtx.WF Hc'.venv c.lparams.length
        (entry :: H.parameterDecls) := by
      change VLCtx.WF Hc.venv c.lparams.length
        (entry :: H.parameterDecls)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hscope] using Hc.mlctx_wf.tr.wf
      · intro fv deps heq
        simp only [entry, Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨by simpa [hscope] using Hc.current_not_mem,
          by simpa [hscope] using htr.fvarsList⟩
      · change Hc.venv.IsType c.lparams.length
          H.parameterDecls.toCtx ty'
        simpa [hscope] using hty
    have hold : List.Forall₂
        (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
        stats.params.toList
        ((cachedParamVars stats.params.size 0).map
          fun e => e.liftN 1 0) := by
      have weakAll : ∀ {as bs},
          List.Forall₂
              (TrExprS Hc.venv c.lparams H.parameterDecls) as bs →
            List.Forall₂
              (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
              as (bs.map fun e => e.liftN 1 0) := by
        intro as bs hp
        induction hp with
        | nil => exact .nil
        | cons h _ ih =>
          exact .cons
            (h.weakFV Hc.checking.tr.wf.ordered W hnarrowWF) ih
      exact weakAll H.narrowParams
    have hnew : TrExprS Hc'.venv c.lparams
        (entry :: H.parameterDecls)
        (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
      apply TrExprS.fvar (A := ty'.lift)
      simp [entry, VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type]
    simpa [Array.toList_push, cachedParamVars_succ] using
      Lean4Lean.VerifyInductive.List.Forall₂.append' hold
        (.cons hnew .nil)

/-- Index binders extend only the ambient prefix and preserve the exact
cached-parameter suffix. -/
def ParameterContextSuffix.withIndex
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      stats (depth + 1) := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := ?_
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    narrowParams := H.narrowParams }
  change entry :: Hc.mlctx.vlctx =
    (entry :: H.ambientDecls) ++ H.parameterDecls
  simp only [List.cons_append]
  rw [H.context]

theorem ParameterContextSuffix.parameterDecls_length
    (H : ParameterContextSuffix Hc stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    H.cached
  simpa using hlength.symm

/-- Locate executable parameter `i` in the reverse-ordered local-context
suffix. -/
theorem ParameterContextSuffix.parameterAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := by
    exact hj
  have hcached := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change CachedParameterDecl stats.params[stats.params.size - 1 - j]
    H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

/-- Split the cached-parameter suffix at executable array index `i`.  Entries
in `newer` are precisely the cached declarations introduced after parameter
`i`; `older` contains those introduced before it. -/
theorem ParameterContextSuffix.splitAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      CachedParameterDecl stats.params[i] entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

/-- Expose the exact `FVLift` that removes the ambient declarations and the
cached parameters newer than executable parameter `i`, leaving that
parameter as the head of the retained suffix. -/
theorem ParameterContextSuffix.fvLiftAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      Hc.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        Hc.mlctx.vlctx
        0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : Hc.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older)
      hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, rfl,
    hcontext, hparam, hlift⟩

/-- Narrow concrete scope immediately before consuming cached parameter `i`.
Only parameters already consumed by this later header may occur; ambient
indices and the current-or-future cached parameters are excluded. -/
structure LaterParameterScope
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : Hc.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    Hc.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem LaterParameterScope.olderLength
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size) :
    H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

theorem LaterParameterScope.older_eq_nil
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

/-- After the final cached parameter is consumed, the accumulated narrow
scope is exactly the complete cached-parameter suffix. -/
theorem LaterParameterScope.completedScope
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

/-- Consecutive cached-parameter scopes agree on the consumed suffix. -/
theorem LaterParameterScope.nextOlder
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {e next : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (Hnext : LaterParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

theorem LaterParameterScope.openedFVars
    (H : LaterParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem LaterParameterScope.openedUpSet
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      Hc.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older) H.added
    (by simpa [H.context] using Hc.mlctx_wf.tr.wf)

/-- Substitution of the current cached parameter, followed by an executable
normalization step, cannot introduce dependencies outside the newly consumed
parameter scope. -/
theorem LaterParameterScope.consumedFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : LaterParameterScope Hsuffix i body)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

/-- Forget the ambient prefix, the not-yet-consumed cached parameters, and
the current cached parameter.  A source domain at this point may depend only
on the already consumed parameters in `older`. -/
theorem LaterParameterScope.olderLift
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    VLCtx.FVLift H.older Hc.mlctx.vlctx 0
      (VLCtx.toCtx H.added).length.succ 0 := by
  let current : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  have hcontext : Hc.mlctx.vlctx =
      (H.added ++ [current]) ++ H.older := by
    simpa only [current, List.append_assoc, List.singleton_append]
      using H.context
  have hfullNoBV : ((H.added ++ [current]) ++ H.older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hprefixNoBV : (H.added ++ [current]).NoBV :=
    VLCtx.NoBV.leftOfAppend (H.added ++ [current]) H.older hfullNoBV
  have hlift := VLCtx.FVLift.to_append H.older hprefixNoBV
  rw [← hcontext] at hlift
  simpa [current, VLCtx.toCtx] using hlift

/-- Restrict a translated later-header domain to precisely the cached
parameters already consumed by this header. -/
theorem LaterParameterScope.domainTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' : VExpr}
    (H : LaterParameterScope Hsuffix i (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom') :
    ∃ sourceDom', TrExprS Hc.venv c.lparams H.older dom sourceDom' := by
  have hclosed : Closed dom 0 := by
    have := hdom.closed
    simpa [Hc.mlctx.noBV] using this
  exact hdom.weakFV_inv Hc.checking.tr.wf H.olderLift
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hclosed H.fvars.1

/-- Recover every premise needed by the executable cached-parameter branch
from the retained local-context translation. -/
theorem LaterParameterScope.typing
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' ∧
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? Hc.mlctx_wf.tr.wf hhead
  rcases hfull with hfull
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : Hc.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ Hc.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  have hlocal :=
    (Hc.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv
  rcases hlocal with ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← Hc.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ Hc.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact Hc.mlctx_wf.tr.wf.find?_wf Hc.checking.tr.wf hfind

/-- The successful executable comparison of a later parameter domain with
its cached local type descends to the narrowed, abstract context. -/
theorem LaterParameterScope.domainDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {dom' paramTy' : VExpr}
    (H : LaterParameterScope Hsuffix i (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hparamTyEq : paramTy' = H.paramType.lift.liftN
      (VLCtx.toCtx H.added).length 0)
    (heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' paramTy') :
    ∃ sourceDom',
      TrExprS Hc.venv c.lparams H.older dom sourceDom' ∧
      Hc.venv.IsDefEqU c.lparams.length H.older.toCtx
        sourceDom' H.paramType := by
  rcases H.domainTranslation hdom with ⟨sourceDom', hsourceDom⟩
  have hweak := hsourceDom.weakFV Hc.checking.tr.wf.ordered
    H.olderLift Hc.mlctx_wf.tr.wf
  have htranslated : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx dom'
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0) :=
    hdom.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hweak
  rw [hparamTyEq] at heq
  have hfull := htranslated.symm.trans Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq
  have hfull' : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0)
      (H.paramType.liftN (VLCtx.toCtx H.added).length.succ 0) := by
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hfull
  exact ⟨sourceDom', hsourceDom,
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx
      H.olderLift.toCtx).1 hfull'⟩

/-- A closed source header starts the later-parameter traversal with an empty
free-variable scope. -/
noncomputable def LaterParameterScope.ofNoFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    LaterParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

/-- Advance the narrow scope after substituting cached parameter `i` and
normalizing the resulting body.  The next parameter's older suffix is
exactly the current cached declaration followed by the current older suffix.
-/
noncomputable def LaterParameterScope.next
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : LaterParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    LaterParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp :
        H.newer ++ currentEntry :: H.older =
          (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hopened : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older))
        (body.instantiate1 stats.params[i]!) := by
      rw [Expr.instantiate1_eq, H.parameter]
      exact H.openedFVars
    have hnormalized : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older)) normalized :=
      hbelow _ H.openedUpSet hopened
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

/-- The core later-parameter abstraction step.  Translation of the
executable cached substitution is first restricted to the current-and-older
parameter suffix, then the cached free variable is turned back into the
source binder. -/
theorem LaterParameterScope.uninstantiateEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS Hc.venv c.lparams
        ((none, .vlam H.paramType) :: H.older) body body'' ∧
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        body' (body''.liftN (VLCtx.toCtx H.added).length 0) := by
  have hopened' : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1' (.fvar H.fv)) body' := by
    simpa [Expr.instantiate1_eq, H.parameter] using hopened
  have hsuffixWF := H.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hfresh : H.fv ∉ H.older.fvars :=
    (hsuffixWF.2.1 H.fv H.deps rfl).1
  have hsourceFresh : FVarsIn (· ≠ H.fv) body :=
    H.fvars.mono fun fv hfv heq => by
      subst fv
      exact hfresh hfv
  have hopenedClosed : Closed (body.instantiate1' (.fvar H.fv)) 0 := by
    have := hopened'.closed
    simpa [Hc.mlctx.noBV] using this
  exact hopened'.uninstantiateAfterWeakFV_eq Hc.checking.tr.wf H.lift
    (.refl Hc.checking.tr.wf.ordered Hc.mlctx_wf.tr.wf)
    hopenedClosed H.openedFVars hsourceFresh

/-- The core later-parameter abstraction step without exposing the equality
back to the retained runtime context. -/
theorem LaterParameterScope.uninstantiate
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS Hc.venv c.lparams
      ((none, .vlam H.paramType) :: H.older) body body'' := by
  rcases H.uninstantiateEq hopened with ⟨body'', hbody'', _⟩
  exact ⟨body'', hbody''⟩

/-- Restrict the post-substitution normal form to the consumed-parameter
suffix and relate it to the reconstructed source body.  This is the semantic
state transition used by the later-header telescope accumulator. -/
theorem LaterParameterScope.normalizedBody
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized)
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized body') :
    ∃ sourceBody' normalized',
      TrExprS Hc.venv c.lparams
        ((none, .vlam H.paramType) :: H.older) body sourceBody' ∧
      TrExprS Hc.venv c.lparams
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
        normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length
        ((H.paramType :: H.older.toCtx)) sourceBody' normalized' := by
  rcases H.uninstantiateEq hopened with
    ⟨sourceBody', hsourceBody, hopenedEq⟩
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  have hopenedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  have hnormalizedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized :=
    hbelow _ H.openedUpSet hopenedFVars
  have hnormalizedClosed : Closed normalized 0 := by
    have := hnormalizedFull.closed
    simpa [Hc.mlctx.noBV] using this
  rcases hnormalizedFull.weakFV_inv Hc.checking.tr.wf H.lift
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedFVars with
    ⟨normalized', hnormalized'⟩
  have hnormalizedWeak := hnormalized'.weakFV
    Hc.checking.tr.wf.ordered H.lift Hc.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hnormalizedWeak
  have hfull : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (sourceBody'.liftN (VLCtx.toCtx H.added).length 0)
      (normalized'.liftN (VLCtx.toCtx H.added).length 0) :=
    hopenedEq.symm.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.symm.trans Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx hnormalizedUniq)
  have hnarrow : Hc.venv.IsDefEqU c.lparams.length
      (VLCtx.toCtx
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      sourceBody' normalized' :=
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx H.lift.toCtx).1 hfull
  exact ⟨sourceBody', normalized', hsourceBody, hnormalized',
    by simpa [VLCtx.toCtx] using hnarrow⟩

/-- Adding a common parameter weakens every cached parameter translation and
appends the newly generated free variable, whose abstract image is `bvar 0`.
This is the exact state update performed by `loopType` on the first header. -/
theorem ParameterCachePrefix.push
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats done 0)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      (done + 1) 0 := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hold : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList
      ((cachedParamVars done 0).map fun e => e.liftN 1 0) := by
    have mapRight : ∀ {as bs},
        List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
        List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
          (bs.map fun e => e.liftN 1 0) := by
      intro as bs hp
      induction hp with
      | nil => exact .nil
      | cons h _ ih =>
        exact .cons
          (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
    exact mapRight H.params
  have hfresh : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
    exact TrExprS.fvar (A := ty'.lift) (by
      change VLCtx.find? ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
      simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
        VLocalDecl.value, VLocalDecl.type])
  refine ⟨?_, ?_⟩
  · simpa using Lean4Lean.VerifyInductive.List.Forall₂.append'
      hold (.cons hfresh .nil)
  · intro param hparam
    simp only [Array.mem_push] at hparam
    rcases hparam with hparam | rfl
    · exact H.paramFVars param hparam
    · exact ⟨⟨c.ngen.curr⟩, rfl⟩

/-- Index binders do not change the concrete parameter cache; they uniformly
shift its abstract de Bruijn interpretation. -/
theorem ParameterCachePrefix.withIndex
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats
      done depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats done (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  refine ⟨?_, H.paramFVars⟩
  rw [cachedParamVars_depth_succ]
  have mapRight : ∀ {as bs},
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
      List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
        (bs.map fun e => e.liftN 1 0) := by
    intro as bs hp
    induction hp with
    | nil => exact .nil
    | cons h _ ih =>
      exact .cons
        (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
  exact mapRight H.params

theorem ParameterCachePrefix.complete
    {decl : VInductDecl}
    (H : ParameterCachePrefix env Us Δ stats decl.nparams depth) :
    List.Forall₂ (TrExprS env Us Δ) stats.params.toList
      (decl.paramVars depth) := by
  rw [← cachedParamVars_eq_paramVars decl]
  exact H.params

/-- Fuel exhaustion cannot produce a successful result. -/
theorem zero.WF :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      0 k c).WF Q := by
  intro _ h
  simp [AddInductive.checkInductiveTypes.loopType] at h

/-- Base case of the header telescope traversal.  This theorem deliberately
states only the executable control-flow fact; the caller's continuation owns
the declarative result-sort and accumulated-telescope obligations. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i = nparams)
    (Hk : (k type stats nindices c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  subst i
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]

/-- A non-forall tail with the wrong number of common parameters is rejected,
so this branch is semantically vacuous. -/
theorem parameterMismatch.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i ≠ nparams) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Verification step for an index binder.  `hdom`/`hdomType` are stated for
the annotation-consumed domain actually installed in the production local
context; deriving them from the source domain is the separate
`consumeTypeAnnotations` compatibility obligation. -/
theorem index.WF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_neg hi]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => do
      let type := body.instantiate1 arg
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) i (nindices + 1) fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.WF Hc' hopened).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Index verification with the WHNF free-variable bound retained for
narrow-scope consumers. -/
theorem index.scopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      FVarsBelow
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_neg hi]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => do
      let type := body.instantiate1 arg
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) i (nindices + 1) fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.scopeWF Hc' hopened).bind
    fun normalized hnormalized =>
      Hrec normalized hnormalized.1 hnormalized.2

/-- Source-facing index step: consume the domain certificate and transport the
source body automatically before invoking `index.WF`. -/
theorem index.sourceWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.WF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- Source-facing index step retaining the WHNF free-variable bound. -/
theorem index.sourceScopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        FVarsBelow
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.scopeWF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hbelow hnormalized =>
      Hrec body'' hbodyEq normalized hbelow hnormalized)

/-- Index-step wrapper that transports the first-header parameter cache under
the newly introduced index binder. -/
theorem index.cacheWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hdom hbody
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.withIndex Hc Hdom.consumed Hdom.isType)

/-- Index-step wrapper carrying the translated parameter cache and the exact
source telescope/counter state in lockstep. -/
theorem index.cacheTelescopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Htelescope : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        HeaderTelescopeLoopCertificate
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType)
          root sourceBody' i (nindices + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' :
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  exact Hrec body'' hbodyEq'' normalized hnormalized Hcache'
    (Htelescope.withIndex Hdom)

/-- Complete index branch for the synthesized header telescope.  The source
body conversion and the following executable `whnf` are composed before the
recursive state is exposed. -/
theorem index.cacheSynthesisWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hsynthesis : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (normalized : Expr) (next : VExpr),
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats done (depth + 1) →
      ParameterContextSuffix Hc' stats (depth + 1) →
      HeaderSynthesisCertificate Hc' target next i (nindices + 1) →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        i (nindices + 1) fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  exact Hrec Hc' rfl rfl normalized next hnext Hcache'
    (Hsuffix.withIndex Hc Hdom.consumed Hdom.isType)
    ((Hsynthesis.withIndex Hdom).normalize hsourceNext)

/-- Later-header index step carrying both the translated parameter cache and
the ambient-prefix shape used at the constructor boundary. -/
theorem index.runtimeStateWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hambient : AmbientParamContext Hc params depth)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        AmbientParamContext
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType) params (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  exact Hrec body'' hbodyEq normalized hnormalized Hcache'
    (Hambient.withIndex Hdom.consumed Hdom.isType Hdom.source_defeq)

/-- Verification step for a common parameter of the first mutual header.  In
addition to the opened-body relation, the continuation sees the exact fresh
free variable appended to the executable parameter cache. -/
theorem firstParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_pos hempty]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun param => do
      let stats := { stats with params := stats.params.push param }
      let type := body.instantiate1 param
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.WF Hc' hopened).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Source-facing first-parameter step, including annotation-domain and body
transport. -/
theorem firstParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact firstParameter.WF Hc hi hempty Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- First-parameter wrapper synchronized with the executable cache push. -/
theorem firstParameter.cacheWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hdom hbody
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.push Hc Hdom.consumed Hdom.isType)

/-- First-parameter wrapper carrying the cache and source telescope counters
through the same successful executable branch. -/
theorem firstParameter.cacheTelescopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Htelescope : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Htelescope.indices = [])
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        HeaderTelescopeLoopCertificate
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType)
          root sourceBody' (i + 1) nindices →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' :
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  exact Hrec body'' hbodyEq'' normalized hnormalized Hcache'
    (Htelescope.withParameter hindices Hdom)

/-- Complete first-parameter branch for the synthesized header telescope. -/
theorem firstParameter.cacheSynthesisWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hsuffix : ParameterContextSuffix Hc stats 0)
    (hprefix : Hsuffix.ambientDecls = [])
    (Hsynthesis : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Hsynthesis.indices = [])
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (normalized : Expr) (next : VExpr),
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        (done + 1) 0 →
      ParameterContextSuffix Hc'
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        0 →
      (Hsynthesis' : HeaderSynthesisCertificate
        Hc' target next (i + 1) nindices) →
      Hsynthesis'.indices = [] →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  let Hsynthesis' :=
    (Hsynthesis.withParameter hindices Hdom).normalize hsourceNext
  exact Hrec Hc' rfl rfl normalized next hnext Hcache'
    (Hsuffix.push Hc hprefix Hdom.consumed Hdom.isType)
    Hsynthesis' (by rfl)

/-- Verification step for a common parameter of a later mutual header.  The
executable checker reuses the cached free variable and requires the new domain
to be definitionally equal to its local type. -/
theorem laterParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hget : (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized, TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · exact (whnfInContext.WF Hc hopened).bind fun normalized hnormalized =>
      Hrec (hequal rfl) normalized hnormalized

/-- Source-facing later-parameter step.  The successful executable equality
check supplies exactly the conversion needed to instantiate the translated
source body with the cached parameter. -/
theorem laterParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hget : (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized,
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact (whnfInContext.WF Hc hopened).bind fun normalized hnormalized =>
      Hrec heq normalized hnormalized

/-- Complete cached-parameter step with the narrow concrete scope and the
reconstructed source binder exposed to the continuation. -/
theorem laterParameter.scopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hget : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' paramTy' →
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          LaterParameterScope Hsuffix (i + 1) normalized) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind
    fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    let Hbody : LaterParameterScope Hsuffix i body := {
      Hscope with fvars := Hscope.fvars.2 }
    have habstract := Hbody.uninstantiate hopened
    exact (whnfInContext.scopeWF Hc hopened).bind
      fun normalized hnormalized =>
      Hrec heq habstract normalized hnormalized.1 hnormalized.2
        (Hbody.normalizedBody hopened hnormalized.1 hnormalized.2)
        (fun hnext => Hbody.next hnext hnormalized.1)

/-- Complete cached-parameter step driven only by the retained scope.  In
particular, lookup of the cached concrete parameter and all of its abstract
typing data are consequences of `Hscope`, rather than premises supplied by
the caller. -/
theorem laterParameter.checkedScopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ {paramTy' param'},
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' →
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      (∃ sourceDom',
        TrExprS Hc.venv c.lparams Hscope.older dom sourceDom' ∧
        Hc.venv.IsDefEqU c.lparams.length Hscope.older.toCtx
          sourceDom' Hscope.paramType) →
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          LaterParameterScope Hsuffix (i + 1) normalized) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hscope.typing with
    ⟨paramTy, paramTy', param', hget, hparamTy, hparamTyEq,
      hparam, hparamType⟩
  apply laterParameter.scopeWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hnonempty Hsuffix Hscope hget hdom hbody hparamTy hparam hparamType
  intro heq habstract normalized hbelow hnormalized htransition hnext
  exact Hrec hparam hparamType heq
    (Hscope.domainDefEq hdom hparamTyEq heq) habstract
    normalized hbelow hnormalized htransition hnext

/-- Reusing a cached parameter does not alter the retained ambient-prefix
shape. -/
theorem laterParameter.runtimeStateWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hambient : AmbientParamContext Hc params depth)
    (hget : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized,
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        AmbientParamContext Hc params depth →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply laterParameter.sourceWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hnonempty hget hdom hbody hparamTy hparam hparamType
  intro heq normalized hnormalized
  exact Hrec heq normalized hnormalized Hambient

/-- Recursive verifier for the first mutual header.  It follows the concrete
fuel recursion and carries both the parameter cache and the synthesized
abstract telescope to the terminal continuation. -/
theorem firstHeaderSynthesisWF
    {target : VInductiveTypeSkeleton}
    {baseLevels : List Level} {baseNindices : Array Nat}
    {baseConsts : Array Expr}
    {R : VEnv → Prop}
    {α : Type} (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M α) (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {type' : Expr}
      {current' : VExpr} {i' nindices' : Nat}
      (Hc' : ContextWF c'),
      c'.lparams = Us →
      stats'.indConsts.isEmpty = true →
      stats'.levels = baseLevels →
      stats'.nindices = baseNindices →
      stats'.indConsts = baseConsts →
      R Hc'.venv →
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      i' = nparams →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' i' nindices' →
      ParameterContextSuffix Hc' stats' nindices' →
      HeaderSynthesisCertificate Hc' target current' i' nindices' →
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      (k type' stats' nindices' c').WF Q)
    (Hc : ContextWF c)
    (hlparams : c.lparams = Us)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevelsStable : stats.levels = baseLevels)
    (hnindicesStable : stats.nindices = baseNindices)
    (hconstsStable : stats.indConsts = baseConsts)
    (HR : R Hc.venv)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats i nindices)
    (Hsuffix : ParameterContextSuffix Hc stats nindices)
    (Hsynthesis : HeaderSynthesisCertificate Hc target current i nindices)
    (hphase : i < nparams → Hsynthesis.indices = [] ∧ nindices = 0)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      fuel k c).WF Q := by
  induction fuel generalizing c stats type current i nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htype with
      | forallE hdomType hbodyType hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom, Hdom⟩
        by_cases hi : i < nparams
        · rcases hphase hi with ⟨hindices, hnindices⟩
          subst nindices
          have hambient : Hsuffix.ambientDecls = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using Hsuffix.prefixLength
          apply firstParameter.cacheSynthesisWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi hempty (by simpa using Hcache) Hsuffix hambient
            Hsynthesis hindices Hdom hbody
          intro c' Hc' hvenv' hlparams' normalized next hnext Hcache' Hsuffix'
            Hsynthesis' hindices'
          apply ih Hc' (hlparams'.trans hlparams) (by simpa using hempty)
            (by simpa using hlevelsStable)
            (by simpa using hnindicesStable)
            (by simpa using hconstsStable)
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro _
            exact ⟨hindices', rfl⟩
          · exact hnext
        · apply index.cacheSynthesisWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi Hcache Hsuffix Hsynthesis Hdom hbody
          intro c' Hc' hvenv' hlparams' normalized next hnext Hcache' Hsuffix'
            Hsynthesis'
          apply ih Hc' (hlparams'.trans hlparams) hempty hlevelsStable
            hnindicesStable hconstsStable
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro hlt
            exact False.elim (hi hlt)
          · exact hnext
    · by_cases hi : i = nparams
      · exact result.WF hforall hi
          (Hresult Hc hlparams hempty hlevelsStable hnindicesStable
            hconstsStable HR hforall hi Hcache Hsuffix Hsynthesis htype)
      · exact parameterMismatch.WF hforall hi

/-- Follow the executable later-header loop through all cached common
parameters.  The retained suffix supplies each cached lookup and advances
after the executable normalization step.  Once `i = nparams`, ownership of
the unchanged loop state passes to the index/result verifier. -/
theorem laterParametersWF
    {alpha : Type} (Hc : ContextWF c)
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {type' current' i' fuel'},
      i' = nparams →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' current' →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        nindices fuel' k c).WF Q)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : i < stats.params.size →
      LaterParameterScope Hsuffix i type)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      nindices fuel k c).WF Q := by
  induction fuel generalizing type current i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htype with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix (Hscope histats) hdom hbody
        intro paramTy' param' _hparam _hparamType _heq _hdomain
          _habstract normalized _hbelow hnormalized _htransition hnext
        apply ih (i := i + 1) (current := body'.inst param')
        · omega
        · intro hlt
          exact hnext hlt
        · exact hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq htype

/-- Cached-parameter recursion with the independent narrow header telescope
accumulated in lockstep.  The executable reader context remains unchanged;
the synthesis scope grows only by the parameters consumed by this header. -/
theorem laterParameterSynthesisWF
    {alpha : Type} (Hc : ContextWF c)
    {target : VInductiveTypeSkeleton}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hresult : ∀ {type' narrowCurrent fullCurrent scope' i' fuel'},
      i' = nparams →
      NarrowHeaderSynthesisCertificate Hc.venv c.lparams target
        scope' narrowCurrent i' 0 →
      scope' = Hsuffix.parameterDecls →
      TrExprS Hc.venv c.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' fullCurrent →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        0 fuel' k c).WF Q)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : ∀ _h : i < stats.params.size,
      LaterParameterScope Hsuffix i type)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target scope narrowCurrent i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      0 fuel k c).WF Q := by
  induction fuel generalizing type scope narrowCurrent fullCurrent i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htypeFull with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := 0) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix Hcurrent hdom hbody
        intro paramTy' param' _hparam _hparamType _heq hdomain
          _habstract normalized hbelow hnormalized htransition hnext
        have hindices : Hsynthesis.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
        have hcurrentWF := Hcurrent.lift.wf Hc.checking.tr.wf
          Hc.mlctx_wf.tr.wf
        rcases Hsynthesis.consumeParameter Hc.checking.tr.wf hindices
            htypeNarrow hcurrentWF hdomain htransition with
          ⟨normalized', hnormalized', ⟨Hsynthesis'⟩⟩
        let Hbody : LaterParameterScope Hsuffix i body := {
          Hcurrent with fvars := Hcurrent.fvars.2 }
        exact ih (i := i + 1)
          (scope := (some (Hcurrent.fv, Hcurrent.deps),
            .vlam Hcurrent.paramType) :: Hcurrent.older)
          (narrowCurrent := normalized')
          (fullCurrent := body'.inst param')
          (hbound := by omega)
          (Hscope := fun hlt => hnext hlt)
          (hscopeEq := fun hlt =>
            Hcurrent.nextOlder (hnext hlt) hlt)
          (hcompleteScope := fun heq => by
            have hdone : i + 1 = stats.params.size := by
              rw [hparams]
              exact heq
            exact Hcurrent.completedScope hdone)
          Hsynthesis' hnormalized'
          (Hbody.consumedFVars hbelow) hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq Hsynthesis (hcompleteScope hieq)
        htypeNarrow htypeFVars htypeFull

/-- Traverse the index suffix of a later mutual header while keeping its
semantic telescope independent of ambient declarations retained by the
executable checker. -/
theorem laterIndexSynthesisWF
    {alpha : Type} {target : VInductiveTypeSkeleton}
    {commonParams : List VExpr}
    {paramU : Nat}
    {R : VEnv → Prop}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hlparams : c'.lparams = c.lparams)
      {type' narrowCurrent fullCurrent scope' nindices' fuel'},
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      (Hsynthesis' : NarrowHeaderSynthesisCertificate Hc'.venv c'.lparams
        target scope' narrowCurrent nparams nindices') →
      NarrowRuntimeScope Hc'.venv c'.lparams scope' Hc'.mlctx.vlctx →
      TrExprS Hc'.venv c'.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' fullCurrent →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats nparams (depth + nindices') →
      ParameterContextSuffix Hc' stats (depth + nindices') →
      AmbientParamContext Hc' commonParams (depth + nindices') →
      R Hc'.venv →
      VEnv.IsDefEqCtx Hc'.venv paramU []
        commonParams.reverse Hsynthesis'.params.reverse →
      (AddInductive.checkInductiveTypes.loopType nparams stats type'
        nparams nindices' (fuel' + 1) k c').WF Q)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hc : ContextWF c)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats nparams (depth + nindices))
    (Hsuffix : ParameterContextSuffix Hc stats (depth + nindices))
    (Hambient : AmbientParamContext Hc commonParams
      (depth + nindices))
    (HR : R Hc.venv)
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target scope narrowCurrent nparams nindices)
    (Hparams : VEnv.IsDefEqCtx Hc.venv paramU []
      commonParams.reverse Hsynthesis.params.reverse)
    (Hruntime : NarrowRuntimeScope Hc.venv c.lparams
      scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type
      nparams nindices fuel k c).WF Q := by
  induction fuel generalizing c type scope narrowCurrent fullCurrent
      nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htypeNarrow with
      | @forallE indexType narrowBody _ _ _ _ _
          hdomType _hbodyType hdomNarrow hbodyNarrow =>
        rcases TrExpr.forallE_source htypeFull with
          ⟨sourceDom, fullBody, hdomFull, hbodyFull,
            hdomFullType, _hbodyFullType, _hfullCurrent⟩
        rcases hconsume c Hc hdomFull hdomFullType with
          ⟨consumedDom, Hdom⟩
        rcases Hdom.body Hc hbodyFull with
          ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
        apply index.scopeWF (stats := stats) (nparams := nparams)
          (i := nparams) (nindices := nindices) (fuel := fuel)
          (k := k) (Q := Q) Hc (by omega) Hdom.consumed Hdom.isType
          hbodyConsumed
        intro normalized hbelow hnormalized
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotations_fvarsIn htypeFVars.1)).1
        rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
          ⟨domainLevel, hdomain⟩
        let Hruntime' : NarrowRuntimeScope Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList),
              .vlam indexType) :: scope)
            Hc'.mlctx.vlctx :=
          Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
        have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
        have hopenedNarrow : TrExprS Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList),
              .vlam indexType) :: scope)
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
          rw [Expr.instantiate1_eq]
          exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
        have hopenedFVars : FVarsIn
            (· ∈ VLCtx.fvars ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList),
              .vlam indexType) :: scope))
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) := by
          rw [Expr.instantiate1_eq]
          apply (htypeFVars.2.mono fun fv hfv => by
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_of_mem _ hfv).instantiate1
          rw [VLCtx.fvars_cons_some]
          exact List.mem_cons_self
        have hnormalizedFVars := hbelow _ Hruntime'.upset hopenedFVars
        rcases hnormalized with
          ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
        have hnormalizedClosed : Closed normalized 0 := by
          have := hnormalizedFull.closed
          have hnoBV : Hc'.mlctx.vlctx.bvars = 0 := Hc'.mlctx.noBV
          rw [hnoBV] at this
          exact this
        rcases Hruntime'.restrictEq Hc'.checking.tr.wf
            hnormalizedFull hnormalizedClosed hnormalizedFVars with
          ⟨normalizedNarrow, hnormalizedNarrow, hnormalizedEq⟩
        have hopenedWeak : TrExprS Hc'.venv c.lparams Hruntime'.expanded
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
            (narrowBody.lift' Hruntime'.shift) := by
          simpa using hopenedNarrow.weakFV' Hc'.checking.tr.wf.ordered
            Hruntime'.lift Hruntime'.context.wf
        have hopenedFull := Hc.instantiateFresh
          (name := name) (bi := bi) Hdom.consumed Hdom.isType
          hbodyConsumed
        have hopenedEq := hopenedWeak.uniq Hc'.checking.tr.wf
          Hruntime'.context hopenedFull
        have hopenedEq' := hopenedEq.defeqDFC
          Hc'.checking.tr.wf.ordered Hruntime'.context.defeqCtx
        have hnormalizeU : Hc'.venv.IsDefEqU c.lparams.length
            Hc'.mlctx.vlctx.toCtx consumedBody normalizedFull :=
          hnormalizeEq.symm
        have hsourceNormalized := hopenedEq'.trans Hc'.checking.tr.wf
          Hc'.mlctx_wf.tr.wf.toCtx hnormalizeU
        have hfull : Hc'.venv.IsDefEqU c.lparams.length
            Hc'.mlctx.vlctx.toCtx
            (narrowBody.lift' Hruntime'.shift)
            (normalizedNarrow.lift' Hruntime'.shift) :=
          hsourceNormalized.trans Hc'.checking.tr.wf
            Hc'.mlctx_wf.tr.wf.toCtx hnormalizedEq
        have hexpanded := hfull.defeqDFC Hc'.checking.tr.wf.ordered
          (Hruntime'.context.defeqCtx.symm Hc'.checking.tr.wf.ordered)
        have hnarrow : Hc'.venv.IsDefEqU c.lparams.length
            (indexType :: scope.toCtx)
            narrowBody normalizedNarrow :=
          (VEnv.IsDefEqU.weak'_iff Hc'.checking.tr.wf
              Hruntime'.context.wf.toCtx Hruntime'.lift.toCtx).1 hexpanded
        have hdomainNarrow : ∃ sourceDom',
            TrExprS Hc'.venv c.lparams scope dom sourceDom' ∧
            Hc'.venv.IsDefEqU c.lparams.length scope.toCtx
              sourceDom' indexType :=
          ⟨_, hdomNarrow,
            ⟨.sort (Classical.choose hdomType),
              Classical.choose_spec hdomType⟩⟩
        have htransition : ∃ sourceBody' normalized',
            TrExprS Hc'.venv c.lparams
              ((none, .vlam indexType) :: scope)
              body sourceBody' ∧
            TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              normalized normalized' ∧
            Hc'.venv.IsDefEqU c.lparams.length
              (indexType :: scope.toCtx)
              sourceBody' normalized' :=
          ⟨narrowBody, normalizedNarrow, hbodyNarrow,
            hnormalizedNarrow, hnarrow⟩
        rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
            Hc'.checking.tr.wf
            (.forallE hdomType _hbodyType hdomNarrow hbodyNarrow)
            hscopeWF hdomainNarrow htransition with
          ⟨nextNarrow, hnextNarrow, Hsynthesis', hparamsPreserved⟩
        exact ih (fun Hc'' hlparams'' =>
            Hresult Hc'' (by simpa using hlparams'')) Hc'
          (by simpa [Nat.add_assoc] using
            Hcache.withIndex Hc Hdom.consumed Hdom.isType)
          (by simpa [Nat.add_assoc] using
            Hsuffix.withIndex Hc Hdom.consumed Hdom.isType)
          (by simpa [Nat.add_assoc] using
            (Hambient.withIndex Hdom.consumed Hdom.isType
              Hdom.source_defeq))
          (by change R Hc.venv; exact HR)
          Hsynthesis' (by
            rw [hparamsPreserved]
            change VEnv.IsDefEqCtx Hc.venv paramU []
              commonParams.reverse Hsynthesis.params.reverse
            exact Hparams) Hruntime' hnextNarrow
          hnormalizedFVars
          ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
    · exact Hresult Hc rfl hforall Hsynthesis Hruntime htypeNarrow
        htypeFVars htypeFull Hcache Hsuffix Hambient HR Hparams

end checkInductiveTypes.loopType

namespace checkInductiveTypes.loopInd

/-- At the first mutual header, the executable `whnf` result determines a
syntax-directed abstract normal form.  Independent translation of the source
header shows that this normal form is definitionally equal to the header in
`TrInductDecl`; the checked source type supplies the common typing witness. -/
theorem initialHeaderNormalization
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType := by
  rcases hnormalized with ⟨normalized', hnormalized', hnormalizedEq⟩
  have hsource : TrExprS Hc.venv c.lparams [] source.type sourceType := by
    simpa [hctx] using hchecked.2.1
  have htargetEq : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType :=
    Htarget.header.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsource
  have hsourceType : Hc.venv.HasType c.lparams.length []
      sourceType checkedType' := by
    simpa [hctx, VLCtx.toCtx] using hchecked.2.2.2
  have htargetType := hsourceType.defeqU_l Hc.checking.tr.wf
    (by trivial) htargetEq.symm
  have hnormalizedEq' : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType := by
    simpa [hctx, VLCtx.toCtx] using hnormalizedEq
  have htargetNormalized := htargetEq.trans Hc.checking.tr.wf
    (by trivial) hnormalizedEq'.symm
  exact ⟨normalized', checkedType', hnormalized',
    htargetNormalized.of_l Hc.checking.tr.wf (by trivial) htargetType⟩

/-- Package initial normalization with the empty executable telescope state.
This is the state consumed by the first parameter/index branch. -/
theorem initialHeaderState
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType ∧
      Nonempty (checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate
        Hc normalized' normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  exact ⟨normalized', exprType, hnormalized', hheader,
    ⟨checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate.empty hctxEq⟩⟩

/-- Definitional synthesis state used by the complete first-header recursion. -/
theorem initialHeaderSynthesisState
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.HeaderSynthesisCertificate
        Hc target normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.header.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.header.uvars] at hwf
    exact hwf
  have hcurrent : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader.toU
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.HeaderSynthesisCertificate.empty
      hctxEq hcurrent hheader⟩⟩

/-- A later source header is closed before cached parameters are substituted.
The outer `whnf` scope witness therefore initializes the narrow
later-parameter invariant at executable parameter zero. -/
noncomputable def initialLaterParameterScope
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (hi : 0 < stats.params.size)
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hnormalized : FVarsBelow Hc.mlctx.vlctx source.type normalized) :
    checkInductiveTypes.loopType.LaterParameterScope
      Hsuffix 0 normalized := by
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.header.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) Hc.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  exact checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars hi
    (hnormalized _ hfalseUpSet hsourceNoFVars)

/-- Although a later header is normalized in the retained first-header local
context, both the source header and its initial normal form are closed.  The
normalization equality therefore descends to the empty abstract context,
where it can seed an independent later-header telescope certificate. -/
theorem initialLaterHeaderDefEq
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length [] target.type normalized' := by
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  let W : VLCtx.FVLift [] Hc.mlctx.vlctx 0
      Hc.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil Hc.mlctx.noBV
  have hnormalizedClosed : Closed normalized 0 := by
    have := hnormalizedFull.closed
    simpa [Hc.mlctx.noBV] using this
  have hnormalizedNoFVars :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) normalized := by
    simpa [VLCtx.fvars] using hfvars
  rcases hnormalizedFull.weakFV_inv Hc.checking.tr.wf W
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedNoFVars with
    ⟨normalized', hnormalized'⟩
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.header.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hsourceClosed : Closed source.type 0 := by
    have := hchecked.2.1.closed
    simpa [Hc.mlctx.noBV] using this
  have hsourceNoFVars' :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) source.type := by
    simpa [VLCtx.fvars] using hsourceNoFVars
  rcases hchecked.2.1.weakFV_inv Hc.checking.tr.wf W
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hsourceClosed hsourceNoFVars' with
    ⟨sourceType', hsourceType'⟩
  have hnormalizedWeak := hnormalized'.weakFV Hc.checking.tr.wf.ordered
    W Hc.mlctx_wf.tr.wf
  have hsourceWeak := hsourceType'.weakFV Hc.checking.tr.wf.ordered
    W Hc.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hnormalizedWeak
  have hsourceUniq := hchecked.2.1.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hsourceWeak
  have hfull : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      (normalized'.liftN Hc.mlctx.vlctx.toCtx.length 0)
      (sourceType'.liftN Hc.mlctx.vlctx.toCtx.length 0) :=
    hnormalizedUniq.symm.trans Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.trans Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx hsourceUniq)
  have hempty : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType' :=
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx W.toCtx).1 hfull
  have htarget : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType' :=
    Htarget.header.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsourceType'
  exact ⟨normalized', hnormalized',
    htarget.trans Hc.checking.tr.wf (by trivial) hempty.symm⟩

/-- Initialize the narrow later-header synthesis state in the empty consumed
scope. -/
theorem initialLaterHeaderSynthesisState
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams target [] normalized' 0 0) := by
  rcases initialLaterHeaderDefEq Hc Htarget hchecked hnormalized hfvars with
    ⟨normalized', hnormalized', hheader⟩
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.header.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.header.uvars] at hwf
    exact hwf
  have hnormalizedType : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader
  rcases htargetType with ⟨targetLevel, htargetType⟩
  have hheaderTyped := hheader.of_l Hc.checking.tr.wf (by trivial)
    htargetType
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
      ⟨targetLevel, htargetType⟩ hnormalizedType hheaderTyped⟩⟩

private def updatedStats (stats : AddInductive.InductiveStats)
    (lctx : LocalContext) (resultLevel : Level) (setResult : Bool)
    (nindices : Nat) (indName : Name) : AddInductive.InductiveStats :=
  let stats := if setResult then
    { stats with
      lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
  else stats
  { stats with
    nindices := stats.nindices.push nindices
    indConsts := stats.indConsts.push (.const indName stats.levels) }

@[simp] theorem updatedStats_levels :
    (updatedStats stats lctx resultLevel setResult nindices indName).levels =
      stats.levels := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_nindices_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices.size =
      stats.nindices.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_nindices :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices =
      stats.nindices.push nindices := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_indConsts_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts.size =
      stats.indConsts.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_indConsts :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts =
      stats.indConsts.push (.const indName stats.levels) := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_params :
    (updatedStats stats lctx resultLevel setResult nindices indName).params =
      stats.params := by
  cases setResult <;> rfl

/-- Initialize the loop certificate when the first header fixes the common
result universe. -/
def HeaderLoopCertificate.first
    {c : AddInductive.Context} {decl : VInductDecl} {params : List VExpr}
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderLoopCertificate env c.lparams decl params
      (updatedStats stats c.lctx resultSort true nindices indName) 1 := by
  subst target
  exact {
    resultLevel := decl.types[0].resultLevel
    commonLevel := by simpa [updatedStats] using hofLevel
    headerPrefix := HeaderPrefixCertificate.first hindex hshape }

/-- Extend the loop certificate for a later mutual header using precisely the
successful production `isEquiv` guard and sort-translation witness. -/
def HeaderLoopCertificate.later
    {c : AddInductive.Context} {decl : VInductDecl} {params : List VExpr}
    (H : HeaderLoopCertificate env c.lparams decl params stats dIdx)
    (hindex : dIdx < decl.types.length)
    (htarget : decl.types[dIdx] = target)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderLoopCertificate env c.lparams decl params
      (updatedStats stats stats.lctx resultSort false nindices indName)
      (dIdx + 1) := by
  subst target
  exact {
    resultLevel := H.resultLevel
    commonLevel := by simpa [updatedStats] using H.commonLevel
    headerPrefix := H.headerPrefix.pushOfIsEquiv hindex hguard hofLevel
      H.commonLevel hshape }

def HeaderLoopCertificate.complete
    (H : HeaderLoopCertificate env lparams decl params stats
      decl.types.length) : HeaderCertificate env decl :=
  H.headerPrefix.complete

/-- Post-telescope continuation for the first mutual header. -/
theorem firstResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_pos hempty]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun c' h => ?_
  subst c'
  simpa [updatedStats, Expr.sortLevel!] using Hrec resultSort hsorted

/-- The first mutual header records its result universe and simultaneously
assembles the independent `TypeShape` certificate before continuing with the
remaining headers. -/
theorem firstResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv params target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  apply Hrec resultSort hofLevel
  exact TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

/-- Canonical first-header specialization: choose the first header's own
parameter telescope as the block-wide parameter list.  Its `ParamsDefEq`
obligation is reflexive and follows from local-context well-formedness. -/
theorem firstResult.refinesCanonical
    {decl : VInductDecl} {target : VInductiveType}
    {ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv ownParams target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  have hctxType : OnCtx (indices.reverse ++ ownParams.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using hctxEq.isType
  exact firstResult.refines k Q Hc hempty htype huvars hctxEq hheader
    hparamsTake hindicesTake
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel Hrec

/-- First-header result with the retained ambient-prefix invariant initialized
from the checked index telescope. -/
theorem firstResult.refinesRuntimeState
    {decl : VInductDecl} {target : VInductiveType}
    {ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv ownParams target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc ownParams indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.refinesCanonical k Q Hc hempty htype huvars hctxEq
    hheader hparamsTake hindicesTake hlevel
  intro resultSort hofLevel hshape
  exact Hrec resultSort hofLevel hshape
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq hctxEq)

/-- First-header result specialized to the state accumulated by the actual
`loopType` parameter/index branches.  The source telescope supplies the
parameter split, index split, and context-conversion premises. -/
theorem firstResult.refinesTelescope
    {decl : VInductDecl} {target : VInductiveType}
    {normalized result translatedResult exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Htelescope : checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate
      Hc normalized result decl.nparams nindices)
    (hnindices : nindices = target.numIndices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type translatedResult)
    (hresultEq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx result translatedResult)
    (huvars : c.lparams.length = decl.uvars)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv Htelescope.params target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Htelescope.params Htelescope.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst nindices
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  have hctxType : OnCtx
      (Htelescope.indices.reverse ++ Htelescope.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using Htelescope.telescope.context.isType
  have hshape := TrExpr.typeShapeOfDefEqCtxResult
    Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    Htelescope.telescope.context hheader Htelescope.takeParameters
    Htelescope.takeIndices
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hresultEq
    (hlevel resultSort) hsorted
  exact Hrec resultSort hofLevel hshape
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Htelescope.telescope.context)

/-- Post-telescope first-header refinement using the definitional synthesis
state produced by `firstHeaderSynthesisWF`. -/
theorem firstResult.refinesSynthesis
    {decl : VInductDecl} {target : VInductiveType}
    {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc target.toSkeleton current decl.nparams nindices)
    (hnindices : nindices = target.numIndices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv Hsynthesis.params target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst nindices
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  exact Hrec resultSort hofLevel
    (Hsynthesis.typeShape huvars (hlevel resultSort) hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)

/-- Metadata-synthesizing first-header continuation.  The executable index
counter and translated result sort are exported as data, together with a
declaration-independent shape proof; no pre-existing `VInductiveType`
metadata is assumed. -/
theorem firstResult.synthesizesHeader
    {source : VInductiveTypeSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc source current nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeader Hc.venv uvars nparams
        Hsynthesis.params source nindices resultLevel →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  exact Hrec resultSort resultLevel hofLevel
    (Hsynthesis.synthesizedHeader huvars hofLevel hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)

/-- Initialize the ordered mutual metadata prefix from the first successful
header result. -/
theorem firstResult.initializesPrefix
    {skeleton : VInductDeclSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (hindex : 0 < skeleton.types.length)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc skeleton.types[0] current skeleton.nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = skeleton.uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton Hsynthesis.params resultLevel [(nindices, resultLevel)] 1 →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.synthesizesHeader k Q Hc hempty Hsynthesis htype
    huvars
  intro resultSort resultLevel hofLevel Hheader Hambient
  exact Hrec resultSort resultLevel hofLevel
    (checkInductiveTypes.loopType.SynthesizedHeaderPrefix.first
      hindex Hheader) Hambient

/-- Post-telescope continuation for later mutual headers.  A mismatched result
universe throws; a successful path records the checked equivalence before
updating the per-type arrays. -/
theorem laterResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_neg (by simp [hnonempty])]
  by_cases hequiv : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = true
  · have hequiv' : resultSort.isEquiv stats.resultLevel = true := by
      simpa [Expr.sortLevel!] using hequiv
    simpa [updatedStats, Expr.sortLevel!, hequiv, hequiv'] using
      Hrec resultSort hequiv' hsorted
  · have hfalse : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = false := by
      cases h : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel <;>
        simp_all
    have hnot : (!(Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel) = true := by
      simp [hfalse]
    rw [if_pos hnot]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Every later mutual header produces the same independent `TypeShape`
certificate as the first header. The executable `isEquiv` guard is retained
as an explicit continuation premise; it is subsequently used to establish
the common-result-universe component of `FormationWF`. -/
theorem laterResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv params target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply laterResult.WF k Q Hc hnonempty htype
  intro resultSort hequiv hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  apply Hrec resultSort hequiv hofLevel
  exact TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

/-- Metadata-synthesizing continuation for a later mutual header.  The
executable result-universe guard extends the ordered metadata prefix, while
the successful parameter comparisons let the independently synthesized
header use the common parameter telescope fixed by the first family member.

This theorem deliberately starts at the post-telescope boundary.  The
per-binder later-header recursion has a different runtime shape from the
first header (cached parameters are substituted rather than introduced), so
it is verified separately instead of being hidden behind the first-header
invariant. -/
theorem laterResult.extendsPrefix
    {skeleton : VInductDeclSkeleton} {source : VInductiveTypeSkeleton}
    {current : VExpr} {commonParams : List VExpr}
    {metadata : List (Nat × VLevel)} {commonLevel : VLevel}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (hindex : dIdx < skeleton.types.length)
    (hsource : skeleton.types[dIdx] = source)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc source current skeleton.nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = skeleton.uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv skeleton.uvars []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst source
  apply laterResult.WF k Q Hc hnonempty htype
  intro resultSort hguard hsorted
  rcases TrExpr.sort_source hsorted with
    ⟨resultLevel, hofLevel, _hresult⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams huvars hparams
    hofLevel hsorted
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  exact Hrec resultSort resultLevel hguard hofLevel
    (Hprefix.push hindex hheader hlevel)

/-- Later-header result continuation for the independent narrow telescope.
The executable sort check runs in the retained runtime context; `resultSort`
restricts its translation before the synthesized header is added to the
ordered metadata prefix. -/
theorem laterResult.extendsPrefixNarrow
    {skeleton : VInductDeclSkeleton} {source : VInductiveTypeSkeleton}
    {narrowCurrent fullCurrent : VExpr} {scope : VLCtx}
    {commonParams : List VExpr}
    {metadata : List (Nat × VLevel)} {commonLevel : VLevel}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (hindex : dIdx < skeleton.types.length)
    (hsource : skeleton.types[dIdx] = source)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hsynthesis : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      Hc.venv c.lparams source scope narrowCurrent
      skeleton.nparams nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent)
    (huvars : c.lparams.length = skeleton.uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv skeleton.uvars []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst source
  rcases htypeFull with ⟨sourceFull, hsourceFull, _hsourceEq⟩
  apply laterResult.WF k Q Hc hnonempty hsourceFull
  intro resultSort hguard hsorted
  have hsourceFull' : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type sourceFull :=
    hsourceFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hsortedNarrow := Hruntime.resultSort Hc.checking.tr.wf
    htypeNarrow hsourceFull' hsorted
  rcases TrExpr.sort_source hsortedNarrow with
    ⟨resultLevel, hofLevel, _hresult⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams
    Hc.checking.tr.wf huvars hparams hofLevel hsortedNarrow
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  exact Hrec resultSort resultLevel hguard hofLevel
    (Hprefix.push hindex hheader hlevel)

/-- Base case of the mutual-header loop.  The executable assertions become
explicit invariants at the proof boundary instead of being silently erased. -/
theorem result.WF
    (hidx : ¬ dIdx < indTypes.size)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = indTypes.size)
    (hconsts : stats.indConsts.size = indTypes.size)
    (hparams : stats.params.size = nparams)
    (Hk : (k stats c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_neg hidx]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  simpa [hlevels, hindices, hconsts, hparams] using Hk

/-- Verified prefix of one mutual-header iteration: closed source checking and
WHNF are connected to the abstract translation before control enters the
already verified telescope loop.  The continuation owns the result-sort,
statistics update, and recursive mutual iteration invariants. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_pos hidx]
  change (AddInductive.checkClosedType indTypes[dIdx].name indTypes[dIdx].type c >>=
    fun _ => ((do
      let normalized ← TypeChecker.whnf indTypes[dIdx].type
      AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k)) : AddInductive.M _) c).WF Q
  exact (checkClosedType.WF Hc).bind fun checkedType hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    exact (whnfInContext.scopeWF Hc hchecked.2.1).bind
      fun normalized hnormalized =>
      Hloop checkedType type' checkedType' hchecked normalized
        hnormalized.1 hnormalized.2

/-- Metadata-free declaration-facing header step.  This is the entry point
used before `checkInductiveTypes` has recovered enough information to build a
`VInductDecl`. -/
theorem stepPrefix.refinesSkeleton
    {skeleton : VInductDeclSkeleton}
    {envTypes envCtors : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonCore Hc.venv c.lparams nparams
      indTypes.toList isUnsafe skeleton envTypes envCtors)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ envTypes,
        Hc.venv.addConsts skeleton.typeConstants = some envTypes →
        ∀ target,
        skeleton.types[dIdx]? = some target →
        TrInductiveTypeSkeleton Hc.venv envTypes c.lparams
          indTypes[dIdx] target →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices =>
            show AddInductive.M _ from do
            let type ← TypeChecker.ensureSort type
            let mut stats := stats
            let resultLevel := type.sortLevel!
            if stats.indConsts.isEmpty then
              let lctx := (← read).lctx
              stats := { stats with
                lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
            else if !resultLevel.isEquiv stats.resultLevel then
              throw <| .other
                "mutually inductive types must live in the same universe"
            stats := { stats with
              nindices := stats.nindices.push nindices
              indConsts := stats.indConsts.push
                (.const indTypes[dIdx].name stats.levels) }
            AddInductive.checkInductiveTypes.loopInd nparams indTypes
              (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  have htarget : dIdx < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl]
    simpa using hidx
  have htargetTr :=
    Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.typeAt Hdecl dIdx
      (by simpa using hidx) htarget
  apply stepPrefix.WF (nparams := nparams) (stats := stats) (k := k)
    (Q := Q) Hc hidx
  intro checkedType type' checkedType' hchecked normalized hscope hnormalized
  exact Hloop checkedType type' checkedType' hchecked envTypes Hdecl.typesAdded
    skeleton.types[dIdx] (by simp [htarget]) (by simpa using htargetTr)
    normalized hscope hnormalized

/-- Complete first iteration of the executable mutual-header loop, from the
closed source check through initialization of the ordered synthesized
metadata prefix. -/
theorem firstStep.initializesPrefix
    {skeleton : VInductDeclSkeleton}
    {envTypes envCtors : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonCore Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes envCtors)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel} {params : List VExpr},
      (Hc' : ContextWF c') →
      c'.lparams = c.lparams →
      stats'.levels = stats.levels →
      stats'.nindices = stats.nindices →
      stats'.indConsts = stats.indConsts →
      TrInductDeclSkeletonCore Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe skeleton envTypes envCtors →
      VLevel.ofLevel c'.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
        skeleton.nparams nindices →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' nindices →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc'.venv
        skeleton params resultLevel [(nindices, resultLevel)] 1 →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' params nindices →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 1
        (updatedStats stats' c'.lctx resultSort true nindices
          indTypes[0].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 0
      stats k c).WF Q := by
  have hskeletonIdx : 0 < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl]
    simpa using hidx
  apply stepPrefix.refinesSkeleton (k := k) (Q := Q) Hc Hdecl hidx
  intro checkedType type' checkedType' hchecked translatedTypes htypes
    target htarget Htarget normalized _hscope hnormalized
  have htargetEq : target = skeleton.types[0] := by
    symm
    simpa [List.getElem?_eq_getElem hskeletonIdx] using htarget
  subst target
  rcases initialHeaderSynthesisState Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', hnormalized', ⟨Hsynthesis⟩⟩
  have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats 0 0 :=
    checkInductiveTypes.loopType.ParameterCachePrefix.empty hparams
  have Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats 0 :=
    checkInductiveTypes.loopType.ParameterContextSuffix.empty Hc hctx hparams
  apply checkInductiveTypes.loopType.firstHeaderSynthesisWF
    (Us := c.lparams) (target := skeleton.types[0])
    (nparams := skeleton.nparams) (stats := stats)
    (type := normalized) (current := normalized') (i := 0)
    (nindices := 0) (c := c)
    (k := fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push
          (.const indTypes[0].name stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 1
        stats k)
    (Q := Q) (hconsume := hconsume)
    (Hresult := by
      intro c' stats' type'' current'' i' nindices' Hc' hlparams'
        hempty' hlevels' hnindices' hconsts' Hdecl' hforall iEq Hcache'
        Hsuffix' Hsynthesis' htype'
      cases iEq
      apply firstResult.initializesPrefix k Q Hc' hempty' hskeletonIdx
        Hsynthesis' htype'
      · rw [hlparams', ← Hdecl.uvars]
      · intro resultSort resultLevel hofLevel Hprefix Hambient
        apply Hrec Hc' hlparams' hlevels' hnindices' hconsts'
          (by simpa [hlparams'] using Hdecl') hofLevel Hcache' Hsuffix'
          Hprefix
        simpa [Hsynthesis'.indexCount] using Hambient)
    (Hc := Hc) (hlparams := rfl) (hempty := hempty)
    (hlevelsStable := rfl) (hnindicesStable := rfl)
    (hconstsStable := rfl)
    (R := fun env => TrInductDeclSkeletonCore env c.lparams
      skeleton.nparams indTypes.toList isUnsafe skeleton envTypes envCtors)
    (HR := Hdecl)
    (Hcache := Hcache) (Hsuffix := Hsuffix) (Hsynthesis := Hsynthesis)
    (hphase := by
      intro _
      exact ⟨List.eq_nil_of_length_eq_zero Hsynthesis.indexCount, rfl⟩)
    (htype := hnormalized')

/-- Complete a noninitial mutual-header iteration.  Cached parameters are
consumed in an independent narrow telescope, later indices extend both the
runtime and outer-loop context certificates, and the result sort appends one
ordered metadata entry. -/
theorem laterStep.extendsPrefix
    {skeleton : VInductDeclSkeleton} {commonParams : List VExpr}
    {commonLevel : VLevel} {metadata : List (Nat × VLevel)}
    {envTypes envCtors : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonCore Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes envCtors)
    (hidx : dIdx < indTypes.size)
    (_hnoninitial : 0 < dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hparams : stats.params.size = skeleton.nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats skeleton.nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.lparams = c.lparams →
      TrInductDeclSkeletonCore Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe skeleton envTypes envCtors →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        skeleton.nparams (depth + nindices) →
      checkInductiveTypes.loopType.ParameterContextSuffix Hc'
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        (depth + nindices) →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc'.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      checkInductiveTypes.loopType.AmbientParamContext Hc'
        commonParams (depth + nindices) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
      dIdx stats k c).WF Q := by
  have hskeletonIdx : dIdx < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl]
    simpa using hidx
  apply stepPrefix.refinesSkeleton (k := k) (Q := Q) Hc Hdecl hidx
  intro checkedType type' checkedType' hchecked translatedTypes htypes
    target htarget Htarget normalized hbelow hnormalized
  have htargetEq : target = skeleton.types[dIdx] := by
    symm
    simpa [List.getElem?_eq_getElem hskeletonIdx] using htarget
  subst target
  have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized := by
    have hsourceNoFVars : FVarsIn (fun _ => False)
        indTypes[dIdx].type :=
      Htarget.header.type.fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False)
        Hc.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    exact hbelow _ hfalseUpSet hsourceNoFVars
  rcases initialLaterHeaderSynthesisState Hc Htarget hchecked
      hnormalized hnormalizedNoFVars with
    ⟨narrowCurrent, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
  let Hscope : ∀ h : 0 < stats.params.size,
      checkInductiveTypes.loopType.LaterParameterScope Hsuffix 0
        normalized := fun h =>
    initialLaterParameterScope Hc Hsuffix h Htarget hbelow
  apply checkInductiveTypes.loopType.laterParameterSynthesisWF Hc
    (target := skeleton.types[dIdx])
    (k := fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push
          (.const indTypes[dIdx].name stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k)
    (Q := Q) hnonempty Hsuffix
    (Hresult := by
      intro type'' narrow'' full'' scope'' i'' fuel'' hi'' Hsynthesis''
        hscope'' htypeNarrow'' htypeFVars'' htypeFull''
      cases hi''
      subst scope''
      let Hruntime :=
        checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix
      have hindices'' : Hsynthesis''.indices = [] :=
        List.eq_nil_of_length_eq_zero Hsynthesis''.indexCount
      have hparamScope : Hsuffix.parameterDecls.toCtx =
          Hsynthesis''.params.reverse := by
        simpa [hindices''] using Hsynthesis''.scopeCtx
      have hparamsBoundary := Hsuffix.paramsDefEq Hambient <|
        Hprefix.parameterCount.trans hparams.symm
      rw [hparamScope] at hparamsBoundary
      apply checkInductiveTypes.loopType.laterIndexSynthesisWF
        (depth := depth) (commonParams := commonParams)
        (paramU := c.lparams.length)
        (R := fun env =>
          checkInductiveTypes.loopType.SynthesizedHeaderPrefix env
              skeleton commonParams commonLevel metadata dIdx ∧
            TrInductDeclSkeletonCore env c.lparams skeleton.nparams
              indTypes.toList isUnsafe skeleton envTypes envCtors)
        (k := fun type stats nindices => show AddInductive.M α from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other
              "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
            (dIdx + 1) stats k)
        (Q := Q)
        (Hresult := by
          intro c' Hc' hlparams' type''' narrow''' full''' scope'''
            nindices''' fuel''' hforall''' Hsynthesis''' Hruntime'''
            htypeNarrow''' _htypeFVars''' htypeFull''' Hcache'''
            Hsuffix''' Hambient''' HR''' hparams'''
          rcases HR''' with ⟨Hprefix''', Hdecl'''⟩
          apply checkInductiveTypes.loopType.result.WF
            (fuel := fuel''') (Q := Q) hforall''' rfl
          apply laterResult.extendsPrefixNarrow
            (indTypes := indTypes) (indName := indTypes[dIdx].name)
            (commonParams := commonParams) (metadata := metadata)
            (commonLevel := commonLevel) k Q Hc' hnonempty
            hskeletonIdx rfl Hprefix''' Hsynthesis'''
            Hruntime''' htypeNarrow''' htypeFull'''
          · rw [hlparams', ← Hdecl.uvars]
          · simpa [hlparams', ← Hdecl.uvars] using hparams'''
          · simpa [hlparams'] using hcommon
          · intro resultSort resultLevel hguard hofLevel Hprefix'
            apply Hrec Hc' hlparams'
            · simpa [hlparams'] using Hdecl'''
            · exact Hcache'''.reindex (by simp [updatedStats])
            · exact Hsuffix'''.reindex (by simp [updatedStats])
            · exact Hprefix'
            · exact Hambient''')
        hconsume Hc (by simpa using Hcache) (by simpa using Hsuffix)
        (by simpa using Hambient) ⟨Hprefix, Hdecl⟩ Hsynthesis''
        hparamsBoundary
        Hruntime
        htypeNarrow'' htypeFVars'' htypeFull'')
    hparams (by omega) Hscope
    (fun h => (Hscope h).older_eq_nil h |>.symm)
    (by
      intro hzero
      have hsize : stats.params.size = 0 := hparams.trans hzero.symm
      apply (List.eq_nil_of_length_eq_zero ?_).symm
      rw [Hsuffix.parameterDecls_length, hsize])
    Hsynthesis hnormalizedNarrow (by simpa [VLCtx.fvars] using
      hnormalizedNoFVars) hnormalized

/-- Concrete statistics recovered together with a materialized mutual header.
This is the early traversal-facing form of `ValidAppStatsWF`; it is kept here
because the latter also packages the derived name-search invariant used by
positivity, which is defined after the executable constructor interfaces. -/
structure MaterializedHeaderResult (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (depth : Nat) where
  headers : HeaderCertificate env decl
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : stats.indConsts =
    (decl.types.map fun type => .const type.name stats.levels).toArray
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv
  parameterScope : VLCtx
  ambientScope : VLCtx
  scopeDecomposition : Δ = ambientScope ++ parameterScope
  ambientLength : ambientScope.length = depth
  cachedScope : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse parameterScope
  runtimeScope : checkInductiveTypes.loopType.NarrowRuntimeScope
    env Us parameterScope Δ
  paramsContext : VEnv.IsDefEqCtx env Us.length []
    headers.params.reverse parameterScope.toCtx
  narrowParams : List.Forall₂ (TrExprS env Us parameterScope)
    stats.params.toList (decl.paramVars 0)

private theorem forall₂_trExprS_mono {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {es : List Expr} {es' : List VExpr},
      List.Forall₂ (TrExprS env Us Δ) es es' →
      List.Forall₂ (TrExprS env' Us Δ) es es'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (h.mono henv)
      (forall₂_trExprS_mono henv hs)

def MaterializedHeaderResult.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    MaterializedHeaderResult env' Us Δ stats decl depth where
  headers := H.headers.mono henv
  levels := H.levels
  uvars := H.uvars
  consts := H.consts
  indices := H.indices
  params := forall₂_trExprS_mono henv H.params
  paramFVars := H.paramFVars
  parameterScope := H.parameterScope
  ambientScope := H.ambientScope
  scopeDecomposition := H.scopeDecomposition
  ambientLength := H.ambientLength
  cachedScope := H.cachedScope
  runtimeScope := H.runtimeScope.mono henv
  paramsContext := H.paramsContext.mono henv
  narrowParams := forall₂_trExprS_mono henv H.narrowParams

/-- Fold the verified noninitial step over the remainder of the mutual block.
At exact coverage the executable length assertions are discharged and the
metadata-free declaration is materialized together with its header
certificate. -/
theorem laterSteps.materialize
    {skeleton : VInductDeclSkeleton} {commonParams : List VExpr}
    {commonLevel : VLevel} {metadata : List (Nat × VLevel)}
    {envTypes envCtors : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonCore Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes envCtors)
    (hdone : dIdx ≤ indTypes.size)
    (hpositive : 0 < dIdx)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = dIdx)
    (hconsts : stats.indConsts.size = dIdx)
    (hindicesExact : stats.nindices.toList = metadata.map Prod.fst)
    (hconstsExact : stats.indConsts =
      ((skeleton.types.take dIdx).map fun type =>
        .const type.name stats.levels).toArray)
    (hparams : stats.params.size = skeleton.nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats skeleton.nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth' : Nat},
      (Hc' : ContextWF c') →
      TrInductDeclCore Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl envTypes envCtors →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth' →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
      dIdx stats k c).WF Q := by
  by_cases hidx : dIdx < indTypes.size
  · have hnonempty : stats.indConsts.isEmpty = false := by
      cases hempty : stats.indConsts.isEmpty
      · rfl
      · have hzero : stats.indConsts.size = 0 := by
          simpa [Array.isEmpty] using hempty
        omega
    have htargetIdx : dIdx < skeleton.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl]
      simpa using hidx
    have hname := Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.typeNameAt
      Hdecl dIdx (by simpa using hidx) htargetIdx
    have hname' : indTypes[dIdx].name = skeleton.types[dIdx].name := by
      simpa using hname
    apply laterStep.extendsPrefix k Q Hc Hdecl hidx hpositive hnonempty
      hparams Hcache Hsuffix Hprefix Hambient hcommon hconsume
    intro c' nindices resultSort resultLevel Hc' hlparams' Hdecl'
      Hcache' Hsuffix' Hprefix' Hambient'
    apply laterSteps.materialize k Q Hc' Hdecl'
      (dIdx := dIdx + 1) (depth := depth + nindices)
      (stats := updatedStats stats stats.lctx resultSort false nindices
        indTypes[dIdx].name)
      (metadata := metadata ++ [(nindices, resultLevel)])
      (commonParams := commonParams) (commonLevel := commonLevel)
    · omega
    · omega
    · simpa [updatedStats, hlparams'] using hlevels
    · simp [updatedStats, hindices]
    · simp [updatedStats, hconsts]
    · simp [updatedStats, hindicesExact]
    · rw [List.take_succ_eq_append_getElem]
      · simp [updatedStats, hconstsExact, hname']
      · rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl]
        simpa using hidx
    · simpa [updatedStats] using hparams
    · exact Hcache'
    · exact Hsuffix'
    · exact Hprefix'
    · exact Hambient'
    · simpa [updatedStats, hlparams'] using hcommon
    · exact hconsume
    · intro c'' stats'' decl depth'' Hc'' Hdecl'' Hresult
      exact Hfinish Hc'' Hdecl'' Hresult
  · have heq : dIdx = indTypes.size := by omega
    have htypes : skeleton.types.length = indTypes.size := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl]
      simp
    have Hprefix' : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
        Hc.venv skeleton commonParams commonLevel metadata
          skeleton.types.length := by
      simpa [heq, htypes] using Hprefix
    rcases Hprefix'.materializes with
      ⟨decl, hmaterialize, _⟩
    let Hheaders := Hprefix'.complete hmaterialize
    have hfields := VInductDeclSkeleton.materialize_fields hmaterialize
    have herase := VInductDeclSkeleton.materialize_toSkeleton hmaterialize
    have Hdecl' :=
      Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.materialized
        Hdecl hmaterialize
    apply checkInductiveTypes.loopInd.result.WF
      (k := k) (Q := Q) hidx hlevels
    · simpa [heq] using hindices
    · simpa [heq] using hconsts
    · exact hparams
    · apply Hfinish (depth' := depth) Hc Hdecl'
      refine {
        headers := Hheaders
        levels := ?_
        uvars := ?_
        consts := ?_
        indices := ?_
        params := ?_
        paramFVars := Hcache.paramFVars
        parameterScope := Hsuffix.parameterDecls
        ambientScope := Hsuffix.ambientDecls
        scopeDecomposition := Hsuffix.context
        ambientLength := Hsuffix.prefixLength
        cachedScope := Hsuffix.cached
        runtimeScope :=
          checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix
        paramsContext := ?_
        narrowParams := ?_ }
      · exact hlevels.trans (Hdecl.uvars.symm.trans hfields.1.symm)
      · exact Hdecl.uvars.symm.trans hfields.1.symm
      · have hconstMap :
            (decl.types.map fun type => Expr.const type.name stats.levels) =
              (skeleton.types.map fun type =>
                Expr.const type.name stats.levels) := by
          have := congrArg (fun d : VInductDeclSkeleton =>
            d.types.map fun type => Expr.const type.name stats.levels) herase
          simpa [VInductDecl.toSkeleton, VInductiveType.toSkeleton,
            Function.comp_def] using this
        calc
          stats.indConsts =
              (skeleton.types.map fun type =>
                .const type.name stats.levels).toArray := by
            have hd : dIdx = skeleton.types.length := heq.trans htypes.symm
            simpa [hd] using hconstsExact
          _ = (decl.types.map fun type =>
                .const type.name stats.levels).toArray := by
            rw [hconstMap]
      · have hmetadata : metadata.map Prod.fst =
            decl.types.map (·.numIndices) := by
          have zipIndices : ∀ (types : List VInductiveTypeSkeleton)
              (data : List (Nat × VLevel)), data.length = types.length →
              (List.zipWith (fun type datum =>
                type.toVInductiveType datum.1 datum.2) types data).map
                  (·.numIndices) = data.map Prod.fst := by
            intro types data hlength
            induction types generalizing data with
            | nil => simpa using hlength
            | cons type types ih =>
              cases data with
              | nil => simp at hlength
              | cons datum data =>
                simp only [List.length_cons] at hlength
                change datum.1 ::
                    (List.zipWith (fun type datum =>
                      type.toVInductiveType datum.1 datum.2)
                      types data).map (·.numIndices) =
                    datum.1 :: data.map Prod.fst
                exact congrArg (List.cons datum.1) (ih data (by omega))
          have hmetadataLength :=
            VInductDeclSkeleton.materialize_length hmaterialize
          simp only [VInductDeclSkeleton.materialize] at hmaterialize
          split at hmaterialize
          · simp only [Option.some.injEq] at hmaterialize
            subst decl
            exact (zipIndices skeleton.types metadata hmetadataLength).symm
          · contradiction
        exact hindicesExact.trans hmetadata
      · have Hcache' : checkInductiveTypes.loopType.ParameterCachePrefix
            Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams depth := by
          rw [hfields.2.1]
          exact Hcache
        exact Hcache'.complete
      · apply Hsuffix.paramsDefEq Hambient
        exact Hprefix.parameterCount.trans hparams.symm
      · rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
        have hsize : stats.params.size = decl.nparams := by
          exact hparams.trans hfields.2.1.symm
        simpa [hsize] using Hsuffix.narrowParams
termination_by indTypes.size - dIdx

def MaterializedHeaderResult.parameterSuffix
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MaterializedHeaderResult Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth) :
    checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth where
  ambientDecls := H.ambientScope
  parameterDecls := H.parameterScope
  context := H.scopeDecomposition
  prefixLength := H.ambientLength
  cached := H.cachedScope
  narrowParams := by
    have hsize : stats.params.size = decl.nparams := by
      have hlength :=
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.narrowParams
      simpa [VInductDecl.paramVars] using hlength
    rw [hsize,
      checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
    exact H.narrowParams

/-- Complete the whole nonempty mutual-header phase, including the special
first header that establishes the common parameters and result universe. -/
theorem firstStep.materialize
    {skeleton : VInductDeclSkeleton}
    {envTypes envCtors : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonCore Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes envCtors)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevels : stats.levels.length = c.lparams.length)
    (hnindices : stats.nindices = #[])
    (hconsts : stats.indConsts = #[])
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth' : Nat},
      (Hc' : ContextWF c') →
      TrInductDeclCore Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl envTypes envCtors →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth' →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 0
      stats k c).WF Q := by
  apply firstStep.initializesPrefix k Q Hc Hdecl hctx hidx hempty hparams
    hconsume
  intro c' stats' nindices resultSort resultLevel params Hc' hlparams'
    hlevels' hnindices' hconsts' Hdecl' hofLevel Hcache' Hsuffix'
    Hprefix' Hambient'
  let statsNext := updatedStats stats' c'.lctx resultSort true nindices
    indTypes[0].name
  have hparamSize : stats'.params.size = skeleton.nparams := by
    have hlength :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hcache'.params
    simpa using hlength
  have hskeletonIdx : 0 < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.types_length Hdecl']
    simpa using hidx
  have hname := Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.typeNameAt
    Hdecl' 0 (by simpa using hidx) hskeletonIdx
  have hname' : indTypes[0].name = skeleton.types[0].name := by
    simpa using hname
  apply laterSteps.materialize k Q Hc' Hdecl'
    (dIdx := 1) (depth := nindices) (stats := statsNext)
    (metadata := [(nindices, resultLevel)])
    (commonParams := params) (commonLevel := resultLevel)
  · omega
  · omega
  · simpa [statsNext, updatedStats, hlevels', hlparams'] using hlevels
  · simp [statsNext, updatedStats, hnindices', hnindices]
  · simp [statsNext, updatedStats, hconsts', hconsts]
  · simp [statsNext, updatedStats, hnindices', hnindices]
  · rw [List.take_succ_eq_append_getElem hskeletonIdx]
    simp [statsNext, updatedStats, hconsts', hconsts, hname']
  · simpa [statsNext, updatedStats] using hparamSize
  · exact Hcache'.reindex (by simp [statsNext, updatedStats])
  · exact Hsuffix'.reindex (by simp [statsNext, updatedStats])
  · exact Hprefix'
  · exact Hambient'
  · simpa [statsNext, updatedStats] using hofLevel
  · exact hconsume
  · exact Hfinish

/-- Public verifier for the executable mutual-header checker.  Successful
checking returns a materialized abstract declaration, its source translation,
and the independent header specification certificate to the continuation. -/
theorem checkInductiveTypes.materialize
    {skeleton : VInductDeclSkeleton}
    {envTypes envCtors : VEnv}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonCore Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton envTypes envCtors)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat},
      (Hc' : ContextWF c') →
      TrInductDeclCore Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl envTypes envCtors →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes skeleton.nparams indTypes k c).WF Q := by
  change (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
    0 { (default : AddInductive.InductiveStats) with
      levels := c.lparams.map .param } k c).WF Q
  apply firstStep.materialize k Q Hc Hdecl hctx hnonempty
  · rfl
  · simp
  · rfl
  · rfl
  · rfl
  · exact hconsume
  · exact Hfinish

/-- Indexed declaration-facing form of `stepPrefix.WF`.  Besides the checked
source translation, the continuation receives the exact corresponding
abstract mutual header and the environment obtained by installing all header
constants. -/
theorem stepPrefix.refinesTrInduct
    {decl : VInductDecl}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDecl Hc.venv c.lparams nparams
      indTypes.toList isUnsafe decl)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ envTypes,
        Hc.venv.addConsts decl.typeConstants = some envTypes →
        ∀ target,
        decl.types[dIdx]? = some target →
        TrInductiveType Hc.venv envTypes c.lparams
          indTypes[dIdx] target →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices =>
            show AddInductive.M _ from do
            let type ← TypeChecker.ensureSort type
            let mut stats := stats
            let resultLevel := type.sortLevel!
            if stats.indConsts.isEmpty then
              let lctx := (← read).lctx
              stats := { stats with
                lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
            else if !resultLevel.isEquiv stats.resultLevel then
              throw <| .other
                "mutually inductive types must live in the same universe"
            stats := { stats with
              nindices := stats.nindices.push nindices
              indConsts := stats.indConsts.push
                (.const indTypes[dIdx].name stats.levels) }
            AddInductive.checkInductiveTypes.loopInd nparams indTypes
              (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  have htarget : dIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDecl.types_length Hdecl]
    simpa using hidx
  rcases Lean4Lean.VerifyInductive.TrInductDecl.typeAt Hdecl dIdx
      (by simpa using hidx) htarget with
    ⟨envTypes, htypes, htargetTr⟩
  apply stepPrefix.WF (nparams := nparams) (stats := stats) (k := k)
    (Q := Q) Hc hidx
  intro checkedType type' checkedType' hchecked normalized hscope hnormalized
  exact Hloop checkedType type' checkedType' hchecked envTypes htypes
    decl.types[dIdx] (by simp [htarget]) (by simpa using htargetTr)
    normalized hscope hnormalized

end checkInductiveTypes.loopInd

namespace checkConstructors.loopCtors

theorem result.WF
    (hidx : ¬ ctorIdx < ctors.length) (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_neg hidx]
  exact Except.WF.pure hQ

/-- One constructor-loop iteration up to the already verified telescope
checker. The continuation receives the closed source translation before
choosing the public `CtorShape` refinement. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
  rw [if_neg (by simpa using hfresh)]
  exact (checkClosedType.WF Hc).bind fun _ hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
      ((AddInductive.checkConstructors.loopCtor stats isUnsafe
          ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
          c'.fuel.inductiveFuel >>= fun _ =>
        AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
          (foundCtors.insert ctors[ctorIdx].name)) : AddInductive.M Unit) c).WF Q
    have hread : ((read : AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine hread.bind fun c' hc' => ?_
    subst c'
    exact (Hloop _ type' checkedType' hchecked).bind fun _ hnext => hnext

/-- Shape-producing constructor step. This is the interface used by the
flattened constructor-prefix accumulator; all telescope details remain local
to `Hshape`. -/
theorem stepShape.WF
    {decl : VInductDecl} {target : VInductiveType} {ctor' : VConstVal}
    {envTypes : VEnv} {params : List VExpr}
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hshape : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target ctor')
    (Hnext : decl.CtorShape envTypes params target ctor' →
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  apply stepPrefix.WF (stats := stats) (isUnsafe := isUnsafe)
    (targetIdx := targetIdx) (Q := Q) Hc hidx hfresh
  intro checkedType type' checkedType' hchecked
  exact (Hshape checkedType type' checkedType' hchecked).mono fun _ hshape =>
    Hnext hshape

theorem stepCertificate.WF
    {decl : VInductDecl} {target : VInductiveType} {ctor' : VConstVal}
    {envTypes : VEnv} {params : List VExpr} {done : Nat}
    (Hc : ContextWF c)
    (Hprefix : ConstructorPrefixCertificate Hc.venv decl envTypes params done)
    (hdone : done < decl.ownedConstructors.length)
    (howned : decl.ownedConstructors[done] = (target, ctor'))
    (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hshape : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target ctor')
    (Hnext : ConstructorPrefixCertificate Hc.venv decl envTypes params
        (done + 1) →
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  apply stepShape.WF (decl := decl) (target := target) (ctor' := ctor')
    (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
    (Q := Q) Hc hidx hfresh Hshape
  intro hshape
  have hshape' : decl.CtorShape envTypes params
      decl.ownedConstructors[done].1 decl.ownedConstructors[done].2 := by
    rw [howned]
    exact hshape
  exact Hnext (Hprefix.push hdone hshape')

/-- Complete the production constructor loop for one family.  Name-set
freshness is exposed against the exact reachable state, while semantic shape
checking is supplied one translated constructor at a time. -/
theorem refinesType
    {decl : VInductDecl} {target : VInductiveType}
    {sourceEnv envTypes : VEnv} {params : List VExpr}
    {source : InductiveType}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htarget : TrInductiveType sourceEnv envTypes c.lparams source target)
    (Hnames : ConstructorNameState source.ctors ctorIdx foundCtors)
    (Hprefix : ConstructorTypePrefix envTypes decl params target ctorIdx)
    (Hfresh : ∀ {i found}, ConstructorNameState source.ctors i found →
      (hi : i < source.ctors.length) →
      found.contains source.ctors[i].name = false)
    (Hshape : ∀ i (hsource : i < source.ctors.length)
      (htarget : i < target.ctors.length),
      TrSourceConst envTypes c.lparams source.ctors[i].name
        source.ctors[i].type target.ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        source.ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        source.ctors[i].name targetIdx source.ctors[i].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target target.ctors[i])
    (Hfinish : ConstructorTypePrefix envTypes decl params target
        target.ctors.length →
      Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepShape.WF (decl := decl) (target := target)
      (ctor' := target.ctors[ctorIdx]) (Q := Q) Hc hidx
      (Hfresh Hnames hidx)
    · intro checkedType type' checkedType' hchecked
      exact Hshape ctorIdx hidx htarget Hctor checkedType type'
        checkedType' hchecked
    · intro hshape
      exact refinesType Q Hc Htarget (.succ Hnames hidx)
        (Hprefix.push htarget hshape) Hfresh Hshape Hfinish
  · have heq : ctorIdx = source.ctors.length := by
      have := Hprefix.covered
      rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htarget]
        at this
      omega
    apply result.WF (Q := Q) hidx
    have Hcomplete : ConstructorTypePrefix envTypes decl params target
        target.ctors.length := by
      simpa [heq,
        Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htarget] using
          Hprefix
    exact Hfinish Hcomplete
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

theorem result.WF
    (hidx : ¬ targetIdx < indTypes.size) (hQ : Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_neg hidx]
  exact Except.WF.pure hQ

theorem step.WF
    (hidx : targetIdx < indTypes.size)
    (Hctors :
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        indTypes[targetIdx].ctors 0 {} c).WF fun _ =>
      (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
        (targetIdx + 1) c).WF Q) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_pos hidx]
  exact Hctors.bind fun _ hnext => hnext

/-- Fold the verified inner constructor traversal over every family in a
mutual block, retaining the same two-dimensional order as the source arrays. -/
theorem refinesBlock
    {decl : VInductDecl} {sourceEnv envTypes : VEnv}
    {params : List VExpr}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveType sourceEnv envTypes c.lparams)
      indTypes.toList decl.types)
    (Hprefix : ConstructorTypesPrefix envTypes decl params targetIdx)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (Hshape : ∀ targetIdx (hsource : targetIdx < indTypes.size)
      (htarget : targetIdx < decl.types.length)
      i (hctorSource : i < indTypes[targetIdx].ctors.length)
      (hctorTarget : i < decl.types[targetIdx].ctors.length),
      TrSourceConst envTypes c.lparams indTypes[targetIdx].ctors[i].name
        indTypes[targetIdx].ctors[i].type decl.types[targetIdx].ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[targetIdx].ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[targetIdx].ctors[i].name targetIdx
        indTypes[targetIdx].ctors[i].type 0 c.fuel.inductiveFuel c).WF
        fun _ => decl.CtorShape envTypes params decl.types[targetIdx]
          decl.types[targetIdx].ctors[i])
    (Hfinish : ConstructorTypesPrefix envTypes decl params
        decl.types.length → Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      omega
    have Htarget : TrInductiveType sourceEnv envTypes c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.refinesType
      (Q := fun _ =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF Q)
      Hc Htarget .zero
      (ConstructorTypePrefix.empty envTypes decl params decl.types[targetIdx])
      (Hfresh targetIdx hidx)
    · intro i hsource htarget' Hctor checkedType type' checkedType' hchecked
      exact Hshape targetIdx hidx htarget i hsource htarget' Hctor
        checkedType type' checkedType' hchecked
    · intro Htype
      exact refinesBlock Q Hc Htypes
        (Hprefix.push htarget Htype) Hfresh Hshape Hfinish
  · have heq : targetIdx = indTypes.size := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      have := Hprefix.covered
      omega
    apply result.WF (Q := Q) hidx
    apply Hfinish
    have hlength : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
    simpa [heq, hlength] using Hprefix
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

namespace checkConstructors.loopCtor

theorem zero.WF :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkConstructors.loopCtor] at h

/-- A constructor telescope ending in the checked target application returns
success; the separate application-refinement theorem will connect
`isValidIndAppIdx` to `VInductDecl.ValidIndAppAt`. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals exact Except.WF.pure hQ

/-- An invalid non-forall constructor target is rejected. -/
theorem invalidResult.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = false) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Common-parameter branch of a constructor telescope.  The cached parameter
type comparison is converted directly into abstract body instantiation. -/
theorem parameter.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = some param)
    (hget : (AddInductive.getType param c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx param param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 param) (body'.inst param') →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel c).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  change (AddInductive.getType param c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other
          s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
      AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel) : AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact Hrec heq hopened

/-- Safe constructor-field branch.  Successful field typing, the executable
universe bound, positivity, annotation transport, and fresh body opening are
all delivered to the recursive continuation. -/
theorem safeField.sourceWF
    {Pos : Prop}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF (fun _ => Pos))
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      Pos →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !false then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    refine Hpos.bind fun _ hpos => ?_
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound hpos body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Unsafe constructor-field branch: the same source typing, universe, and
annotation obligations apply, while positivity is intentionally skipped. -/
theorem unsafeField.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !true then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

end checkConstructors.loopCtor

namespace checkPositivityStep

theorem hasIndOcc_eq_findAny :
    AddInductive.hasIndOcc indConsts type =
      type.findAny (fun
        | .const name _ => indConsts.any fun I => I.constName! == name
        | _ => false) := by
  unfold AddInductive.hasIndOcc
  exact Expr.find?_isSome_eq_findAny _ _

def IndConstNames (indConsts : Array Expr) (names : List Name) : Prop :=
  ∀ name, (indConsts.any fun I => I.constName! == name) = names.contains name

/-- The concrete array accumulated by header checking has exactly the abstract
mutual-family names, in declaration order.  Keeping this stronger structural
fact separate makes the weaker search correspondence above reusable by both
positivity and recursive-target validation. -/
structure IndConstArray (levels : List Level) (indConsts : Array Expr)
    (names : List Name) : Prop where
  exact : indConsts = (names.map fun name => .const name levels).toArray
  names : IndConstNames indConsts names

/-- The portion of the mutable header statistics needed to interpret a
recursive application in the independent declaration.  In particular, the
common parameters are related by expression translation rather than merely by
array position. -/
structure ValidAppStatsWF (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

theorem forall₂_length_eq
    (H : List.Forall₂ R as bs) : as.length = bs.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.mapM_some_length
    {xs : List α} {ys : List β} {f : α → Option β}
    (H : xs.mapM f = some ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    simp at H
    subst ys
    rfl
  | cons x xs ih =>
    cases hx : f x <;> simp [hx] at H
    rename_i y
    cases hxs : xs.mapM f <;> simp [hxs] at H
    rename_i ys'
    subst ys
    simp [ih hxs]

theorem forall₂_get?_eq_some
    {R : α → β → Prop} {as : List α} {bs : List β}
    {i : Nat} {a : α} {b : β}
    (H : List.Forall₂ R as bs)
    (ha : as[i]? = some a) (hb : bs[i]? = some b) : R a b := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero =>
      simp at ha hb
      subst a
      subst b
      exact h
    | succ i => exact ih (by simpa using ha) (by simpa using hb)

theorem ValidAppStatsWF.params_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.params.size = decl.nparams := by
  have := forall₂_length_eq H.params
  simpa [VInductDecl.paramVars] using this

theorem ValidAppStatsWF.types_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem ValidAppStatsWF.indConstAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem ValidAppStatsWF.nindicesAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem ValidAppStatsWF.paramAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env Us Δ stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlen := forall₂_length_eq H.params
      simpa using hlen ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    forall₂_get?_eq_some H.params hsource htarget⟩

theorem ValidAppStatsWF.paramFVarAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

theorem forall₂_map_right
    (H : List.Forall₂ R as bs)
    (hf : ∀ {a b}, R a b → S a (f b)) :
    List.Forall₂ S as (bs.map f) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hf h) ih

@[simp] theorem VInductDecl.paramVars_liftN
    {decl : VInductDecl} {depth : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN 1 e 0) =
      decl.paramVars (depth + 1) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  omega

theorem ValidAppStatsWF.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsWF
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  have W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 := by
    change VLCtx.FVLift Hc.mlctx.vlctx
      ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) 0 1 0
    exact .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    H.params fun h =>
      h.weakFV Hc'.checking.tr.wf W Hc'.mlctx_wf.tr.wf
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  change List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    stats.params.toList (decl.paramVars (depth + 1))
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

/-- Extend application statistics in an independently tracked semantic scope.
Unlike `withLocalDecl`, this theorem does not require the executable context
to be that scope; the already verified target-context extension is sufficient
for weakening the cached parameter translations. -/
theorem ValidAppStatsWF.withFVar
    (H : ValidAppStatsWF env Us scope stats decl depth)
    (henv : env.WF)
    (hscope' : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam fieldType) :: scope)) :
    ValidAppStatsWF env Us
      ((some (fv, deps), .vlam fieldType) :: scope)
      stats decl (depth + 1) := by
  let W : VLCtx.FVLift scope
      ((some (fv, deps), .vlam fieldType) :: scope) 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS env Us
      ((some (fv, deps), .vlam fieldType) :: scope))
    H.params fun h => h.weakFV henv.ordered W hscope'
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

theorem IndConstArray.empty (levels : List Level) :
    IndConstArray levels #[] [] where
  exact := rfl
  names := by simp [IndConstNames, Array.any]

theorem IndConstArray.push
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (H : IndConstArray levels indConsts names) (newName : Name) :
    IndConstArray levels (indConsts.push (.const newName levels))
      (names ++ [newName]) where
  exact := by rw [H.exact]; simp
  names := by
    intro name
    rw [Array.any_push, H.names name]
    change (names.contains name || (newName == name)) =
      (names ++ [newName]).contains name
    rw [List.contains_append]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, List.contains_cons,
      List.contains_nil, Bool.or_false]
    exact eq_comm

theorem IndConstArray.ofExact
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (h : indConsts = (names.map fun name => .const name levels).toArray) :
    IndConstArray levels indConsts names where
  exact := h
  names := by
    intro name
    apply Bool.eq_iff_iff.mpr
    simp [h]
    constructor
    · rintro ⟨source, hsource, hname⟩
      have : source = name := by
        simpa [Expr.constName!] using hname
      simpa [this] using hsource
    · intro hname
      exact ⟨name, hname, by simp [Expr.constName!]⟩

/-- Promote the exact traversal-facing statistics into the positivity-facing
application invariant. -/
def ValidAppStatsWF.ofMaterializedHeader
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us Δ stats decl depth where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.params
  paramFVars := H.paramFVars

def ValidAppStatsWF.ofMaterializedHeaderNarrow
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us H.parameterScope stats decl 0 where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.narrowParams
  paramFVars := H.paramFVars

theorem IndConstArray.updatedStats
    {stats : AddInductive.InductiveStats} {names : List Name}
    {lctx : LocalContext} {resultLevel : Level} {setResult : Bool}
    {nindices : Nat} {indName : Name}
    (H : IndConstArray stats.levels stats.indConsts names) :
    IndConstArray
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).levels
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).indConsts
      (names ++ [indName]) := by
  simpa using H.push indName

/-- Incremental form of `ValidAppStatsWF`, synchronized with the mutual-header
loop before all family members have been visited. -/
structure ValidAppStatsPrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth done : Nat) : Prop where
  covered : done ≤ decl.types.length
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    ((decl.types.take done).map (·.name))
  indices : stats.nindices.toList =
    (decl.types.take done).map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- Convert the completed first-header telescope invariant into the initial
mutual-family statistics prefix, just before the first family constant and
index count are appended. -/
def ValidAppStatsPrefix.beforeFirst
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      env Us Δ stats decl.nparams depth)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : Us.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[]) :
    ValidAppStatsPrefix env Us Δ stats decl depth 0 where
  covered := Nat.zero_le _
  levels := hlevels
  uvars := huvars
  consts := by
    simpa [hconsts] using IndConstArray.empty stats.levels
  indices := by simp [hindices]
  params := Hcache.complete
  paramFVars := Hcache.paramFVars

theorem ValidAppStatsPrefix.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsPrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth done)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsPrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) done := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList (decl.paramVars (depth + 1)) := by
    rw [← VInductDecl.paramVars_liftN]
    exact forall₂_map_right H.params fun h =>
      h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
  exact {
    covered := H.covered
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := hparams
    paramFVars := H.paramFVars }

theorem ValidAppStatsPrefix.push
    (H : ValidAppStatsPrefix env Us Δ stats decl depth done)
    (hindex : done < decl.types.length)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices) :
    ValidAppStatsPrefix env Us Δ
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName)
      decl depth (done + 1) := by
  have htake : decl.types.take (done + 1) =
      decl.types.take done ++ [decl.types[done]] :=
    List.take_succ_eq_append_getElem hindex
  refine {
    covered := by omega
    levels := by simpa using H.levels
    uvars := H.uvars
    consts := ?_
    indices := ?_
    params := by simpa using H.params
    paramFVars := by simpa using H.paramFVars }
  · rw [htake, List.map_append]
    simpa [hname] using H.consts.updatedStats (lctx := lctx)
      (resultLevel := resultLevel) (setResult := setResult)
      (nindices := nindices) (indName := indName)
  · rw [htake, List.map_append]
    simp [H.indices, hnindices]

theorem ValidAppStatsPrefix.complete
    (H : ValidAppStatsPrefix env Us Δ stats decl depth decl.types.length) :
    ValidAppStatsWF env Us Δ stats decl depth := by
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := ?_
    indices := ?_
    params := H.params
    paramFVars := H.paramFVars }
  · simpa using H.consts
  · simpa using H.indices

/-- The two independent invariants carried across the mutual-header loop.
`headers` follows the context used to check the current family header, while
`applicationStats` remains interpreted in the parameter context captured by
the first header.  Keeping the contexts separate reflects the executable
implementation: later family headers reuse the cached parameter free
variables without retaining their temporary index contexts. -/
structure HeaderTraversalCertificate (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (depth done : Nat) where
  headers : HeaderLoopCertificate env Us decl params stats done
  applicationStats : ValidAppStatsPrefix env Us Δ stats decl depth done

structure HeaderTraversalResult (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats) (depth : Nat) where
  headers : HeaderCertificate env decl
  applicationStats : ValidAppStatsWF env Us Δ stats decl depth

def HeaderTraversalResult.ofMaterialized
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    HeaderTraversalResult env Us Δ decl stats depth where
  headers := H.headers
  applicationStats := ValidAppStatsWF.ofMaterializedHeader H

/-- Executable header-loop state in the actual retained reader context. -/
structure HeaderRuntimeCertificate (Hc : ContextWF c)
    (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (depth done : Nat) where
  headers : HeaderLoopCertificate Hc.venv c.lparams decl params stats done
  applicationStats : ValidAppStatsPrefix Hc.venv c.lparams
    Hc.mlctx.vlctx stats decl depth done
  ambient : checkInductiveTypes.loopType.AmbientParamContext Hc params depth

def HeaderRuntimeCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth done)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    HeaderRuntimeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      decl params stats (depth + 1) done where
  headers := H.headers
  applicationStats := H.applicationStats.withLocalDecl Hc htr hty
  ambient := H.ambient.withIndex htr hty hsource

def HeaderRuntimeCertificate.first
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams indices.length)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : c.lparams.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[])
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (hofLevel : VLevel.ofLevel c.lparams resultSort = some target.resultLevel)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx)
    (hshape : decl.TypeShape Hc.venv params target) :
    HeaderRuntimeCertificate Hc decl params
      (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
        true nindices indName)
      indices.length 1 where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.first
    hindex htarget hofLevel hshape
  applicationStats :=
    (ValidAppStatsPrefix.beforeFirst Hcache hlevels huvars hconsts hindices).push
      hindex hname hnindices
  ambient :=
    checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq hctx

def HeaderRuntimeCertificate.later
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth done)
    (hindex : done < decl.types.length)
    (htarget : decl.types[done] = target)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort = some target.resultLevel)
    (hshape : decl.TypeShape Hc.venv params target) :
    HeaderRuntimeCertificate Hc decl params
      (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
        false nindices indName)
      depth (done + 1) where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.later
    H.headers hindex htarget hguard hofLevel hshape
  applicationStats := H.applicationStats.push hindex hname hnindices
  ambient := H.ambient

theorem HeaderRuntimeCertificate.firstResultWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams indices.length)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : c.lparams.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[])
    (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (params, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      HeaderRuntimeCertificate Hc decl params
        (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
          true nindices indName)
        indices.length 1 →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes 1
        (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
          true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes 1 stats k)
      type stats nindices c).WF Q := by
  apply checkInductiveTypes.loopInd.firstResult.refinesRuntimeState
    (dIdx := 0) k Q Hc hempty htype huvars hctxEq hheader hparamsTake
      hindicesTake hlevel
  intro resultSort hofLevel _hshape _hambient
  exact Hrec resultSort hofLevel
    (HeaderRuntimeCertificate.first Hcache hlevels huvars hconsts hindices
      hindex htarget hname hnindices hofLevel
      hctxEq _hshape)

theorem HeaderRuntimeCertificate.laterResultWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (H : HeaderRuntimeCertificate Hc decl params stats depth dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (hindex : dIdx < decl.types.length)
    (htarget : decl.types[dIdx] = target)
    (hname : indName = decl.types[dIdx].name)
    (hnindices : nindices = decl.types[dIdx].numIndices)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      HeaderRuntimeCertificate Hc decl params
        (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
          false nindices indName)
        depth (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
          false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply checkInductiveTypes.loopInd.laterResult.refines k Q Hc hnonempty
    htype huvars hctxEq hheader hparamsTake hindicesTake hparams hlevel
  intro resultSort hguard hofLevel hshape
  exact Hrec resultSort hguard hofLevel
    (H.later hindex htarget hname hnindices hguard hofLevel hshape)

def HeaderRuntimeCertificate.complete
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth
      decl.types.length) :
    HeaderTraversalResult Hc.venv c.lparams Hc.mlctx.vlctx
      decl stats depth where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.complete H.headers
  applicationStats := H.applicationStats.complete

/-- Pair the first successfully checked header with the corresponding first
statistics update.  The application-statistics premise is deliberately about
the post-telescope parameter context, which is exactly the context saved in
`stats.lctx` by the executable first-header branch. -/
def HeaderTraversalCertificate.first
    {c : AddInductive.Context}
    (Hstats : ValidAppStatsPrefix env c.lparams Δ stats decl depth 0)
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderTraversalCertificate env c.lparams Δ decl params
      (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
        true nindices indName)
      depth 1 where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.first
    hindex htarget hofLevel hshape
  applicationStats := Hstats.push hindex hname hnindices

/-- Extend both mutual-header invariants after a later header passes the
common-universe guard. -/
def HeaderTraversalCertificate.later
    {c : AddInductive.Context}
    (H : HeaderTraversalCertificate env c.lparams Δ decl params stats
      depth done)
    (hindex : done < decl.types.length)
    (htarget : decl.types[done] = target)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderTraversalCertificate env c.lparams Δ decl params
      (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
        false nindices indName)
      depth (done + 1) where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.later
    H.headers hindex htarget hguard hofLevel hshape
  applicationStats := H.applicationStats.push hindex hname hnindices

/-- At loop completion, expose exactly the two public certificates needed by
the constructor and formation stages. -/
def HeaderTraversalCertificate.complete
    (H : HeaderTraversalCertificate env Us Δ decl params stats depth
      decl.types.length) :
    HeaderTraversalResult env Us Δ decl stats depth where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.complete H.headers
  applicationStats := H.applicationStats.complete

/-- Joint output of header checking and the subsequent flattened constructor
traversal.  This is the formation-side payload eventually returned to
`Environment.addInductive`; application statistics remain available for
recursor and iota generation. -/
structure CheckedFormationResult (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (decl : VInductDecl) (stats : AddInductive.InductiveStats)
    (depth : Nat) where
  formation : FormationCertificate env decl
  applicationStats : ValidAppStatsWF env Us Δ stats decl depth

def HeaderTraversalResult.withConstructors
    (H : HeaderTraversalResult env Us Δ decl stats depth)
    (envTypes : VEnv)
    (htypes : env.addConsts decl.typeConstants = some envTypes)
    (Hctors : ConstructorPrefixCertificate env decl envTypes
      H.headers.params decl.ownedConstructors.length) :
    CheckedFormationResult env Us Δ decl stats depth where
  formation := {
    headers := H.headers
    envTypes := envTypes
    typesInstalled := htypes
    constructors := Hctors.complete }
  applicationStats := H.applicationStats

def HeaderTraversalResult.withConstructorTypes
    (H : HeaderTraversalResult env Us Δ decl stats depth)
    (envTypes : VEnv)
    (htypes : env.addConsts decl.typeConstants = some envTypes)
    (Hctors : ConstructorTypesPrefix envTypes decl H.headers.params
      decl.types.length) :
    CheckedFormationResult env Us Δ decl stats depth where
  formation := {
    headers := H.headers
    envTypes := envTypes
    typesInstalled := htypes
    constructors := Hctors.complete }
  applicationStats := H.applicationStats

def LiteralDisjoint (indConsts : Array Expr) : Prop :=
  ∀ literal : Literal,
    AddInductive.hasIndOcc indConsts literal.toConstructor = false

theorem forall₂_append {R : α → β → Prop}
    (H₁ : List.Forall₂ R as₁ bs₁) (H₂ : List.Forall₂ R as₂ bs₂) :
    List.Forall₂ R (as₁ ++ as₂) (bs₁ ++ bs₂) := by
  induction H₁ with
  | nil => exact H₂
  | cons h _ ih => exact .cons h ih

/-- Split the right-hand list at the boundary forced by an appended
left-hand list in a `Forall₂` derivation. -/
theorem List.Forall₂.split_left
    (H : List.Forall₂ R (as ++ bs) cs) :
    ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧
      List.Forall₂ R as cs₁ ∧ List.Forall₂ R bs cs₂ := by
  induction as generalizing cs with
  | nil => exact ⟨[], cs, by simp, .nil, H⟩
  | cons a as ih =>
      cases H with
      | cons hab htail =>
        rcases ih htail with ⟨cs₁, cs₂, rfl, hleft, hright⟩
        exact ⟨_ :: cs₁, cs₂, by simp, .cons hab hleft, hright⟩

/-- Exact inversion of a translated concrete application list.  Unlike the
typechecker-oriented `AppStack`, this retains the final abstract spine, which
is needed to split the field arguments and recursive results of an iota RHS. -/
theorem TrExprS.mkAppList_inv
    (H : TrExprS env Us Δ (Expr.mkAppList fn args) out) :
    ∃ fn' args',
      TrExprS env Us Δ fn fn' ∧
      List.Forall₂ (TrExprS env Us Δ) args args' ∧
      out = VExpr.mkApps fn' args' := by
  induction args generalizing fn out with
  | nil =>
      exact ⟨out, [], H, .nil, rfl⟩
  | cons arg args ih =>
      simp only [Expr.mkAppList] at H
      rcases ih H with ⟨app', args', happ, hargs, hout⟩
      cases happ with
      | app _ _ hfn harg =>
        refine ⟨_, _ :: args', hfn, .cons harg hargs, ?_⟩
        simpa [VExpr.mkApps] using hout

/-- Application-spine inversion with an exact split between two concrete
argument groups. -/
theorem TrExprS.mkAppList_append_inv
    (H : TrExprS env Us Δ (Expr.mkAppList fn (left ++ right)) out) :
    ∃ fn' left' right',
      TrExprS env Us Δ fn fn' ∧
      List.Forall₂ (TrExprS env Us Δ) left left' ∧
      List.Forall₂ (TrExprS env Us Δ) right right' ∧
      out = VExpr.mkApps fn' (left' ++ right') := by
  rcases TrExprS.mkAppList_inv H with
    ⟨fn', args', hfn, hargs, hout⟩
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.List.Forall₂.split_left
    hargs with
    ⟨left', right', rfl, hleft, hright⟩
  exact ⟨fn', left', right', hfn, hleft, hright, hout⟩

/-- Translation preserves a constant-headed application spine and the
left-to-right correspondence of all its arguments.  This is the syntax bridge
needed by both executable recursive-target checks. -/
theorem TrExprS.constAppSpine
    (H : TrExprS env Us Δ e e')
    (hhead : e.getAppFn = .const name levels) :
    ∃ levels' args',
      e'.getAppFnArgs = (.const name levels', args') ∧
      levels.mapM (VLevel.ofLevel Us) = some levels' ∧
      List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  induction e generalizing e' with
  | const _ _ =>
    cases H with
    | const _ hlevels _ =>
      cases hhead
      exact ⟨_, [], rfl, hlevels, .nil⟩
  | app fn arg ihFn _ =>
    cases H
    rename_i f' _ _ arg' _ _ hfn harg
    rcases ihFn hfn hhead with ⟨levels', args', hspine, hlevels, hargs⟩
    have hargs' := forall₂_append hargs (.cons harg .nil)
    refine ⟨levels', args' ++ [arg'], ?_, hlevels, ?_⟩
    · simp [hspine]
    · simpa only [Expr.getAppArgsList_app] using hargs'
  | bvar _ | fvar _ | sort _ | lit _ => cases hhead
  | mvar _ => cases H
  | lam _ _ _ _ _ _ => cases hhead
  | forallE _ _ _ _ _ _ => cases hhead
  | letE _ _ _ _ _ _ _ _ => cases hhead
  | mdata _ _ _ => cases hhead
  | proj _ _ _ _ => cases hhead

theorem TrExprS.eqv_fvar_target
    (H₁ : TrExprS env Us Δ (.fvar fv) e₁')
    (H₂ : TrExprS env Us Δ e₂ e₂')
    (heq : ((.fvar fv : Expr) == e₂) = true) : e₁' = e₂' := by
  cases e₂ <;> simp [(· == ·), Expr.eqv'] at heq
  have hfv : fv = _ := beq_iff_eq.mp heq
  subst_vars
  cases H₁ with
  | fvar h₁ =>
    cases H₂ with
    | fvar h₂ =>
      rw [h₁] at h₂
      cases h₂
      rfl

theorem isValidIndAppIdx.head
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    (type.getAppFn == stats.indConsts[i]!) = true := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.constHead
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels)) :
    type.getAppFn = .const name levels := by
  have hhead := isValidIndAppIdx.head hvalid
  have hget : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  rw [hget] at hhead
  exact Expr.eqv_const.mp hhead

theorem isValidIndAppIdx.arity
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    type.getAppArgs.size = stats.params.size + stats.nindices[i]! := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.param
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hj : j < stats.params.size) :
    (stats.params[j] == type.getAppArgs[j]'(by
      have := isValidIndAppIdx.arity hvalid
      omega)) = true := by
  have hp :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    cases hparams :
        (stats.params == type.getAppArgs.extract 0 stats.params.size) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  rw [Array.beq_eq_decide] at hp
  split at hp
  · rename_i hsize
    simp only [decide_eq_true_eq] at hp
    have helem := hp j hj
    simpa only [Array.getElem_extract, Nat.zero_add] using helem
  · simp_all

theorem isValidIndAppIdx.indexNoOccurrence
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hlower : stats.params.size ≤ j) (hupper : j < type.getAppArgs.size) :
    AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
  have hall :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    have harity := isValidIndAppIdx.arity hvalid
    rw [harity]
    cases hclean :
        (type.getAppArgs.extract stats.params.size
          (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  have hk : j - stats.params.size <
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).size := by
    simp only [Array.size_extract]
    omega
  have hclean := Array.all_eq_true.mp hall (j - stats.params.size) hk
  simp only [Array.getElem_extract] at hclean
  have hj : stats.params.size + (j - stats.params.size) = j := by omega
  simp only [hj] at hclean
  cases hocc : AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] <;>
    simp_all

theorem isValidIndAppFrom?_some
    (h : AddInductive.isValidIndAppFrom? stats type start fuel = some i) :
    start ≤ i ∧ i < start + fuel ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  induction fuel generalizing start with
  | zero => simp [AddInductive.isValidIndAppFrom?] at h
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?] at h
    by_cases hvalid : AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hvalid] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hvalid⟩
    · have hfalse : AddInductive.isValidIndAppIdx stats type start = false := by
        cases hv : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hvalid hv)
      simp [hfalse] at h
      rcases ih h with ⟨hlower, hupper, hvalid⟩
      exact ⟨by omega, by omega, hvalid⟩

theorem isValidIndApp?_some
    (h : AddInductive.isValidIndApp? stats type = some i) :
    i < stats.indConsts.size ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  exact ⟨by simpa using (isValidIndAppFrom?_some h).2.1,
    (isValidIndAppFrom?_some h).2.2⟩

/-- Once the preceding validation has identified a family member,
`getIIndices` returns that same member. This isolates the partial `get!` in
the production helper. -/
theorem getIIndices.fst_eq_of_valid
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 = i := by
  simp only [AddInductive.getIIndices, h, Option.get!_eq_getD,
    Option.getD_some]

/-- The suffix returned by `getIIndices` has the declared index arity of the
selected mutual-family member. -/
theorem getIIndices.index_arity
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size = stats.nindices[i]! := by
  rw [AddInductive.getIIndices]
  change (type.getAppArgs.toSubarray stats.params.size).toArray.size = _
  rw [Subarray.size_toArray, Subarray.size_eq]
  simp only [Array.stop_toSubarray, Array.start_toSubarray]
  have hvalid := (isValidIndApp?_some h).2
  have harity := isValidIndAppIdx.arity hvalid
  omega

theorem getIIndices.family_lt
    {decl : VInductDecl}
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 < decl.types.length := by
  rw [getIIndices.fst_eq_of_valid h]
  have hi := (isValidIndApp?_some h).1
  rw [H.consts.exact] at hi
  simpa using hi

/-- Together with the stats/declaration correspondence, the executable suffix
has the abstractly declared index arity. -/
theorem getIIndices.declared_index_arity
    {decl : VInductDecl}
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size =
      (decl.types[i]'(by simpa [getIIndices.fst_eq_of_valid h] using
        getIIndices.family_lt H h)).numIndices := by
  rw [getIIndices.index_arity h]
  have hi : i < decl.types.length := by
    simpa [getIIndices.fst_eq_of_valid h] using getIIndices.family_lt H h
  have hlen : stats.nindices.size = decl.types.length := by
    have := congrArg List.length H.indices
    simpa using this
  have hget := congrArg (fun xs => xs[i]?) H.indices
  simpa [Array.getElem!_eq_getD, hi, hlen] using hget

namespace mkRecRules.loopU

/-- The iota RHS generator produces exactly one recursive-result term for
each field selected by `loopCtorArgs`. The contents of each term are verified
separately; this theorem fixes the cardinality and continuation boundary. -/
theorem resultCount
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (hi : i ≤ u.size) (hv : v.size = i)
    (Hk : ∀ v c, v.size = u.size → (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hval :
        ((AddInductive.mkRecInfos.loopUArgs u[i] (fun uiTy xs =>
          let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
          let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
          let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
            motives) minors) itIndices
          return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)) c).WF
          (fun _ => True)) := by
      intro _ _
      trivial
    refine hval.bind fun val _ => ?_
    exact resultCount (indTypes := indTypes) (stats := stats)
      (motives := motives) (minors := minors) (lvls := lvls)
      (u := u) (i := i + 1) (v := v.push val) (k := k) (c := c)
      (by omega) (by simp [hv]) Hk
  · rw [dif_neg hnext]
    apply Hk
    omega
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.resultCountFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hk : ∀ v c, v.size = u.size → (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.resultCount (Nat.zero_le _) rfl Hk

namespace mkRecInfos.loopUArgs

/-- `loopUArgs` can only return through its continuation. This structural
interface lets rule generation retain the exposed recursive-field indices
without depending on typechecker correctness a second time. -/
private theorem loop_continueWith
    {α : Type} {Q : α → Prop}
    (k : Expr → Array Expr → AddInductive.M α)
    (Hk : ∀ uiTy xs c, (k uiTy xs c).WF Q) :
    ∀ fuel uiTy xs c,
      (AddInductive.mkRecInfos.loopUArgs.loop k uiTy xs fuel c).WF Q
  | 0, _, _, _ => Except.WF.throw
  | fuel + 1, uiTy, xs, c => by
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          dom.consumeTypeAnnotations bi }
      unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
        AddInductive.instMonadLocalNameGeneratorM
        AddInductive.instMonadWithReaderOfLocalContextM
      change ((monadLift (TypeChecker.whnf
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
          AddInductive.M Expr) c' >>= fun normalized =>
        AddInductive.mkRecInfos.loopUArgs.loop k normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) fuel c').WF Q
      have hwhnf :
          ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c').WF (fun _ => True) := by
        intro _ _
        trivial
      exact hwhnf.bind fun normalized _ =>
        loop_continueWith k Hk fuel normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) c'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change (k _ xs c).WF Q
      exact Hk _ _ _

theorem continueWith
    {α : Type} {Q : α → Prop}
    (ui : Expr) (k : Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ uiTy xs c, (k uiTy xs c).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs ui k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopUArgs
  have hinfer :
      ((monadLift (TypeChecker.inferType ui) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hinfer.bind fun inferred _ => ?_
  have hwhnf :
      ((monadLift (TypeChecker.whnf inferred) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hwhnf.bind fun normalized _ => ?_
  change (AddInductive.mkRecInfos.loopUArgs.loop k normalized #[]
    c.fuel.inductiveFuel c).WF Q
  exact loop_continueWith k Hk _ _ _ _

end mkRecInfos.loopUArgs

/-- Exact concrete syntax of one recursive call generated for an argument
selected by `loopCtorArgs`. -/
def GeneratedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (field value : Expr) : Prop :=
  ∃ (exposedType : Expr) (localArgs : Array Expr) (lctx : LocalContext),
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN
      (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices
    value = (lctx.mkLambda localArgs <|
      recursor.app (mkAppN field localArgs))

/-- Prefix invariant for `mkRecRules.loopU`: generated values correspond
pointwise to the selected recursive fields. -/
structure GeneratedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    GeneratedRecursiveCall indTypes stats motives minors lvls u[i]
      v[i]!

def GeneratedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) (u : Array Expr) :
    GeneratedRecursiveCalls indTypes stats motives minors lvls u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

def GeneratedRecursiveCalls.push
    (H : GeneratedRecursiveCalls indTypes stats motives minors lvls u v done)
    (hdone : done < u.size)
    (Hentry : GeneratedRecursiveCall indTypes stats motives minors lvls
      u[done] value) :
    GeneratedRecursiveCalls indTypes stats motives minors lvls u
      (v.push value) (done + 1) where
  covered := by omega
  size := by simp [H.size]
  entries i hi hiu := by
    by_cases h : i = done
    · subst i
      have hpush : done < (v.push value).size := by simp [H.size]
      have hbang : (v.push value)[done]! = value := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush]
        simpa [H.size] using (@Array.getElem_push_eq Expr v value)
      rw [hbang]
      exact Hentry
    · have hold : i < done := by omega
      have hv : i < v.size := by simpa [H.size] using hold
      have hpush : i < (v.push value).size := by
        simpa using Nat.lt_succ_of_lt hv
      have hbang : (v.push value)[i]! = v[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hv]
        exact Array.getElem_push_lt hv
      rw [hbang]
      exact H.entries i hold hiu

namespace mkRecRules.loopU

theorem generatedCalls
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hprefix : GeneratedRecursiveCalls indTypes stats motives minors lvls
      u v i)
    (Hk : ∀ v c,
      GeneratedRecursiveCalls indTypes stats motives minors lvls
        u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      fun uiTy xs => do
        let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
        let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
        let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
          motives) minors) itIndices
        return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => GeneratedRecursiveCall indTypes stats motives minors
            lvls u[i] value) := by
      apply mkRecInfos.loopUArgs.continueWith
      intro uiTy xs c'
      exact Except.WF.pure ⟨uiTy, xs, c'.lctx, rfl⟩
    · exact hval.bind fun value Hvalue =>
        generatedCalls
          (Hprefix.push hnext Hvalue) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.generatedCallsFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hk : ∀ v c,
      GeneratedRecursiveCalls indTypes stats motives minors lvls
        u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.generatedCalls
    (GeneratedRecursiveCalls.empty indTypes stats motives minors lvls u) Hk

/-- Exact source-level record emitted for one constructor by `mkRecRules`.
This certificate deliberately precedes translation to `VDefEq`: it fixes the
constructor, field count, minor ordinal, recursive-call array, and complete
right-hand side built by the executable traversal. -/
def GeneratedRecursorRule
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx : Nat) (rule : RecursorRule) : Prop :=
  ∃ (bu u v : Array Expr) (lctx : LocalContext),
    u.toList.Sublist bu.toList ∧
    GeneratedRecursiveCalls indTypes stats motives minors lvls
      u v u.size ∧
    rule.ctor = ctor.name ∧
    rule.nfields = bu.size ∧
    rule.rhs =
      (lctx.mkLambda stats.params <| lctx.mkLambda motives <|
       lctx.mkLambda minors <| lctx.mkLambda bu <|
       mkAppN (mkAppN minors[minorIdx]! bu) v)

/-- Ordered source-level coverage of the constructor suffix processed by the
named `mkRecRules.loopCtors` recursion. -/
inductive GeneratedRecursorRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : GeneratedRecursorRules indTypes stats motives minors lvls [] start []
  | cons :
      GeneratedRecursorRule indTypes stats motives minors lvls ctor start rule →
      GeneratedRecursorRules indTypes stats motives minors lvls
        ctors (start + 1) rules →
      GeneratedRecursorRules indTypes stats motives minors lvls
        (ctor :: ctors) start (rule :: rules)

theorem GeneratedRecursorRules.length
    (H : GeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) :
    rules.length = ctors.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Indexed form used by the flattened iota certificate: rule `i` belongs to
constructor `i` and its minor is the global starting ordinal plus `i`. -/
theorem GeneratedRecursorRules.entry
    (H : GeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      GeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) rules[i] := by
  induction H with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor start rule ctors rules Hrule Htail ih =>
      intro i hctor hrule
      cases i with
      | zero => simpa using Hrule
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        simpa only [List.getElem_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 i] using h

/-- A validated concrete parameter argument translates to the corresponding
abstract de Bruijn parameter.  The fvar-shape invariant is what upgrades
structural `Expr` equality to exact syntax translation here. -/
theorem ValidAppStatsWF.translatedParam
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlen := forall₂_length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlen, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := forall₂_get?_eq_some hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

/-- Absence of a newly declared constant is preserved by syntax translation.
Literal expansion and projection translation are explicit side conditions:
literals introduce old primitive constants, while `TrProj` is still an
independent typing boundary in the existing model. -/
theorem TrExprS.noFreshConsts
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e') :
    e'.containsAnyConst names = false := by
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | @const name _ _ _ _ hconst _ _ =>
    change names.contains name = false
    apply Bool.eq_false_iff.mpr
    intro hcontains
    have hmem : name ∈ names := by simpa using hcontains
    rw [hfresh name hmem] at hconst
    cases hconst
  | app _ _ _ _ ihFn ihArg =>
    exact Bool.or_eq_false_iff.mpr ⟨ihFn hctx, ihArg hctx⟩
  | lam _ _ _ ihTy ihBody =>
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx, ihBody ?_⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | forallE _ _ _ _ ihTy ihBody =>
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx, ihBody ?_⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    exact ihBody (hctx.cons (d := .vlet _ _) (ofv := none)
      (ihValue hctx))
  | lit _ _ ih => exact ih hctx
  | mdata _ ih => exact ih hctx
  | proj _ Hproj ih => exact hproj Hproj (ih hctx)

/-- Pointwise form of `TrExprS.noFreshConsts` for a translated application
spine. -/
theorem List.Forall₂.targets_noFreshConsts
    (H : List.Forall₂ (TrExprS env Us Δ) source target)
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false) :
    ∀ arg ∈ target, arg.containsAnyConst names = false := by
  induction H with
  | nil => simp
  | cons Hhead _ ih =>
    intro arg harg
    simp only [List.mem_cons] at harg
    rcases harg with rfl | harg
    · exact checkPositivityStep.TrExprS.noFreshConsts
        hfresh hctx hproj Hhead
    · exact ih arg harg

theorem TrExprS.noIndOcc
    (halign : IndConstNames indConsts names)
    (hlit : LiteralDisjoint indConsts)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e')
    (hno : AddInductive.hasIndOcc indConsts e = false) :
    e'.containsAnyConst names = false := by
  rw [hasIndOcc_eq_findAny] at hno
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | const _ _ _ =>
    simp only [Expr.findAny] at hno
    change names.contains _ = false
    rw [← halign]
    exact hno
  | app _ _ _ _ ihFn ihArg =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hfn, harg⟩
    exact Bool.or_eq_false_iff.mpr ⟨ihFn hctx hfn, ihArg hctx harg⟩
  | lam _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | forallE _ _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨htyValue, hbody⟩
    rcases Bool.or_eq_false_iff.mp htyValue with ⟨hty, hvalue⟩
    have hvalue' := ihValue hctx hvalue
    exact ihBody (hctx.cons (d := .vlet _ _) (ofv := none) hvalue') hbody
  | lit _ _ ih =>
    apply ih hctx
    rw [← hasIndOcc_eq_findAny]
    exact hlit _
  | mdata _ ih =>
    simpa only [Expr.findAny, Bool.false_or] using ih hctx hno
  | proj _ Hproj ih =>
    simp only [Expr.findAny, Bool.false_or] at hno
    exact hproj Hproj (ih hctx hno)

theorem ValidAppStatsWF.translatedIndexNoOccurrence
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].containsAnyConst (decl.types.map (·.name)) = false := by
  have hlen := forall₂_length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlen]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := forall₂_get?_eq_some hargs hsource htarget
  have hno := isValidIndAppIdx.indexNoOccurrence hvalid hlower hjArgs
  exact TrExprS.noIndOcc H.consts.names hlit hctx hproj harg hno

theorem isValidIndAppIdx.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (htarget : target = none ∨ target = some decl.types[typeIdx].name)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt target depth type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlen := List.mapM_some_length hlevels
    have hstats := H.levels
    omega
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := forall₂_length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalid hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, htarget,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalid hargs hlit hctx hproj
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

theorem isValidIndApp?.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt none depth type' := by
  rcases isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  exact isValidIndAppIdx.validIndAppAt H hi' htr hvalidIdx
    (Or.inl rfl) hlit hctx hproj

theorem noOccurrence.WF
    {type : Expr} {Q : Unit → Prop}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  simp [AddInductive.checkPositivityStep, hocc]
  change (Except.ok ()).WF Q
  exact Except.WF.pure hQ

/-- The successful fast path of executable positivity establishes the
declarative nonrecursive case.  All non-syntactic correspondence assumptions
are named at the boundary: the accumulated mutual constants, local-variable
translation, literal expansion, and projection translation. -/
theorem noOccurrence.refines
    {decl : VInductDecl} {type' : VExpr} {depth : Nat} {ctx : List VExpr}
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htr : TrExprS env Us Δ type type')
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact noOccurrence.WF
    (Q := fun _ => decl.SyntacticallyPositive env ctx depth type')
    hocc (.nonrecursive <|
      checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit hctx hproj htr hocc)

theorem validApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals exact Except.WF.pure hQ

/-- Once the application-spine refinement supplies `ValidIndAppAt`, the final
executable success branch is exactly the declarative recursive positivity
constructor. -/
theorem validApplication.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hrefines : decl.ValidIndAppAt none depth type') :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact validApplication.WF hocc hforall hvalid (.recursive hrefines)

theorem validApplication.sourceRefines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  apply validApplication.refines hocc hforall hvalid
  exact isValidIndApp?.validIndAppAt Hstats htr hvalid hlit hctx hproj

theorem invalidApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = none) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

theorem negativeDomain.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_pos hdomOcc]
  change (Except.error _).WF Q
  exact Except.WF.throw

/-- Positive higher-order branch after WHNF.  Source-domain annotation
transport is shared with header and constructor telescopes. -/
theorem forallE.sourceWF
    (Hc : ContextWF c)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_neg (by simp [hdomOcc])]
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => recur (body.instantiate1 arg))
    Hc Hdom.consumed Hdom.isType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    Hdom.consumed Hdom.isType hbody''
  exact Hrec body'' hbodyEq hopened

/-- The successful higher-order branch refines the declarative `forallE`
positivity rule.  The recursive checker runs in the consumed-annotation local
context, while its certificate is deliberately stated for the original
source-domain/body translation used by the independent specification. -/
theorem forallE.refines
    {decl : VInductDecl} {depth : Nat}
    (Hc : ContextWF c)
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (huvars : c.lparams.length = decl.uvars)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
        (fun _ => decl.Positive Hc.venv
          (consumedDom' :: Hc.mlctx.vlctx.toCtx) (depth + 1) body'')) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx depth
        (.forallE sourceDom' sourceBody')) := by
  have hdomNo := checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit
    hctx hproj Hdom.source hdomOcc
  refine forallE.sourceWF (Q := fun _ => decl.SyntacticallyPositive Hc.venv
      Hc.mlctx.vlctx.toCtx depth (.forallE sourceDom' sourceBody'))
      (recur := recur) (ctor := ctor)
      (idx := idx) Hc hocc hdomOcc Hdom hbody ?_
  intro body'' hbodyEq hopened
  exact (Hrec body'' hbodyEq hopened).mono fun _ hpositive => by
    rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
    rcases hbodyEq with ⟨bodyType, hbodyEq⟩
    exact .forallE hdomNo
      (by simpa [huvars] using hdomEq)
      (by simpa [huvars] using hbodyEq) hpositive

end checkPositivityStep

namespace checkConstructors.loopCtor

/-- The terminal constructor target check now discharges the declarative
`CtorTailWF.result` rule, rather than returning an unconstrained success. -/
theorem result.refines
    {decl : VInductDecl} {depth : Nat} {result type' exprType : VExpr}
    {ctorCtx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hdefeq : env.IsDefEq decl.uvars ctorCtx result type' exprType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF env decl.types[targetIdx]
        ctorCtx depth result) := by
  exact checkConstructors.loopCtor.result.WF
    (Q := fun _ => decl.CtorTailWF env decl.types[targetIdx]
      ctorCtx depth result)
    hforall hvalid (.result
      (checkPositivityStep.isValidIndAppIdx.validIndAppAt
        Hstats hi htr hvalid (Or.inr rfl) hlit hctx hproj)
      hdefeq)

/-- Semantic wrapper for a safe constructor field.  The low-level traversal
supplies source typing and annotation transport; this theorem packages those
facts as the declarative `CtorTailWF.field` rule. -/
theorem safeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF
      (fun _ => decl.Positive Hc.venv ctorCtx depth sourceDom'))
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.Positive Hc.venv ctorCtx depth sourceDom' →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine safeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (Pos := decl.Positive Hc.venv ctorCtx depth sourceDom')
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody Hpos ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    hpositive body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound hpositive body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inr hpositive)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

theorem unsafeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (hunsafe : decl.isUnsafe = true)
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine unsafeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inl hunsafe)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

/-- Starting after the common constructor parameters, the complete executable
constructor-tail traversal builds `CtorTailWF`.  The remaining level-order
premise is isolated explicitly until `Level.geq` is connected to `VLevel.LE`. -/
theorem tailRefines
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hpositivity : ∀ {c : AddInductive.Context} {depth posIdx : Nat}
      {type : Expr} {type' : VExpr} (Hc : ContextWF c),
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
        Hc.mlctx.vlctx stats decl depth →
      checkPositivityStep.VLCtx.NoIndConsts
        (decl.types.map (·.name)) Hc.mlctx.vlctx →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type' →
      (AddInductive.checkPositivity stats type ctor posIdx c).WF
        (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type'))
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  induction fuel generalizing c type type' depth i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htr with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        have hparamNext : stats.params[i + 1]? = none := by
          rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
          omega
        cases isUnsafe with
        | false =>
          have Hpos := hpositivity (posIdx := i) Hc Hstats hctx
            (hdom.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
          exact safeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            Hpos hbound fun _ _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
        | true =>
          exact unsafeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            (hunsafe rfl) hbound fun _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact invalidResult.WF hforall hvalid
      · rcases htr.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf with
          ⟨exprType, htype⟩
        subst target
        exact result.refines Hstats hi htr hforall hvalid hlit hctx hproj
          (by simpa [Hstats.uvars] using htype)

end checkConstructors.loopCtor

namespace checkPositivity.loop

theorem zero.WF :
    (AddInductive.checkPositivity.loop stats ctor idx type 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkPositivity.loop] at h

theorem succ.WF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.WF Hc htype).bind fun normalized hnormalized =>
    Hstep normalized hnormalized

/-- Positivity's WHNF step with the concrete free-variable preservation fact
retained for refinements whose semantic scope is narrower than the executable
local context. -/
theorem succ.scopeWF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.scopeWF Hc htype).bind
    fun normalized hnormalized => Hstep normalized hnormalized.1 hnormalized.2

/-- The complete recursive positivity traversal refines the independent
declarative judgment.  In particular, every recursive call under a higher-
order binder performs and records its own WHNF/definitional-equality step. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    refine succ.WF Hc hsource ?_
    intro normalized hnormalized
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx
              depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using hsourceExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit hctx hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        exact finish <| checkPositivityStep.forallE.refines Hc Hstats.consts
          hlit hctx hproj hocc' hdomOcc' Hdom Hstats.uvars hbody
          fun body'' hbodyEq hopened => by
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
              Hc Hdom.consumed Hdom.isType
            have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
              apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
              rfl
            exact ih Hc' Hstats' hctx'
              (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
    ·
      cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit hctx hproj hocc' hforall hvalid

/-- Positivity refinement for constructor checking after mutual headers have
left ambient declarations in the executable context.  The concrete checker
runs in `Hc.mlctx.vlctx`, while every declarative judgment is constructed in
the independent `scope`; runtime WHNF results are restricted before any
positivity rule is emitted. -/
theorem refinesNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htypeFull with ⟨sourceFull, hsourceFull, hsourceTarget⟩
    refine succ.scopeWF Hc hsourceFull ?_
    intro normalized hbelow hnormalized
    have hnormalizedFVars : FVarsIn (· ∈ scope.fvars) normalized :=
      hbelow _ Hruntime.upset htypeNarrow.fvarsIn
    rcases hnormalized with
      ⟨exposedFull, hexposedFull, hexposedTarget⟩
    have hnormalizedClosed : Closed normalized 0 := by
      have hclosed := hexposedFull.closed
      rw [Hc.mlctx.noBV] at hclosed
      exact hclosed
    have hnormalizedFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
        normalized fullType :=
      ⟨exposedFull, hexposedFull,
        hexposedTarget.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
          hsourceTarget⟩
    have hinputFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
        type fullType :=
      ⟨sourceFull, hsourceFull, hsourceTarget⟩
    rcases Hruntime.restrictTrExpr Hc.checking.tr.wf htypeNarrow
        hinputFull hnormalizedFull hnormalizedClosed hnormalizedFVars with
      ⟨exposed, hexposed, hexposedEq⟩
    rcases hexposedEq.symm with ⟨exprType, htypeExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv scope.toCtx depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv scope.toCtx depth narrowType) :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using htypeExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit
        (Hruntime.noIndConsts (decl.types.map (·.name))) hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hexposedFull with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          refine finish <| checkPositivityStep.forallE.sourceWF
            (Q := fun _ => decl.SyntacticallyPositive Hc.venv
              scope.toCtx depth (.forallE _ _))
            (recur := fun body =>
              AddInductive.checkPositivity.loop stats ctor idx body fuel)
            Hc hocc' hdomOcc' Hdom hbodyFull ?_
          intro bodyFull' _hbodyFullEq hopenedFull
          let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn hnormalizedFVars.1)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.NarrowRuntimeScope
                Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
          have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam narrowDom) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
          have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
          have Hrec := ih Hc' Hruntime' Hstats' hopenedNarrow
            (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          exact Hrec.mono fun _ hpositive => by
            rcases hdomNarrowType with ⟨domLevel, hdomTyped⟩
            rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
            change Hc.venv.IsDefEq c.lparams.length scope.toCtx
              narrowDom narrowDom (.sort domLevel) at hdomTyped
            change Hc.venv.IsDefEq c.lparams.length
              (narrowDom :: scope.toCtx) narrowBody narrowBody
              (.sort bodyLevel) at hbodyTyped
            exact .forallE
              (checkPositivityStep.TrExprS.noIndOcc Hstats.consts.names
                hlit (Hruntime.noIndConsts (decl.types.map (·.name)))
                hproj hdomNarrow hdomOcc')
              (by simpa [Hstats.uvars] using hdomTyped)
              (by simpa [Hstats.uvars] using hbodyTyped)
              hpositive
    · cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit
            (Hruntime.noIndConsts (decl.types.map (·.name)))
            hproj hocc' hforall hvalid

end checkPositivity.loop

theorem checkPositivity.WF
    (Hloop : (AddInductive.checkPositivity.loop stats ctor idx type
      c.fuel.inductiveFuel c).WF Q) :
    (AddInductive.checkPositivity stats type ctor idx c).WF Q := by
  unfold AddInductive.checkPositivity
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact Hloop

/-- Public positivity refinement, including the production fuel lookup. -/
theorem checkPositivity.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refines Hc Hstats hconsume hlit hctx hproj htype

/-- Public narrow-scope positivity refinement, including the production fuel
lookup used by constructor checking. -/
theorem checkPositivity.refinesNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refinesNarrow Hc Hruntime Hstats hconsume
    hlit hproj htypeNarrow htypeFull

namespace isRecArg.loop

/-- The recursive-argument classifier used by recursor generation refines the
independent `RecursiveArg` judgment whenever it returns a family index. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.isRecArg.loop stats type fuel c).WF
      (fun result => ∀ target, result = some target →
        target < decl.types.length ∧
        decl.RecursiveArg Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero =>
    intro _ h
    simp [AddInductive.isRecArg.loop] at h
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    rw [AddInductive.isRecArg.loop]
    refine (whnfInContext.WF Hc hsource).bind fun normalized hnormalized => ?_
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
        refine withLocalDecl.WF (name := name) (bi := bi)
          (Q := fun result => ∀ target, result = some target →
            target < decl.types.length ∧
            decl.RecursiveArg Hc.venv Hc.mlctx.vlctx.toCtx depth type')
          Hc Hdom.consumed Hdom.isType ?_
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hopened := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.consumed Hdom.isType hbody''
        have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
          Hc Hdom.consumed Hdom.isType
        have hctx' : checkPositivityStep.VLCtx.NoIndConsts
            (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
          apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
          rfl
        have Hrec := ih Hc' Hstats' hctx'
          (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
        exact Hrec.mono fun result hrec target htarget => by
          rcases hrec target htarget with ⟨htarget, hrecursive⟩
          rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
          rcases hbodyEq with ⟨bodyType, hbodyEq⟩
          exact ⟨htarget, .forallE
            (by simpa [Hstats.uvars] using hsourceExposed)
            (by simpa [Hstats.uvars] using hdomEq)
            (by simpa [Hstats.uvars] using hbodyEq)
            hrecursive⟩
    · cases normalized <;> try { simp at hforall }
      all_goals
        change (Except.ok (AddInductive.isValidIndApp? stats _)).WF _
        exact Except.WF.pure fun target hvalid => by
          rcases checkPositivityStep.isValidIndApp?_some hvalid with
            ⟨htargetLt, _⟩
          refine ⟨?_, .direct
            (by simpa [Hstats.uvars] using hsourceExposed)
            (checkPositivityStep.isValidIndApp?.validIndAppAt Hstats hexposed
              hvalid hlit hctx hproj)⟩
          rw [← Hstats.types_size]
          exact htargetLt

end isRecArg.loop

theorem isRecArg.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.isRecArg stats type c).WF
      (fun result => ∀ target, result = some target →
        target < decl.types.length ∧
        decl.RecursiveArg Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  unfold AddInductive.isRecArg
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF
      (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact isRecArg.loop.refines Hc Hstats hconsume hlit hctx hproj htype

namespace mkRecInfos.loopCtorArgs.loop

/-- Independently of typing, the recursive-argument array accumulated by
recursor generation is an ordered sublist of the complete field array. This
is the executable source of `IotaRule.fieldPositions_ordered`. -/
theorem selectedSublist {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : α → Prop}
    (hselected : u.toList.Sublist bu.toList)
    (Hk : ∀ t bu u c, u.toList.Sublist bu.toList → (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      cases hparam : stats.params[i]? with
      | some param =>
        change (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
          (body.instantiate1 param) (i + 1) bu u fuel c).WF Q
        exact ih hselected
      | none =>
        change (Lean4Lean.withLocalDecl name bi dom.consumeTypeAnnotations
          (fun arg => do
            let bu := bu.push arg
            let u := if (← AddInductive.isRecArg stats dom).isSome then
              u.push arg else u
            AddInductive.mkRecInfos.loopCtorArgs.loop stats k
              (body.instantiate1 arg) (i + 1) bu u fuel) c).WF Q
        unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
          AddInductive.instMonadLocalNameGeneratorM
          AddInductive.instMonadWithReaderOfLocalContextM
        let c' : AddInductive.Context := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }
        change (AddInductive.isRecArg stats dom c' >>= fun selected =>
          AddInductive.mkRecInfos.loopCtorArgs.loop stats
            k (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            (bu.push (.fvar ⟨c.ngen.curr⟩))
            (if selected.isSome then u.push (.fvar ⟨c.ngen.curr⟩) else u)
            fuel c') |>.WF Q
        have hclass : (AddInductive.isRecArg stats dom c').WF (fun _ => True) := by
          intro _ _
          trivial
        refine hclass.bind fun selected _ => ?_
        cases selected with
        | none =>
          apply ih
          simpa using hselected.trans
            (List.sublist_append_left bu.toList [.fvar ⟨c.ngen.curr⟩])
        | some target =>
          apply ih
          simpa using hselected.append_right [.fvar ⟨c.ngen.curr⟩]
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      change (k _ bu u c).WF Q
      exact Hk _ _ _ _ hselected

end mkRecInfos.loopCtorArgs.loop

/-- Public structural invariant for constructor argument classification. -/
theorem mkRecInfos.loopCtorArgs.selectedSublist {α : Type}
    (stats : AddInductive.InductiveStats) (t : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context) {Q : α → Prop}
    (Hk : ∀ t bu u c, u.toList.Sublist bu.toList → (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopCtorArgs
  exact mkRecInfos.loopCtorArgs.loop.selectedSublist stats k .slnil Hk

namespace mkRecRules.loopCtors

/-- The complete named constructor recursion emits one exact source rule per
input constructor, preserves order, and advances the flattened minor ordinal
once per rule. -/
theorem generatedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule)
    (start : Nat) (c : AddInductive.Context) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          checkPositivityStep.GeneratedRecursorRules indTypes stats motives minors lvls
            ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start c with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      refine ⟨[], ?_, .nil, by simp⟩
      simp
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecRules.loopCtors]
      have hone :
          ((fun minorIdx => AddInductive.mkRecInfos.loopCtorArgs stats
            ctor.type fun _ bu u =>
              AddInductive.mkRecRules.loopU indTypes stats motives minors
                lvls u 0 #[] fun v => do
                  let lctx ← getLCtx
                  let rule := {
                    ctor := ctor.name
                    nfields := bu.size
                    rhs := lctx.mkLambda stats.params <|
                      lctx.mkLambda motives <| lctx.mkLambda minors <|
                      lctx.mkLambda bu <|
                      mkAppN (mkAppN minors[minorIdx]! bu) v }
                  return (rule, minorIdx + 1)) start c).WF fun out =>
            checkPositivityStep.GeneratedRecursorRule indTypes stats motives minors lvls
              ctor start out.1 ∧ out.2 = start + 1 := by
        apply mkRecInfos.loopCtorArgs.selectedSublist stats
        intro _ bu u c' hselected
        apply checkPositivityStep.mkRecRules.loopU.generatedCallsFromEmpty
        intro v c'' Hcalls
        exact Except.WF.pure ⟨⟨bu, u, v, c''.lctx, hselected,
          Hcalls, rfl, rfl, rfl⟩, rfl⟩
      exact hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, hnext⟩
        have htail := ih (acc := acc.push out.1)
          (start := out.2) (c := c)
        exact htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, .cons Hrule ?_, ?_⟩
          · simpa [hout]
          · simpa [hnext] using Hgenerated
          · simp at hend ⊢
            omega

end mkRecRules.loopCtors

/-- Public rule-generator boundary: starting with an empty accumulator returns
exactly the ordered rules certified for the selected mutual-family member. -/
theorem mkRecRules.generatedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    (c : AddInductive.Context) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        checkPositivityStep.GeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.generatedRules indTypes stats motives minors
    (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start c
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- Bridge from one verified executable family batch to the flattened
abstract iota accumulator. All traversal and indexing facts are discharged
here; the sole pointwise premise is the semantic translation of each exact
generated source rule into the independent `IotaRule` judgment. -/
theorem IotaBuildCertificate.appendGeneratedRules
    (Hbuild : IotaBuildCertificate env decl block prior)
    (Hgenerated : checkPositivityStep.GeneratedRecursorRules
      indTypes stats motives minors lvls ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (hsemantic : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length),
      checkPositivityStep.GeneratedRecursorRule indTypes stats motives minors
        lvls ctors[i] (start + i) sourceRules[i] →
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i])) :
    IotaBuildCertificate env decl block (prior ++ abstractRules) := by
  apply Hbuild.append hroom
  intro i habstract
  have hsource : i < sourceRules.length := by omega
  have hctor : i < ctors.length := by
    rw [← Hgenerated.length]
    exact hsource
  exact hsemantic i hctor hsource habstract
    (Hgenerated.entry i hctor hsource)

/-- Proof-side metadata retained for every field selected by `isRecArg`.
The executable code stores only the field free variable; this record retains
the independent recursive-domain certificate needed by `IotaRule`. -/
structure RecursorRecursiveDomain (env : VEnv) (decl : VInductDecl) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArg env ctx depth domain

/-- Exact correspondence between the two arrays built by `loopCtorArgs` and
the proof-side recursive-domain certificates. Constructors preserve the
left-to-right field order and record the field ordinal at selection time. -/
inductive RecursorFieldSelections (env : VEnv) (decl : VInductDecl) :
    Array Expr → Array Expr → List (RecursorRecursiveDomain env decl) → Prop
  | nil : RecursorFieldSelections env decl #[] #[] []
  | nonrecursive : RecursorFieldSelections env decl bu u fields →
      RecursorFieldSelections env decl (bu.push arg) u fields
  | recursive : RecursorFieldSelections env decl bu u fields →
      cert.fieldIndex = bu.size →
      RecursorFieldSelections env decl (bu.push arg) (u.push arg)
        (fields ++ [cert])

theorem RecursorFieldSelections.map
    (H : RecursorFieldSelections env decl bu u fields)
    (f : Expr → Expr) :
    RecursorFieldSelections env decl (bu.map f) (u.map f) fields := by
  induction H with
  | nil =>
    rw [Array.map_empty]
    exact .nil
  | @nonrecursive bu u fields arg _ ih =>
    rw [Array.map_push]
    exact RecursorFieldSelections.nonrecursive (arg := f arg) ih
  | @recursive bu u fields arg cert _ hindex ih =>
    rw [Array.map_push, Array.map_push]
    apply RecursorFieldSelections.recursive (arg := f arg) (cert := cert) ih
    simpa using hindex

theorem RecursorFieldSelections.selectedSublist
    (H : RecursorFieldSelections env decl bu u fields) :
    u.toList.Sublist bu.toList := by
  induction H with
  | nil => exact .slnil
  | nonrecursive _ ih =>
    simpa using ih.trans (List.sublist_append_left _ [_])
  | @recursive bu u fields arg cert _ _ ih =>
    simpa using ih.append_right [arg]

theorem RecursorFieldSelections.fields_length
    (H : RecursorFieldSelections env decl bu u fields) :
    fields.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursorFieldSelections.positions_lt
    (H : RecursorFieldSelections env decl bu u fields) :
    ∀ cert ∈ fields, cert.fieldIndex < bu.size := by
  induction H with
  | nil => simp
  | @nonrecursive bu u fields arg _ ih =>
    intro cert hmem
    have := ih cert hmem
    simp only [Array.size_push]
    omega
  | @recursive bu u fields arg cert _ hindex ih =>
    intro old hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · have := ih old hmem
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push, hindex]
      omega

theorem RecursorFieldSelections.positions_ordered
    (H : RecursorFieldSelections env decl bu u fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  induction H with
  | nil => simp
  | nonrecursive _ ih => exact ih
  | @recursive bu u fields arg cert H hindex ih =>
    simp only [List.map_append, List.map_singleton]
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro old hold _ hnew
    simp only [List.mem_singleton] at hnew
    subst hnew
    rw [hindex]
    rcases List.mem_map.mp hold with ⟨oldCert, hmem, rfl⟩
    exact H.positions_lt oldCert hmem

/-- The selected recursive array and its proof-side certificates remain
pointwise aligned with the final all-fields array. In particular, the
recorded field ordinal selects the very concrete argument paired with that
certificate, even after later fields extend `bu`. -/
theorem RecursorFieldSelections.arguments_at_positions
    (H : RecursorFieldSelections env decl bu u fields) :
    List.Forall₂ (fun cert arg =>
      ∃ h : cert.fieldIndex < bu.size, arg = bu[cert.fieldIndex]'h)
      fields u.toList := by
  induction H with
  | nil => exact .nil
  | @nonrecursive bu u fields arg H ih =>
      have lift : List.Forall₂ (fun cert selected =>
          ∃ h : cert.fieldIndex < (bu.push arg).size,
            selected = (bu.push arg)[cert.fieldIndex]'h)
          fields u.toList := by
        apply List.Forall₂.imp (R := fun cert selected =>
          ∃ h : cert.fieldIndex < bu.size,
            selected = bu[cert.fieldIndex]'h) (fun cert selected hhead => ?_) ih
        rcases hhead with ⟨hpos, heq⟩
        refine ⟨by simp; omega, ?_⟩
        rw [heq]
        exact (Array.getElem_push_lt hpos).symm
      exact lift
  | @recursive bu u fields arg cert H hindex ih =>
      have lift : List.Forall₂ (fun old selected =>
          ∃ h : old.fieldIndex < (bu.push arg).size,
            selected = (bu.push arg)[old.fieldIndex]'h)
          fields u.toList := by
        apply List.Forall₂.imp (R := fun old selected =>
          ∃ h : old.fieldIndex < bu.size,
            selected = bu[old.fieldIndex]'h) (fun old selected hhead => ?_) ih
        rcases hhead with ⟨hpos, heq⟩
        refine ⟨by simp; omega, ?_⟩
        rw [heq]
        exact (Array.getElem_push_lt hpos).symm
      rw [Array.toList_push]
      apply checkPositivityStep.forall₂_append lift
      apply List.Forall₂.cons
      · refine ⟨by simp [hindex], ?_⟩
        simpa [hindex] using (@Array.getElem_push_eq Expr bu arg).symm
      · exact .nil

/-- Translation preserves the selector's ordered-sublist invariant. The only
potential ambiguity is translating the same selected source field along the
`bu` and `u` arrays; `IsUnique` resolves exactly that equality. -/
theorem RecursorFieldSelections.translatedSublist
    (H : RecursorFieldSelections semanticEnv decl bu u fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList allArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    recursiveArgs.Sublist allArgs := by
  induction H generalizing allArgs recursiveArgs with
  | nil =>
      cases Hbu
      cases Hu
      exact .slnil
  | @nonrecursive bu u fields arg H ih =>
      rw [Array.toList_push] at Hbu
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hbu with
        ⟨allPrefix, translatedArg, rfl,
        HbuPrefix, _⟩
      have Hsub := ih HbuPrefix Hu Hunique
      exact Hsub.trans (List.sublist_append_left allPrefix [translatedArg])
  | @recursive bu u fields arg cert H hindex ih =>
      rw [Array.toList_push] at Hbu Hu
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hbu with
        ⟨allPrefix, translatedArg, rfl,
        HbuPrefix, HargAll⟩
      rcases Lean4Lean.VerifyInductive.List.Forall₂.unsnoc Hu with
        ⟨recursivePrefix, recursiveArg, rfl,
        HuPrefix, HargRec⟩
      have HuniquePrefix : ∀ old ∈ u.toList,
          TrExprS.IsUnique old := by
        intro old hold
        exact Hunique old (by simp [hold])
      have Hsub := ih HbuPrefix HuPrefix HuniquePrefix
      have hargUnique : TrExprS.IsUnique arg :=
        Hunique arg (by simp)
      have heq : recursiveArg = translatedArg :=
        TrExprS.unique hargUnique HargRec HargAll
      subst recursiveArg
      exact Hsub.append_right [translatedArg]

def RecursorRecursiveDomain.toRecursiveField
    (cert : RecursorRecursiveDomain env decl) (arg : VExpr) :
    decl.RecursiveField env where
  fieldIndex := cert.fieldIndex
  arg := arg
  ctx := cert.ctx
  depth := cert.depth
  domain := cert.domain
  recursive := cert.recursive

/-- Zips the proof-side domain certificates with their final translated field
arguments to obtain the public `RecursiveField` witnesses used by iota rules. -/
inductive RecursorFieldsMaterialize (env : VEnv) (decl : VInductDecl) :
    List (RecursorRecursiveDomain env decl) → List VExpr →
      List (decl.RecursiveField env) → Prop
  | nil : RecursorFieldsMaterialize env decl [] [] []
  | cons : RecursorFieldsMaterialize env decl certs args fields →
      RecursorFieldsMaterialize env decl (cert :: certs) (arg :: args)
        (cert.toRecursiveField arg :: fields)

theorem RecursorFieldsMaterialize.exists_of_length
    (h : certs.length = args.length) :
    ∃ fields, RecursorFieldsMaterialize env decl certs args fields := by
  induction certs generalizing args with
  | nil =>
    cases args <;> simp_all
    exact ⟨[], .nil⟩
  | cons cert certs ih =>
    cases args with
    | nil => simp at h
    | cons arg args =>
      have h' : certs.length = args.length := by
        simpa using Nat.succ.inj h
      rcases ih h' with ⟨fields, hfields⟩
      exact ⟨_, .cons hfields⟩

theorem RecursorFieldsMaterialize.args
    {env : VEnv} {decl : VInductDecl}
    {certs : List (RecursorRecursiveDomain env decl)}
    {translated : List VExpr} {fields : List (decl.RecursiveField env)}
    (H : RecursorFieldsMaterialize env decl certs translated fields) :
    fields.map (·.arg) = translated := by
  induction H with
  | nil => rfl
  | cons _ ih => simp [RecursorRecursiveDomain.toRecursiveField, ih]

theorem RecursorFieldsMaterialize.positions
    {env : VEnv} {decl : VInductDecl}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (H : RecursorFieldsMaterialize env decl certs translated fields) :
    fields.map (·.fieldIndex) = certs.map (·.fieldIndex) := by
  induction H with
  | nil => rfl
  | cons _ ih => simp [RecursorRecursiveDomain.toRecursiveField, ih]

theorem RecursorFieldSelections.exists_materialization
    (H : RecursorFieldSelections env decl bu u certs)
    (hargs : List.Forall₂ R u.toList args) :
    ∃ fields, RecursorFieldsMaterialize env decl certs args fields := by
  apply RecursorFieldsMaterialize.exists_of_length
  rw [H.fields_length]
  have hlen := checkPositivityStep.forall₂_length_eq hargs
  simpa using hlen

theorem RecursorFieldsMaterialize.positions_ordered
    {env : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (Hsel : RecursorFieldSelections env decl bu u certs)
    (Hmat : RecursorFieldsMaterialize env decl certs translated fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  rw [Hmat.positions]
  exact Hsel.positions_ordered

theorem RecursorFieldsMaterialize.positions_lt
    {env : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (Hsel : RecursorFieldSelections env decl bu u certs)
    (Hmat : RecursorFieldsMaterialize env decl certs translated fields) :
    ∀ field ∈ fields, field.fieldIndex < bu.size := by
  intro field hmem
  have hpos : field.fieldIndex ∈ fields.map (·.fieldIndex) := by
    exact List.mem_map.mpr ⟨field, hmem, rfl⟩
  rw [Hmat.positions] at hpos
  rcases List.mem_map.mp hpos with ⟨cert, hcert, heq⟩
  rw [← heq]
  exact Hsel.positions_lt cert hcert

/-- Materialized recursive fields select the corresponding translated
constructor argument at their certified ordinal. This discharges the
`IotaRule.fields_at_positions` obligation from the executable selection
trace; uniqueness is needed only for the selected source field expression. -/
theorem RecursorFieldsMaterialize.fields_at_positions
    {semanticEnv trEnv : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain semanticEnv decl)}
    {recursiveArgs allArgs : List VExpr}
    {fields : List (decl.RecursiveField semanticEnv)}
    (Hsel : RecursorFieldSelections semanticEnv decl bu u certs)
    (Hmat : RecursorFieldsMaterialize semanticEnv decl certs recursiveArgs fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList allArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    ∀ field ∈ fields,
      ∃ h : field.fieldIndex < allArgs.length,
        field.arg = allArgs[field.fieldIndex]'h := by
  intro field hfield
  rcases List.mem_iff_getElem.mp hfield with ⟨j, hj, rfl⟩
  have hfieldsArgs : fields.length = recursiveArgs.length := by
    have := congrArg List.length Hmat.args
    simpa using this
  have hcertFields : certs.length = fields.length := by
    have := congrArg List.length Hmat.positions
    simpa using this.symm
  have hjCert : j < certs.length := by omega
  have hjRec : j < recursiveArgs.length := by omega
  have hjU : j < u.toList.length := by
    simpa only [Array.length_toList, ← Hsel.fields_length, hcertFields] using hj
  have Halign := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hsel.arguments_at_positions j hjCert hjU
  rcases Halign with ⟨hpos, hsource⟩
  have hposAll : certs[j].fieldIndex < allArgs.length := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hbu
    have hp : certs[j].fieldIndex < bu.toList.length := by
      simpa using hpos
    omega
  have hposEq : fields[j].fieldIndex = certs[j].fieldIndex := by
    have h := congrArg (fun xs => xs[j]?) Hmat.positions
    simpa [hj, hjCert] using h
  have hargEq : fields[j].arg = recursiveArgs[j] := by
    have h := congrArg (fun xs => xs[j]?) Hmat.args
    simpa [hj, hjRec] using h
  refine ⟨hposEq.symm ▸ hposAll, ?_⟩
  rw [hargEq]
  have Hrec := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hu j hjU hjRec
  have Hfield := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hbu certs[j].fieldIndex (by simpa using hpos) hposAll
  have hsourceList : u.toList[j] = bu.toList[certs[j].fieldIndex] := by
    simpa using hsource
  have Hfield' : TrExprS trEnv Us Δ u.toList[j]
      allArgs[certs[j].fieldIndex] := by
    rw [hsourceList]
    exact Hfield
  have heq := TrExprS.unique (Hunique u.toList[j]
    (List.getElem_mem hjU)) Hrec Hfield'
  simpa [hposEq] using heq

theorem RecursorFieldsMaterialize.recursive_args_sublist
    {semanticEnv trEnv : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain semanticEnv decl)}
    {recursiveArgs allArgs : List VExpr}
    {fields : List (decl.RecursiveField semanticEnv)}
    (Hsel : RecursorFieldSelections semanticEnv decl bu u certs)
    (Hmat : RecursorFieldsMaterialize semanticEnv decl certs recursiveArgs fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList allArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    (fields.map (fun field => field.arg)).Sublist allArgs := by
  rw [Hmat.args]
  exact Hsel.translatedSublist Hbu Hu Hunique

/-- The complete recursive-field fragment of `VInductDecl.IotaRule`, isolated
from the surrounding lhs/rhs telescope bookkeeping. -/
structure IotaFieldCertificate (env : VEnv) (decl : VInductDecl)
    (ctorArgs : List VExpr) (fields : List (decl.RecursiveField env))
    (recursiveArgs : List VExpr) where
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = fields.map (fun field => field.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ fields,
    ∃ h : field.fieldIndex < ctorArgs.length,
      field.arg = ctorArgs[field.fieldIndex]'h
  recursiveArgs_eq : recursiveArgs = fields.map (fun field => field.arg)
  recursive_args : recursiveArgs.Sublist ctorArgs

def RecursorFieldsMaterialize.iotaFieldCertificate
    {semanticEnv trEnv : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain semanticEnv decl)}
    {recursiveArgs ctorArgs : List VExpr}
    {fields : List (decl.RecursiveField semanticEnv)}
    (Hsel : RecursorFieldSelections semanticEnv decl bu u certs)
    (Hmat : RecursorFieldsMaterialize semanticEnv decl certs recursiveArgs fields)
    (Hbu : List.Forall₂ (TrExprS trEnv Us Δ) bu.toList ctorArgs)
    (Hu : List.Forall₂ (TrExprS trEnv Us Δ) u.toList recursiveArgs)
    (Hunique : ∀ arg ∈ u.toList, TrExprS.IsUnique arg) :
    IotaFieldCertificate semanticEnv decl ctorArgs fields recursiveArgs where
  fieldPositions := fields.map (fun field => field.fieldIndex)
  fieldPositions_eq := rfl
  fieldPositions_ordered := Hmat.positions_ordered Hsel
  fields_at_positions := Hmat.fields_at_positions Hsel Hbu Hu Hunique
  recursiveArgs_eq := Hmat.args.symm
  recursive_args := by
    rw [← Hmat.args]
    exact Hmat.recursive_args_sublist Hsel Hbu Hu Hunique

/-- Non-recursive equation shape shared by generated iota rules. Recursive
field selection and RHS guardedness are supplied by separate certificates. -/
structure IotaEquationCertificate
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_name : recursor.name = decl.recursorName owner
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + (ctorArgs.length - decl.nparams)

/-- Assemble the independent iota judgment from its three reviewable pieces:
equation shape, recursive-field selection, and guarded RHS construction. -/
def VInductDecl.IotaRule.ofCertificates
    (Hshape : IotaEquationCertificate decl block owner ctor rule)
    (Hfields : IotaFieldCertificate env decl
      (Hshape.ctorArgs.drop decl.nparams) fields recursiveArgs)
    (Hrhs : IotaRhsCertificate (block.recursors.map (·.name))
      Hshape.domains (Hshape.ctorArgs.drop decl.nparams)
      recursiveArgs Hshape.rhsBody) :
    decl.IotaRule env block owner ctor rule where
  recursor := Hshape.recursor
  recursor_mem := Hshape.recursor_mem
  recursor_name := Hshape.recursor_name
  rule_uvars := Hshape.rule_uvars
  domains := Hshape.domains
  lhsBody := Hshape.lhsBody
  rhsBody := Hshape.rhsBody
  typeBody := Hshape.typeBody
  lhs_wrapped := Hshape.lhs_wrapped
  rhs_wrapped := Hshape.rhs_wrapped
  type_wrapped := Hshape.type_wrapped
  recursorLevels := Hshape.recursorLevels
  leadingArgs := Hshape.leadingArgs
  ctorLevels := Hshape.ctorLevels
  ctorArgs := Hshape.ctorArgs
  lhs_pattern := Hshape.lhs_pattern
  recursor_levels := Hshape.recursor_levels
  ctor_levels := Hshape.ctor_levels
  leading_arity := Hshape.leading_arity
  constructor_arity := Hshape.constructor_arity
  parameter_args := Hshape.parameter_args
  domains_arity := Hshape.domains_arity
  recursiveFields := fields
  fieldPositions := Hfields.fieldPositions
  fieldPositions_eq := Hfields.fieldPositions_eq
  fieldPositions_ordered := Hfields.fieldPositions_ordered
  fields_at_positions := Hfields.fields_at_positions
  recursiveArgs := recursiveArgs
  recursiveArgs_eq := Hfields.recursiveArgs_eq
  recursive_args := Hfields.recursive_args
  fieldVars := Hrhs.fieldVars
  fieldVars_eq := Hrhs.fieldVars_eq
  fields_in_scope := Hrhs.fields_in_scope
  minorVar := Hrhs.minorVar
  minor_in_scope := Hrhs.minor_in_scope
  rhsArgs := Hshape.ctorArgs.drop decl.nparams ++ Hrhs.recursiveResults
  rhs_spine := Hrhs.rhs_spine
  field_args := by
    simpa using Hrhs.field_args
  recursive_results := by
    simpa using Hrhs.results_length
  rhs_guarded := Hrhs.guarded

/-- Exact concrete common-parameter prefix consumed by recursor generation.
The relation is intentionally separate from field classification: agreement
of these substitutions with the abstract parameter telescope is established
during constructor checking. -/
inductive RecursorParamPrefix (stats : AddInductive.InductiveStats) :
    Nat → Expr → Expr → Prop
  | done : i = stats.params.size → RecursorParamPrefix stats i tail tail
  | step : stats.params[i]? = some param →
      RecursorParamPrefix stats (i + 1) (body.instantiate1 param) tail →
      RecursorParamPrefix stats i (.forallE name dom body bi) tail

namespace mkRecInfos.loopCtorArgs.loop

/-- `loopCtorArgs.loop` follows a certified common-parameter prefix without
changing either accumulator, then delegates to the supplied tail proof. Fuel
exhaustion is harmless because it cannot return successfully. -/
theorem followsParamPrefix {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t tail : Expr} {i : Nat} {bu u : Array Expr}
    {c : AddInductive.Context} {Q : α → Prop}
    (hprefix : RecursorParamPrefix stats i t tail)
    (Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size bu u fuel c).WF Q) :
    ∀ fuel, (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  intro fuel
  induction fuel generalizing t i with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases hprefix with
    | done hi =>
      subst i
      exact Htail (fuel + 1)
    | @step i param body tail name dom bi hparam hprefix =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop, hparam]
      exact ih hprefix

/-- Typed refinement of the genuine-field suffix of `loopCtorArgs`. Common
parameters have already been exhausted, so every remaining forall binder is a
constructor field. Each successful recursive classification extends an exact
ordered list of independent `RecursiveArg` certificates. -/
theorem recursiveDomains {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : α → Prop}
    (Hc : ContextWF c)
    {fields : List (RecursorRecursiveDomain Hc.venv decl)}
    {args : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hparams : stats.params.size ≤ i)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx t type')
    (hfields : RecursorFieldSelections Hc.venv decl bu u fields)
    (hargs : List.Forall₂
      (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) u.toList args)
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {t' : Expr} {type'' : VExpr}
      {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomain Hc'.venv decl)} {args' : List VExpr},
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx t' type'' →
      RecursorFieldSelections Hc'.venv decl bu' u' fields' →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u depth type' fields args with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      have hparam : stats.params[i]? = none := by
        apply Array.getElem?_eq_none
        omega
      rw [hparam]
      have htypeTr := htype.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
      rcases TrExpr.forallE_source htypeTr with
        ⟨sourceDom', sourceBody', hdom, hbody, hdomType, _, _⟩
      rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
      rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
      refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
        Hc Hdom.consumed Hdom.isType ?_
      let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType
      have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
        Hc Hdom.consumed Hdom.isType
      have hctx' : checkPositivityStep.VLCtx.NoIndConsts
          (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
        apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
        rfl
      let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have hdomWeak : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx dom
          (sourceDom'.liftN 1 0) := by
        apply Hdom.source.weakFV Hc.checking.tr.wf.ordered
          W
        exact Hc'.mlctx_wf.tr.wf
      have hargsWeak : List.Forall₂
          (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) u.toList
          (args.map fun arg => arg.liftN 1 0) := by
        apply checkPositivityStep.forall₂_map_right hargs
        intro source arg harg
        exact harg.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
      have harg : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        exact TrExprS.fvar (A := consumedDom'.lift) (by
          change VLCtx.find? ((some (⟨c.ngen.curr⟩,
            dom.consumeTypeAnnotations.fvarsList), .vlam consumedDom') ::
              Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type])
      have hopened := Hc.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbody''
      have Hclass := isRecArg.refines Hc' Hstats' hconsume hlit hctx' hproj
        (hdomWeak.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
      refine Hclass.bind fun selected hselected => ?_
      cases selected with
      | none =>
        exact ih Hc' Hstats' (by omega) hctx' hopened
          (.nonrecursive hfields) hargsWeak
      | some target =>
        rcases hselected target rfl with ⟨howner, hrecursive⟩
        let cert : RecursorRecursiveDomain Hc'.venv decl := {
          fieldIndex := bu.size
          ownerIdx := target
          owner_lt := howner
          ctx := Hc'.mlctx.vlctx.toCtx
          depth := depth + 1
          domain := sourceDom'.liftN 1 0
          recursive := hrecursive }
        have hargs' : List.Forall₂
            (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
            (u.push (.fvar ⟨c.ngen.curr⟩)).toList
            ((args.map fun arg => arg.liftN 1 0) ++ [.bvar 0]) := by
          simpa using checkPositivityStep.forall₂_append
            hargsWeak (.cons harg .nil)
        exact ih Hc' Hstats' (by omega) hctx' hopened
          (.recursive hfields (cert := cert) rfl) hargs'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      exact Hk Hc htype hfields hargs

end mkRecInfos.loopCtorArgs.loop

/-- Full constructor-argument refinement, composing exact common-parameter
substitution with typed recursive-field classification. -/
theorem mkRecInfos.loopCtorArgs.recursiveDomains {α : Type}
    (stats : AddInductive.InductiveStats) (t tail : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context) {Q : α → Prop}
    {decl : VInductDecl} {tail' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hprefix : RecursorParamPrefix stats 0 t tail)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htail : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx tail tail')
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {t' : Expr} {type'' : VExpr} {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomain Hc'.venv decl)} {args' : List VExpr},
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx t' type'' →
      RecursorFieldSelections Hc'.venv decl bu' u' fields' →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  let inputContext := c
  unfold AddInductive.mkRecInfos.loopCtorArgs
  have hread : ((read : AddInductive.M AddInductive.Context) inputContext).WF
      (fun c' => c' = inputContext) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  have Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size #[] #[] fuel inputContext).WF Q := by
    intro fuel
    exact mkRecInfos.loopCtorArgs.loop.recursiveDomains stats k Hc Hstats
      (Nat.le_refl _) hconsume hlit hctx hproj htail .nil .nil Hk
  exact mkRecInfos.loopCtorArgs.loop.followsParamPrefix stats k hprefix Htail
    inputContext.fuel.inductiveFuel

namespace mkRecInfos.loopArgs1

/-- `loopArgs1` cannot manufacture a successful result: after any sequence
of WHNF steps and local index binders it returns only through its supplied
continuation. This structural fact is the outer-loop interface used to count
one motive record per mutual family. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M α)
    {Q : α → Prop}
    (Hk : ∀ indices c, (k indices c).WF Q) :
    ∀ type i indices fuel c,
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, 0, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, i, indices, fuel + 1, c => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        by_cases hparam : i < stats.params.size
        · rw [if_pos hparam]
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 stats.params[i]!)) :
                AddInductive.M Expr) c).WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWith stats k Hk next (i + 1) indices fuel c
        · rw [if_neg hparam]
          unfold Lean4Lean.withLocalDecl
            MonadLocalNameGenerator.withFreshId
            AddInductive.instMonadLocalNameGeneratorM
            AddInductive.instMonadWithReaderOfLocalContextM
          let c' : AddInductive.Context := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }
          change ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c' >>= fun next =>
              AddInductive.mkRecInfos.loopArgs1 stats next i
                (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel k c').WF Q
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
                AddInductive.M Expr) c').WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWith stats k Hk next i
              (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel c'
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          simpa [AddInductive.mkRecInfos.loopArgs1] using Hk indices c

end mkRecInfos.loopArgs1

/-- Structural opening of a production local declaration when the proof only
needs to follow the continuation and does not yet claim typing for the new
domain. -/
theorem withLocalDecl.continueRaw
    {α : Type} {Q : α → Prop} {k : Expr → AddInductive.M α}
    {c : AddInductive.Context} {name : Name} {bi : BinderInfo} {ty : Expr}
    (H : (k (.fvar ⟨c.ngen.curr⟩) { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
    AddInductive.instMonadLocalNameGeneratorM
    AddInductive.instMonadWithReaderOfLocalContextM
  exact H

/-- `Except.WF.bind` lifted across the reader layer used by the executable
inductive checker. Keeping the reader bind visible avoids repeatedly
unfolding `ReaderT` in structural traversal proofs. -/
theorem readerBind.WF
    {α β : Type} {Q : α → Prop} {R : β → Prop}
    {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context}
    (Hx : (x c).WF Q) (Hf : ∀ a, Q a → (f a c).WF R) :
    ((x >>= f) c).WF R := by
  exact Hx.bind Hf

namespace mkRecInfos.loopInd1

/-- The first recursor pass appends exactly one `RecInfo` (motive, indices,
major premise) for each mutual family. -/
theorem resultCount
    {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = dIdx)
    (hempty : ∀ r ∈ recInfos.toList, r.minors.isEmpty)
    (harities : ∀ i, i < recInfos.size →
      recInfos[i]!.indices.size = stats.nindices[i]!)
    (Hk : ∀ recInfos c, recInfos.size = indTypes.size →
      (∀ r ∈ recInfos.toList, r.minors.isEmpty) →
      (∀ i, i < recInfos.size →
        recInfos[i]!.indices.size = stats.nindices[i]!) →
      (k recInfos c).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context) hread fun ctx hctx => ?_
    subst ctx
    have hwhnf :
        ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
          AddInductive.M Expr) c).WF (fun _ => True) := by
      intro _ _
      trivial
    refine hwhnf.bind fun type _ => ?_
    apply mkRecInfos.loopArgs1.continueWith stats
    intro indices cIndices
    by_cases harity : (indices.size == stats.nindices[dIdx]!) = true
    · rw [if_pos harity]
      apply withLocalDecl.continueRaw
      let cMajor : AddInductive.Context := { cIndices with
        ngen := cIndices.ngen.next
        lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
          (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices).consumeTypeAnnotations
          .default }
      have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
          (fun lctx => lctx = cMajor.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      apply withLocalDecl.continueRaw
      apply mkRecInfos.loopInd1.resultCount
        (stats := stats) (indTypes := indTypes) (elimLevel := elimLevel)
        (dIdx := dIdx + 1) (recInfos := recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩, minors := #[], indices := indices,
          major := .fvar ⟨cIndices.ngen.curr⟩ }) (k := k)
        (Q := Q)
      · omega
      · simpa [hsize]
      · intro r hr
        simp only [Array.toList_push, List.mem_append, List.mem_cons,
          List.mem_singleton] at hr
        rcases hr with hr | hr
        · exact hempty r hr
        · rcases hr with rfl | hr
          · rfl
          · contradiction
      · intro i hiPush
        have harityEq : indices.size = stats.nindices[dIdx]! := by
          simpa using harity
        by_cases hilast : i = recInfos.size
        · subst i
          simpa [← hsize, harityEq]
        · have hiOld : i < recInfos.size := by
            have hiPush' : i < recInfos.size + 1 := by simpa using hiPush
            omega
          have hbang :
              (recInfos.push {
                motive := .fvar ⟨cMajor.ngen.curr⟩, minors := #[],
                indices := indices,
                major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
            simp only [Array.getElem!_eq_getD]
            unfold Array.getD
            rw [dif_pos hiPush, dif_pos hiOld]
            exact Array.getElem_push_lt hiOld
          rw [hbang]
          exact harities i hiOld
      · exact Hk
    · rw [if_neg harity]
      exact Except.WF.throw
  · rw [dif_neg hidx]
    apply Hk
    · omega
    · exact hempty
    · exact harities
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd1

namespace mkRecInfos.loopU

/-- The induction-hypothesis loop returns only through its continuation.
Its generated local declarations affect the eventual minor type, but not the
`RecInfo` array whose cardinality is tracked by `loopCtors`. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M α) {Q : α → Prop}
    (Hk : ∀ v c, (k v c).WF Q)
    (i : Nat) (v : Array Expr) (c : AddInductive.Context) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k c).WF Q := by
      rw [AddInductive.mkRecInfos.loopU]
      by_cases hnext : i < u.size
      · rw [dif_pos hnext]
        have hviTy :
            ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
              let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
              let motiveApp := .app
                (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
              return (← getLCtx).mkForall xs motiveApp) c).WF
              (fun _ => True) := by
          intro _ _
          trivial
        refine hviTy.bind fun viTy _ => ?_
        have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
            (fun lctx => lctx = c.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        apply withLocalDecl.continueRaw
        exact continueWith stats u recInfos k Hk (i + 1)
          (v.push (.fvar ⟨c.ngen.curr⟩)) _
      · rw [dif_neg hnext]
        exact Hk v c
termination_by u.size - i

end mkRecInfos.loopU

namespace mkRecInfos.loopCtors

theorem getElemBang_modify_ne {α : Type} [Inhabited α]
    (xs : Array α) (dIdx i : Nat) (f : α → α)
    (hi : i < xs.size) (hne : dIdx ≠ i) :
    (xs.modify dIdx f)[i]! = xs[i]! := by
  have hi' : i < (xs.modify dIdx f).size := by simpa using hi
  have heq : (xs.modify dIdx f)[i]'hi' = xs[i]'hi := by
    rw [Array.getElem_modify]
    simp [hne]
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

theorem getElemBang_modify_self {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) (hi : i < xs.size) :
    (xs.modify i f)[i]! = f xs[i]! := by
  have hi' : i < (xs.modify i f).size := by simpa using hi
  have heq : (xs.modify i f)[i]'hi' = f (xs[i]'hi) :=
    Array.getElem_modify_self f hi'
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

/-- Processing a constructor list preserves the number of family records and
appends exactly one minor premise per constructor to the selected owner. -/
theorem resultCount {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats) (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors : List Constructor)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hidx : dIdx < recInfos.size)
    (Hk : ∀ out c,
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + ctors.length →
      { out[dIdx]! with minors := #[] } = { recInfos[dIdx]! with minors := #[] } →
      (∀ i, i < recInfos.size → dIdx ≠ i → out[i]! = recInfos[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos ctors k c).WF Q := by
  induction ctors generalizing recInfos c with
  | nil =>
      simp only [AddInductive.mkRecInfos.loopCtors]
      apply Hk
      · rfl
      · simp
      · rfl
      · intros
        rfl
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecInfos.loopCtors]
      apply mkRecInfos.loopCtorArgs.selectedSublist stats
      intro t bu u cArgs _
      apply mkRecInfos.loopU.continueWith stats u recInfos
      intro v cIH
      have hget : ((getLCtx : AddInductive.M LocalContext) cIH).WF
          (fun lctx => lctx = cIH.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      apply withLocalDecl.continueRaw
      let next := recInfos.modify dIdx fun s =>
        { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) }
      apply ih next _
      · simpa [next]
      · intro out cOut houtSize houtCount houtFrame
          houtOther
        apply Hk out cOut
        · simpa [next] using houtSize
        · rw [houtCount]
          dsimp [next]
          have hnextIdx : dIdx < (recInfos.modify dIdx fun s =>
              { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) }).size := by
            simpa using hidx
          have hbangModified :
              (recInfos.modify dIdx fun s =>
                { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) })[dIdx]! =
              { recInfos[dIdx]! with
                minors := recInfos[dIdx]!.minors.push (.fvar ⟨cIH.ngen.curr⟩) } := by
            simp only [Array.getElem!_eq_getD]
            unfold Array.getD
            rw [dif_pos hnextIdx, dif_pos hidx]
            exact Array.getElem_modify_self _ hnextIdx
          rw [hbangModified]
          simp
          omega
        · rw [houtFrame]
          dsimp [next]
          rw [getElemBang_modify_self recInfos dIdx _ hidx]
        · intro i hi hine
          rw [houtOther i (by simpa [next] using hi) hine]
          exact getElemBang_modify_ne recInfos dIdx i _ hi hine

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

def SameFrame (a b : AddInductive.RecInfo) : Prop :=
  { a with minors := #[] } = { b with minors := #[] }

theorem SameFrame.refl (a : AddInductive.RecInfo) : SameFrame a a := rfl

theorem SameFrame.trans (hab : SameFrame a b) (hbc : SameFrame b c) :
    SameFrame a c := Eq.trans hab hbc

theorem SameFrame.indices_eq (H : SameFrame a b) : a.indices = b.indices := by
  have h := congrArg AddInductive.RecInfo.indices H
  simpa [SameFrame] using h

/-- The second mutual pass finishes every family with exactly one minor per
owned constructor. The prefix/suffix formulation makes the mutation boundary
explicit and is directly initialized by `loopInd1`, whose minor arrays are
empty. -/
theorem resultCounts {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (origin : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = indTypes.size)
    (horiginSize : origin.size = recInfos.size)
    (hframes : ∀ i, i < recInfos.size → SameFrame recInfos[i]! origin[i]!)
    (hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hsuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      out.size = origin.size →
      (∀ i, i < out.size → SameFrame out[i]! origin[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultCount (Q := Q) stats indTypes[dIdx].name dIdx
      recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes (dIdx + 1) out k)
      c (by simpa [hsize] using hidx)
    intro out cOut houtSize houtCount houtFrame houtOther
    apply mkRecInfos.loopInd2.resultCounts (Q := Q) stats indTypes (dIdx + 1)
      out origin k cOut
    · omega
    · simpa [hsize] using houtSize
    · omega
    · intro i hiout
      apply SameFrame.trans (b := recInfos[i]!)
      · by_cases heq : i = dIdx
        · subst i
          exact houtFrame
        · rw [houtOther i (by simpa [hsize, houtSize] using hiout) (Ne.symm heq)]
          exact SameFrame.refl _
      · exact hframes i (by simpa [houtSize] using hiout)
    · intro i hi hiout
      by_cases heq : i = dIdx
      · subst i
        rw [houtCount, hsuffix dIdx (by omega) (by simpa [hsize] using hidx)]
        simp [Array.getElem!_eq_getD, Array.getD, hidx]
      · rw [houtOther i (by simpa [hsize, houtSize] using hiout) (Ne.symm heq)]
        exact hprefix i (by omega) (by simpa [hsize, houtSize] using hiout)
    · intro i hi hiout
      rw [houtOther i (by simpa [hsize, houtSize] using hiout) (by omega)]
      exact hsuffix i (by omega) (by simpa [hsize, houtSize] using hiout)
    · exact Hk
  · rw [dif_neg hidx]
    apply Hk recInfos c hsize
    · intro i hi
      exact hprefix i (by omega) hi
    · omega
    · exact hframes
termination_by indTypes.size - dIdx

/-- `loopInd2` changes only the `minors` field of each `RecInfo`; motives,
indices, and major premises remain those constructed by `loopInd1`. -/
theorem resultFrames {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = indTypes.size)
    (Hk : ∀ out c, out.size = recInfos.size →
      (∀ i, i < recInfos.size → SameFrame out[i]! recInfos[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultCount (Q := Q) stats indTypes[dIdx].name dIdx
      recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes (dIdx + 1) out k)
      c (by simpa [hsize] using hidx)
    intro out cOut houtSize _ houtFrame houtOther
    apply mkRecInfos.loopInd2.resultFrames (Q := Q) stats indTypes (dIdx + 1)
      out k cOut
    · omega
    · simpa [hsize] using houtSize
    · intro final cFinal hfinalSize hfinalFrames
      apply Hk final cFinal
      · simpa [houtSize] using hfinalSize
      · intro i hi
        apply SameFrame.trans (hfinalFrames i (by simpa [houtSize] using hi))
        by_cases heq : i = dIdx
        · subst i
          exact houtFrame
        · have hsibling := houtOther i hi (Ne.symm heq)
          rw [hsibling]
          exact SameFrame.refl _
  · rw [dif_neg hidx]
    apply Hk recInfos c
    · rfl
    · intro i hi
      exact SameFrame.refl _
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

/-- End-to-end structural cardinality theorem for production `mkRecInfos`:
one record per mutual family, initialized by the first pass and populated with
one minor per source constructor by the second pass. -/
theorem mkRecInfos.resultStructure {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ (initial out : Array AddInductive.RecInfo)
        (c : AddInductive.Context),
      initial.size = indTypes.size →
      (∀ r ∈ initial.toList, r.minors.isEmpty) →
      (∀ i, i < initial.size →
        initial[i]!.indices.size = stats.nindices[i]!) →
      out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      (∀ i, i < out.size →
        mkRecInfos.loopInd2.SameFrame out[i]! initial[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  unfold AddInductive.mkRecInfos
  apply mkRecInfos.loopInd1.resultCount (Q := Q) stats indTypes elimLevel
    0 #[] (fun recInfos =>
      AddInductive.mkRecInfos.loopInd2 stats indTypes 0 recInfos k) c
  · omega
  · simp
  · simp
  · simp
  · intro recInfos cRec hsize hempty harities
    apply mkRecInfos.loopInd2.resultCounts (Q := Q) stats indTypes 0
      recInfos recInfos k cRec
    · omega
    · exact hsize
    · rfl
    · intro i hi
      exact mkRecInfos.loopInd2.SameFrame.refl _
    · intro i hi
      omega
    · intro i _ hi
      have he := hempty (recInfos[i]'hi) (Array.getElem_mem_toList hi)
      rw [Array.isEmpty_iff_size_eq_zero] at he
      simpa [Array.getElem!_eq_getD, Array.getD, hi] using he
    · intro out cOut houtSize houtCounts _ houtFrames
      exact Hk recInfos out cOut hsize hempty harities houtSize houtCounts
        houtFrames

/-- Cardinality-only projection of `resultStructure`. -/
theorem mkRecInfos.resultCounts {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultStructure (Q := Q) stats indTypes elimLevel k c
  intro _ out cOut _ _ _ houtSize houtCounts _
  exact Hk out cOut houtSize houtCounts

/-- Per-family minor counts imply the corresponding flattened block count
used by production recursor types. -/
theorem mkRecInfos.flatMinors_size
    {recInfos : Array AddInductive.RecInfo}
    {indTypes : Array InductiveType}
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  rw [Array.size_flatMap, Array.size_flatMap]
  congr 1
  apply Array.ext
  · simp [hsize]
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    have hiRec : i < recInfos.size := by simpa using hiLeft
    have hiInd : i < indTypes.size := by omega
    have hc := hcounts i hiRec
    simpa [Array.getElem!_eq_getD, Array.getD, hiRec, hiInd] using hc

theorem ownedConstructors_length_eq_flattened_size
    (indTypes : Array InductiveType) :
    (ownedConstructors indTypes.toList).length =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  simp only [ownedConstructors, List.length_flatMap, List.length_map,
    Array.size_flatMap]
  rw [← Array.sum_toList, Array.toList_map]
  simp

theorem mkRecInfos.motives_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (hsize : recInfos.size = indTypes.size) :
    (recInfos.map (·.motive)).size = decl.types.length := by
  simp only [Array.size_map]
  rw [hsize]
  simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl

theorem mkRecInfos.flatMinors_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size = decl.ownedConstructors.length := by
  rw [mkRecInfos.flatMinors_size hsize hcounts,
    ← ownedConstructors_length_eq_flattened_size]
  exact Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl

/-- Structural portion of the independent recursor shape, assembled before
the generated telescope itself is translated. -/
structure RecursorCardinalityCertificate
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (decl : VInductDecl) : Prop where
  records : recInfos.size = decl.types.length
  params : stats.params.size = decl.nparams
  motives : (recInfos.map (·.motive)).size = decl.types.length
  minors : (recInfos.flatMap (·.minors)).size =
    decl.ownedConstructors.length
  indices : ∀ i (hi : i < recInfos.size),
    recInfos[i]!.indices.size =
      (decl.types[i]'(by simpa [records] using hi)).numIndices

theorem RecursorCardinalityCertificate.ofResult
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (harities : ∀ i, i < recInfos.size →
      recInfos[i]!.indices.size = stats.nindices[i]!) :
    RecursorCardinalityCertificate stats recInfos decl where
  records := hsize.trans (by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl)
  params := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      Hmaterialized.narrowParams
    simpa [VInductDecl.paramVars] using hlen
  motives := mkRecInfos.motives_size_of_translation Hdecl hsize
  minors := mkRecInfos.flatMinors_size_of_translation Hdecl hsize hcounts
  indices := by
    let Hstats :=
      checkPositivityStep.ValidAppStatsWF.ofMaterializedHeader Hmaterialized
    intro i hi
    have hiDecl : i < decl.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl]
      simpa [hsize] using hi
    have hn := Hstats.nindicesAt hiDecl
    have hstats : stats.nindices[i]! = decl.types[i].numIndices := by
      obtain ⟨hstatsBound, hnget⟩ := Array.getElem?_eq_some_iff.mp hn
      simpa [Array.getElem!_eq_getD, Array.getD, hstatsBound] using hnget
    exact (harities i hi).trans hstats

/-- Public `mkRecInfos` boundary carrying all independently specified
telescope cardinalities into the recursor-construction continuation. -/
theorem AddInductive.mkRecInfos.cardinalityWF
    {α : Type} {Q : α → Prop}
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (Hk : ∀ recInfos c,
      Nonempty (RecursorCardinalityCertificate stats recInfos decl) →
      (k recInfos c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultStructure (Q := Q) stats indTypes elimLevel k c
  intro initial out cOut hinitial _ hinitialArities hout hcounts hframes
  have houtArities : ∀ i, i < out.size →
      out[i]!.indices.size = stats.nindices[i]! := by
    intro i hi
    have hiInitial : i < initial.size := by omega
    rw [(hframes i hi).indices_eq]
    exact hinitialArities i hiInitial
  exact Hk out cOut ⟨RecursorCardinalityCertificate.ofResult
    Hdecl Hmaterialized hout hcounts houtArities⟩

/-- Constructor-tail refinement with the verified positivity traversal plugged
into every safe field. -/
theorem checkConstructors.loopCtor.tailRefinesFull
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  apply checkConstructors.loopCtor.tailRefines Hc Hstats hi htarget
    hparamAt hconsume hlit hctx hproj hunsafe hbound
  · intro c' depth' posIdx type' type'' Hc' Hstats' hctx' htype'
    exact checkPositivity.refines Hc' Hstats' hconsume hlit hctx' hproj htype'
  · exact htr

/-- Regard a constructor constant as the root of a telescope synthesis.  The
existing narrow header certificate only uses the constant fields of its
`target`; the empty constructor list therefore lets the same, already proved
wrapping invariant serve constructor parameter prefixes without duplicating
it. -/
def constructorTelescopeTarget (ctorVal : VConstVal) :
    VInductiveTypeSkeleton where
  toVConstVal := ctorVal
  ctors := []

/-- Initialize constructor telescope synthesis from the independently
translated source constant. -/
noncomputable def ConstructorSynthesisState.initial
    (Hctor : TrSourceConst env Us ctor type ctorVal) :
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us (constructorTelescopeTarget ctorVal) [] ctorVal.type 0 0 := by
  have htype : env.IsType Us.length [] ctorVal.type := by
    have hwf := Hctor.wf
    change env.IsType ctorVal.uvars [] ctorVal.type at hwf
    rwa [Hctor.uvars] at hwf
  let level := Classical.choose htype
  have htyped := Classical.choose_spec htype
  exact checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
    htype htype htyped

/-- A successful cached-parameter comparison advances the semantic
constructor telescope directly.  The executable loop performs no
normalization in this branch: after converting the binder context from the
source domain to the cached parameter type, opening the source body with the
cached free variable supplies the next residual verbatim. -/
theorem checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.consumeConstructorParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i 0)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom,
      TrExprS env Us scope dom sourceDom ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom paramType) :
    ∃ next,
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next ∧
      Nonempty (NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0) := by
  cases htype with
  | forallE hdomType _hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom, hsourceDom, hsourceDomEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    rcases hbody.defeqDFC henv hbodyCtx with ⟨next, hnext⟩
    have hopened : TrExprS env Us
        ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next :=
      hnext.inst_fvar henv.ordered hscopeWF
    have hbodyWF : VLCtx.WF env Us.length
        ((none, .vlam paramType) :: scope) :=
      ⟨H.scopeWF, nofun, ⟨_, hdomTyped.hasType.2⟩⟩
    have hnextRefl : env.IsDefEqU Us.length
        (paramType :: scope.toCtx) next next :=
      hnext.wf henv.ordered hbodyWF
    have hindices : H.indices = [] :=
      List.eq_nil_of_length_eq_zero H.indexCount
    have htype' : TrExprS env Us scope
        (.forallE name dom body bi) (.forallE _ _) :=
      .forallE hdomType _hbodyType hdom hbody
    rcases H.consumeParameter (name := name) (bi := bi)
        henv hindices htype' hscopeWF
        ⟨sourceDom, hsourceDom, hsourceDomEq⟩
        ⟨next, next, hnext, hopened, hnextRefl⟩ with
      ⟨next', hopened', Hnext⟩
    exact ⟨next', hopened', Hnext⟩

/-- Traverse the executable constructor's common-parameter prefix while
building its independent semantic telescope.  The two callbacks isolate the
control-flow boundaries: exact parameter coverage hands the synthesized tail
to the field verifier, while an early non-forall is discharged separately by
the invalid-result argument. -/
theorem checkConstructors.loopCtor.parameterSynthesisWF
    {decl : VInductDecl} {ctorVal : VConstVal}
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Q : Unit → Prop)
    (Hresult : ∀ {source' : Expr}
        {current' fullCurrent' : VExpr} {fuel' : Nat},
      (Hsynthesis' :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          Hsuffix.parameterDecls current' decl.nparams 0) →
      TrExprS Hc.venv c.lparams Hsuffix.parameterDecls source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' decl.nparams (fuel' + 1) c).WF Q)
    (Hearly : ∀ {source' : Expr} {scope' : VLCtx}
        {current' fullCurrent' : VExpr} {i' fuel' : Nat},
      i' < decl.nparams →
      (¬ ∃ name dom body bi, source' = .forallE name dom body bi) →
      checkInductiveTypes.loopType.LaterParameterScope
        Hsuffix i' source' →
      (Hsynthesis' :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          scope' current' i' 0) →
      TrExprS Hc.venv c.lparams scope' source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' i' (fuel' + 1) c).WF Q)
    (hparams : stats.params.size = decl.nparams)
    (hbound : i ≤ decl.nparams)
    (Hscope : ∀ h : i < stats.params.size,
      checkInductiveTypes.loopType.LaterParameterScope Hsuffix i source)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = decl.nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      source fullCurrent) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i fuel c).WF Q := by
  induction fuel generalizing source scope current fullCurrent i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hi : i < decl.nparams
    · have histats : i < stats.params.size := by
        simpa [hparams] using hi
      by_cases hforall : ∃ name dom body bi,
          source = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        cases htypeNarrow with
        | @forallE narrowDom narrowBody _ _ _ _ _
            hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨fullDom, fullBody, hdomFull, hbodyFull,
              _hdomFullType, _hbodyFullType, _hfullCurrent⟩
          rcases Hcurrent.typing with
            ⟨paramTy, paramTy', param', hget, hparamTy,
              hparamTyEq, hparam, hparamType⟩
          have hparamAt : stats.params[i]? = some stats.params[i]! := by
            simp [Array.getElem!_eq_getD, histats]
          refine checkConstructors.loopCtor.parameter.sourceWF
            (Q := Q) Hc hparamAt hget hdomFull hbodyFull
              hparamTy hparam hparamType ?_
          intro heq hopenedFull
          rcases Hcurrent.domainDefEq hdomFull hparamTyEq heq with
            ⟨sourceDom, hsourceDom, hsourceDomEq⟩
          have hconsumedWF : VLCtx.WF Hc.venv c.lparams.length
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older) :=
            Hcurrent.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
          have htypeNarrow' : TrExprS Hc.venv c.lparams Hcurrent.older
              (.forallE name dom body bi) (.forallE narrowDom narrowBody) :=
            .forallE hdomNarrowType hbodyNarrowType
              hdomNarrow hbodyNarrow
          rcases Hsynthesis.consumeConstructorParameter
              (name := name) (bi := bi)
              Hc.checking.tr.wf
              htypeNarrow'
              hconsumedWF
              ⟨sourceDom, hsourceDom, hsourceDomEq⟩ with
            ⟨next, hopenedNarrow, ⟨Hsynthesis'⟩⟩
          have hopenedNarrow' : TrExprS Hc.venv c.lparams
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older)
              (body.instantiate1 stats.params[i]!) next := by
            simpa [Expr.instantiate1_eq, Hcurrent.parameter] using
              hopenedNarrow
          let Hbody :
              checkInductiveTypes.loopType.LaterParameterScope
                Hsuffix i body :=
            { Hcurrent with fvars := Hcurrent.fvars.2 }
          exact ih (i := i + 1)
            (scope := (some (Hcurrent.fv, Hcurrent.deps),
              .vlam Hcurrent.paramType) :: Hcurrent.older)
            (current := next) (fullCurrent := fullBody.inst param')
            (hbound := by omega)
            (Hscope := fun hlt => Hbody.next hlt (fun _ _ h => h))
            (hscopeEq := fun hlt =>
              Hbody.nextOlder (Hbody.next hlt (fun _ _ h => h)) hlt)
            (hcompleteScope := fun heq => by
              have hdone : i + 1 = stats.params.size := by
                rw [hparams]
                exact heq
              exact Hbody.completedScope hdone)
            Hsynthesis' hopenedNarrow'
            (hopenedFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      · exact Hearly hi hforall (Hscope histats)
          Hsynthesis htypeNarrow htypeFull
    · have hieq : i = decl.nparams := by omega
      subst i
      have hscope := hcompleteScope rfl
      subst scope
      exact Hresult Hsynthesis htypeNarrow htypeFull

theorem _root_.Lean4Lean.FVarsIn.getAppArgsList
    (H : FVarsIn P e) (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  have H' : FVarsIn P
      (e.getAppFn.mkAppRevList e.getAppArgsRevList) := by
    rw [Expr.mkAppRevList_getAppArgsRevList]
    exact H
  have ha' : a ∈ e.getAppArgsRevList := by
    simpa [← Expr.getAppArgsList_reverse] using ha
  exact (FVarsIn.appRevList.mp H').2 a ha'

theorem _root_.Lean4Lean.Expr.eqv_fvar_eq
    (H : (((.fvar fv : Expr) == e)) = true) : e = .fvar fv := by
  cases e <;> simp [(· == ·), Expr.eqv'] at H
  rename_i fv'
  have : fv = fv' := beq_iff_eq.mp H
  cases this
  rfl

/-- A constructor cannot reach its result before consuming every cached
parameter.  A valid result application would contain the current cached free
variable as argument `i`, whereas `LaterParameterScope` proves that the tail
can mention only the strictly older cached parameters. -/
theorem checkConstructors.loopCtor.earlyParameterResult.WF
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Hscope : checkInductiveTypes.loopType.LaterParameterScope
      Hsuffix i source)
    (hi : i < stats.params.size)
    (hforall : ¬ ∃ name dom body bi,
      source = .forallE name dom body bi) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i (fuel + 1) c).WF Q := by
  cases hvalid : AddInductive.isValidIndAppIdx stats source targetIdx
  · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
  · have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
    have hiArgs : i < source.getAppArgs.size := by omega
    have hparam : stats.params[i] = .fvar Hscope.fv := by
      have hparam' := Hscope.parameter
      simpa [hi] using hparam'
    have hargEq := checkPositivityStep.isValidIndAppIdx.param hvalid hi
    rw [hparam] at hargEq
    have harg : source.getAppArgs[i] = .fvar Hscope.fv :=
      Expr.eqv_fvar_eq hargEq
    have hsourceArg : source.getAppArgsList[i]? =
        some source.getAppArgs[i] := by
      rw [← Expr.getAppArgs_toList]
      simp [hiArgs]
    have hmem : source.getAppArgs[i] ∈ source.getAppArgsList :=
      List.mem_of_getElem? hsourceArg
    have hargScope := Hscope.fvars.getAppArgsList hmem
    rw [harg] at hargScope
    have hsuffixWF := Hscope.lift.wf Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf
    have hfresh : Hscope.fv ∉ Hscope.older.fvars :=
      (hsuffixWF.2.1 Hscope.fv Hscope.deps rfl).1
    exact False.elim (hfresh hargScope)

/-- Constructor-tail refinement in the independent parameter/field scope.
The executable traversal remains in the retained mutual-header context, but
the resulting `CtorTailWF` never mentions those ambient declarations. -/
theorem checkConstructors.loopCtor.tailRefinesNarrow
    {decl : VInductDecl} {target : VInductiveType}
    {scope : VLCtx} {depth : Nat} {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target scope.toCtx
        depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, hfullTarget⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.refinesNarrow
              (ctor := ctor) (idx := i) Hc Hruntime Hstats
              hconsume hlit hproj hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            refine checkConstructors.loopCtor.safeField.sourceWF
              (Q := fun _ => decl.CtorTailWF Hc.venv target scope.toCtx
                depth (.forallE narrowDom narrowBody))
              Hc hparamAt Hdom hbodyFull Hpos ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound hpositive bodyFull' _hbodyFullEq hopenedFull
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotations.fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
            have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' Hstats' hparamNext hbound
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => by
              have hfieldNarrow := Hruntime.hasTypeOfFull
                Hc.checking.tr.wf hdomNarrow hfield htyped
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              exact .field
                (by simpa [Hstats.uvars] using hfieldNarrow)
                (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                (Or.inr hpositive)
                (by simpa [Hstats.uvars] using hfieldEq)
                (by simpa [Hstats.uvars] using hbodyTyped)
                htail
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              (Q := fun _ => decl.CtorTailWF Hc.venv target scope.toCtx
                depth (.forallE narrowDom narrowBody))
              Hc hparamAt Hdom hbodyFull ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound bodyFull' _hbodyFullEq hopenedFull
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotations.fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
            have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' Hstats' hparamNext hbound
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => by
              have hfieldNarrow := Hruntime.hasTypeOfFull
                Hc.checking.tr.wf hdomNarrow hfield htyped
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              exact .field
                (by simpa [Hstats.uvars] using hfieldNarrow)
                (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                (Or.inl (hunsafe rfl))
                (by simpa [Hstats.uvars] using hfieldEq)
                (by simpa [Hstats.uvars] using hbodyTyped)
                htail
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · rcases htrNarrow.wf Hc.checking.tr.wf
          (Hruntime.scopeWF Hc.checking.tr.wf) with ⟨exprType, htype⟩
        subst target
        exact checkConstructors.loopCtor.result.refines Hstats hi htrNarrow
          hforall hvalid hlit
          (Hruntime.noIndConsts (decl.types.map (·.name))) hproj
          (by simpa [Hstats.uvars] using htype)

/-- Aggregation boundary for constructors: once the common-parameter prefix
has supplied its independent `takeForalls` and parameter-conversion facts, the
verified executable tail establishes the public `CtorShape` judgment. -/
theorem checkConstructors.loopCtor.ctorShapeRefines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ownParams.reverse)
    (htailEq : type' = tail)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have Htail := checkConstructors.loopCtor.tailRefinesFull
    (ctor := ctor) (fuel := fuel) Hc Hstats hi
    htarget hparamAt hconsume hlit hctx hproj hunsafe hbound htr
  exact Htail.mono fun _ htail => by
    subst type'
    have hctxRefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        Hc.mlctx.vlctx.toCtx Hc.mlctx.vlctx.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hc.mlctx_wf.tr.wf.toCtx)
    exact ⟨normalized, ownParams, tail, exprType,
      Hc.mlctx.vlctx.toCtx, hctor, htake, hparams,
      by rw [← hctxEq]; exact hctxRefl, htail⟩

/-- Public constructor-shape refinement from the independent cached-parameter
scope.  `tailCtx` is allowed to be definitionally equal to the normalized
constructor parameters, which is the semantic relation supplied by mutual
header materialization. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesNarrow
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType narrowType fullType : VExpr}
    {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      ownParams.reverse scope.toCtx)
    (htailEq : narrowType = tail)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have Htail := checkConstructors.loopCtor.tailRefinesNarrow
    (ctor := ctor) (fuel := fuel) Hc Hruntime Hstats hi htarget hparamAt
    hconsume hlit hproj hunsafe hbound htrNarrow htrFull
  exact Htail.mono fun _ htail => by
    subst narrowType
    exact ⟨normalized, ownParams, tail, exprType, scope.toCtx,
      hctor, htake, hparams, htailCtx, htail⟩

/-- Close a completely consumed constructor-parameter synthesis directly
against the verified field tail.  In particular, the normalized constructor
type and its `takeForalls` decomposition are outputs of the synthesis
certificate rather than assumptions reconstructed by the caller. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesOfSynthesis
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    {source : Expr} {current fullType : VExpr} {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current decl.nparams 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[decl.nparams]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hparams : decl.ParamsDefEq Hc.venv params Hsynthesis.params)
    (htrNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source decl.nparams fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have htake :
      (VExpr.wrapForalls Hsynthesis.params current).takeForalls decl.nparams =
        some (Hsynthesis.params, current) := by
    simpa [Hsynthesis.parameterCount] using
      VExpr.takeForalls_wrapForalls Hsynthesis.params current
  have htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      Hsynthesis.params.reverse scope.toCtx := by
    have hrefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        scope.toCtx scope.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hsynthesis.scopeWF.toCtx)
    simpa [Hsynthesis.scopeCtx, hindices] using hrefl
  apply checkConstructors.loopCtor.ctorShapeRefinesNarrow
    (ctor := ctor) (fuel := fuel) Hc Hruntime Hstats hi htarget
    hparamAt hconsume hlit hproj hunsafe hbound
    (normalized := VExpr.wrapForalls Hsynthesis.params current)
    (tail := current) (exprType := Hsynthesis.exprType)
    (ownParams := Hsynthesis.params)
  · simpa [constructorTelescopeTarget, hindices, Hstats.uvars] using
      Hsynthesis.header
  · exact htake
  · exact hparams
  · exact htailCtx
  · rfl
  · exact htrNarrow
  · exact htrFull

/-- End-to-end constructor telescope refinement in a single verifier
environment.  The source constructor is independently translated in the
empty scope; the executable closed-type result supplies its retained-runtime
translation.  Cached common parameters are consumed by
`parameterSynthesisWF`, and all remaining binders are checked by the narrow
positivity refinement. -/
theorem checkConstructors.loopCtor.refinesCtorShape
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (Hctor : TrSourceConst Hc.venv c.lparams ctor source ctorVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source checkedType fullType checkedType')
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source 0 fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have hnoFVars : FVarsIn (fun _ => False) source := by
    simpa [VLCtx.fvars] using Hctor.type.fvarsIn
  let Hinitial := ConstructorSynthesisState.initial Hctor
  apply checkConstructors.loopCtor.parameterSynthesisWF
    (decl := decl) (ctorVal := ctorVal) Hc
    (Q := fun _ => decl.CtorShape Hc.venv params target ctorVal)
    (Hresult := by
      intro source' current' fullCurrent' fuel'
        Hsynthesis' htrNarrow htrFull
      have hindices : Hsynthesis'.indices = [] :=
        List.eq_nil_of_length_eq_zero Hsynthesis'.indexCount
      have hscopeCtx : Hsuffix.parameterDecls.toCtx =
          Hsynthesis'.indices.reverse ++ Hsynthesis'.params.reverse :=
        @checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.scopeCtx
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          Hsuffix.parameterDecls current' decl.nparams 0 Hsynthesis'
      have hparams : decl.ParamsDefEq Hc.venv
          params Hsynthesis'.params := by
        change VEnv.IsDefEqCtx Hc.venv decl.uvars []
          params.reverse Hsynthesis'.params.reverse
        simpa [hscopeCtx, hindices] using hparamsCtx
      have hparamAt : stats.params[decl.nparams]? = none := by
        rw [Array.getElem?_eq_none_iff]
        exact Nat.le_of_eq Hstats.params_size
      exact checkConstructors.loopCtor.ctorShapeRefinesOfSynthesis
        (ctor := ctor) (fuel := fuel' + 1) Hc
        (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix)
        Hstats Hsynthesis' hi htarget hparamAt hconsume hlit hproj
        hunsafe hbound hparams htrNarrow htrFull)
    (Hearly := by
      intro source' scope' current' fullCurrent' i' fuel' hi'
        hforall Hscope' _Hsynthesis' _htrNarrow _htrFull
      exact checkConstructors.loopCtor.earlyParameterResult.WF
        (fuel := fuel') Hc Hscope'
        (by simpa [Hstats.params_size] using hi') hforall)
    Hstats.params_size (by omega)
    (fun h =>
      checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars h hnoFVars)
    (fun h =>
      (checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars
        h hnoFVars).older_eq_nil h |>.symm)
    (by
      intro hzero
      have hlength := Hsuffix.parameterDecls_length
      have hempty : Hsuffix.parameterDecls = [] :=
        List.eq_nil_of_length_eq_zero (by
          rw [hlength, Hstats.params_size, hzero])
      exact hempty.symm)
    Hinitial Hctor.type
    (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)

/-- Fold the end-to-end constructor theorem over the production's nested
family/constructor loops.  This is the constructor-formation result consumed
by `FormationCertificate`; environment installation is intentionally a
separate staging obligation. -/
theorem checkConstructors.loopTypes.refinesMaterialized
    {decl : VInductDecl} {sourceEnv : VEnv}
    {params : List VExpr}
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveType sourceEnv Hc.venv c.lparams)
      indTypes.toList decl.types)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hparams : Hmaterialized.headers.params = params)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0 c).WF
      (fun _ => ConstructorCertificate sourceEnv decl Hc.venv params) := by
  let Hsuffix := Hmaterialized.parameterSuffix
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      Hmaterialized
  have hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx := by
    change VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hmaterialized.parameterScope.toCtx
    subst params
    simpa [Hmaterialized.uvars] using Hmaterialized.paramsContext
  apply checkConstructors.loopTypes.refinesBlock
    (Q := fun _ => ConstructorCertificate sourceEnv decl Hc.venv params)
    Hc Htypes (ConstructorTypesPrefix.empty Hc.venv decl params)
    Hfresh
  · intro targetIdx hsource htarget ctorIdx hctorSource hctorTarget
      Hctor checkedType fullType checkedType' hchecked
    apply checkConstructors.loopCtor.refinesCtorShape
      (fuel := c.fuel.inductiveFuel) Hc Hsuffix Hstats hparamsCtx
      Hctor hchecked htarget rfl hconsume hlit hproj hunsafe
    exact hbound targetIdx htarget
  · intro Hcomplete
    exact Hcomplete.complete (env := sourceEnv)

@[simp] theorem VInductDecl.recursorName_eq_mkRecName
    (decl : VInductDecl) (type : VInductiveType) :
    decl.recursorName type = Lean.mkRecName type.name := rfl

/-- The production choice of an extra eliminator universe has exactly the two
universe arities admitted by `RecursorShape`. -/
theorem AddInductive.getRecLevelParams_length :
    (AddInductive.getRecLevelParams elimLevel lparams).length = lparams.length ∨
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel with
  | param u => simp [AddInductive.getRecLevelParams]
  | _ => simp [AddInductive.getRecLevelParams]

theorem AddInductive.getRecLevelParams_length_of_param
    (h : elimLevel.isParam = true) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

theorem AddInductive.getRecLevelParams_length_of_not_param
    (h : elimLevel.isParam = false) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

/-- `Expr.inferImplicit` changes only concrete binder annotations, which are
erased by the abstract expression translation.  In particular the abstract
recursor type proved before this production post-processing step remains the
translation of the type installed in the environment. -/
theorem TrExprS.inferImplicit
    (H : TrExprS env Us Δ e e') (numParams : Nat) (considerRange : Bool) :
    TrExprS env Us Δ (e.inferImplicit numParams considerRange) e' := by
  induction numParams generalizing e e' Δ with
  | zero => simpa [Expr.inferImplicit] using H
  | succ numParams ih =>
    cases e with
    | forallE name dom body bi =>
      cases H with
      | forallE hdomType hbodyType hdom hbody =>
        simp only [Expr.inferImplicit]
        exact .forallE hdomType hbodyType hdom
          (ih hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- Conversely, the annotation-only `inferImplicit` pass can be erased from
the concrete side of a translation derivation. -/
theorem TrExprS.of_inferImplicit
    (H : TrExprS env Us Δ (e.inferImplicit numParams considerRange) e') :
    TrExprS env Us Δ e e' := by
  induction numParams generalizing e e' Δ with
  | zero => simpa [Expr.inferImplicit] using H
  | succ numParams ih =>
    cases e with
    | forallE name dom body bi =>
      cases H with
      | forallE hdomType hbodyType hdom hbody =>
        exact .forallE hdomType hbodyType hdom (ih hbody)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => simpa [Expr.inferImplicit] using H

/-- A concrete expression consists of exactly `arity` leading forall binders
and the indicated residual body.  This deliberately forgets binder domains:
`RecursorShape` records them existentially but constrains their cardinality. -/
inductive Expr.ForallTelescope : Expr → Nat → Expr → Prop
  | nil (body : Expr) : ForallTelescope body 0 body
  | cons : ForallTelescope body arity result →
      ForallTelescope (.forallE name dom body bi) (arity + 1) result

theorem Expr.ForallTelescope.trans
    (Houter : Expr.ForallTelescope outer outerArity middle)
    (Hinner : Expr.ForallTelescope middle innerArity result) :
    Expr.ForallTelescope outer (outerArity + innerArity) result := by
  induction Houter with
  | nil => simpa using Hinner
  | @cons body outerArity middle name dom bi Houter ih =>
    have h := Expr.ForallTelescope.cons (name := name) (dom := dom)
      (bi := bi) (ih Hinner)
    rw [← Nat.add_right_comm outerArity innerArity 1]
    exact h

/-- Abstracting one retained free variable preserves telescope arity; the
residual body is abstracted below all telescope binders. -/
theorem Expr.ForallTelescope.abstract1
    (H : Expr.ForallTelescope outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstract1]
    apply Expr.ForallTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

/-- Simultaneous abstraction is the iterated form of `abstract1` and likewise
preserves the exact leading telescope. -/
theorem Expr.ForallTelescope.abstractList
    (H : Expr.ForallTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.ForallTelescope (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

theorem Expr.abstractList_fvar_of_not_mem
    (hmem : fv ∉ fvs) :
    (Expr.fvar fv).abstractList fvs k = .fvar fv := by
  induction fvs generalizing k with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mem_cons, not_or] at hmem
    have hne : head ≠ fv := Ne.symm hmem.1
    simp [Expr.abstractList, Expr.abstract1, hne, ih hmem.2]

@[simp] theorem Expr.abstractList_const
    (name : Name) (levels : List Level) (fvs : List FVarId) (k : Nat) :
    (Expr.const name levels).abstractList fvs k = .const name levels := by
  induction fvs with
  | nil => rfl
  | cons fv fvs ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

theorem Expr.abstractList_bvar_ge (fvs : List FVarId) (k n : Nat) :
    (Expr.bvar (k + n)).abstractList fvs k =
      .bvar (k + n + fvs.length) := by
  induction fvs generalizing n with
  | nil => simp
  | cons head tail ih =>
    simp only [Expr.abstractList]
    rw [show (Expr.bvar (k + n)).abstract1 head k = .bvar (k + n + 1) by
      simp [Expr.abstract1]]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

theorem Expr.abstractList_bvar_lt (fvs : List FVarId)
    (h : n < k) :
    (Expr.bvar n).abstractList fvs k = .bvar n := by
  induction fvs with
  | nil => simp
  | cons fv fvs ih =>
    simp [Expr.abstractList, Expr.abstract1, h, ih]

@[simp] theorem Expr.abstractList_app :
    (Expr.app fn arg).abstractList fvs k =
      .app (fn.abstractList fvs k) (arg.abstractList fvs k) := by
  induction fvs generalizing fn arg with
  | nil => simp
  | cons fv fvs ih =>
    simp [Expr.abstractList, Expr.abstract1, ih]

theorem Expr.abstractList_mkAppN :
    (mkAppN fn args).abstractList fvs k =
      mkAppN (fn.abstractList fvs k)
        (args.map fun arg => arg.abstractList fvs k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp

@[simp] theorem Expr.foldl_mkApp_eq (args : List Expr) (fn : Expr) :
    args.foldl Lean.mkApp fn = args.foldl Expr.app fn := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons, Lean.mkApp]
    exact ih (.app fn arg)

theorem Expr.abstractList_fvar_getElem
    (hnd : fvs.Nodup) (i : Nat) (hi : i < fvs.length) :
    (Expr.fvar fvs[i]).abstractList fvs k =
      .bvar (k + (fvs.length - 1 - i)) := by
  induction fvs generalizing i k with
  | nil => simp at hi
  | cons head tail ih =>
    simp only [List.nodup_cons] at hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Expr.abstractList]
      rw [show (Expr.fvar head).abstract1 head k = .bvar k by
        simp [Expr.abstract1]]
      simpa using Expr.abstractList_bvar_ge tail k 0
    | succ i =>
      have hiTail : i < tail.length := by simpa using hi
      have hne : tail[i] ≠ head := by
        intro heq
        apply hnd.1
        simpa [heq] using List.getElem_mem hiTail
      simp only [List.getElem_cons_succ, Expr.abstractList]
      rw [show (Expr.fvar tail[i]).abstract1 head k = .fvar tail[i] by
        simp [Expr.abstract1, Ne.symm hne]]
      rw [ih hnd.2 i hiTail (k := k)]
      congr 1
      simp only [List.length_cons]
      omega

theorem Expr.abstractList_fvarArray
    (fvs : List FVarId) (k : Nat) (hnd : fvs.Nodup) :
    ((fvs.map Expr.fvar).toArray.map fun e => e.abstractList fvs k) =
      (List.ofFn fun i : Fin fvs.length =>
        Expr.bvar (k + (fvs.length - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i (by simpa using hiLeft)

theorem Expr.abstractList_fvarArray_of_disjoint
    (xs binders : List FVarId) (k : Nat)
    (hdisjoint : ∀ fv, fv ∈ xs → fv ∉ binders) :
    ((xs.map Expr.fvar).toArray.map fun e => e.abstractList binders k) =
      (xs.map Expr.fvar).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < xs.length := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
    exact Expr.abstractList_fvar_of_not_mem <|
      hdisjoint xs[i] (List.getElem_mem hi)

theorem Expr.abstractList_indexBVars
    (binders : List FVarId) (n k : Nat) (hk : n < k) :
    ((List.ofFn fun i : Fin n =>
        Expr.bvar (1 + (n - 1 - i))).toArray.map
      fun e => e.abstractList binders k) =
    (List.ofFn fun i : Fin n =>
      Expr.bvar (1 + (n - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < n := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_ofFn]
    apply Expr.abstractList_bvar_lt
    omega

/-- Translation erases names and binder annotations but preserves the exact
number of leading forall binders. -/
theorem TrExprS.forallTelescope_shape
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' := by
  induction Htel generalizing Δ e' with
  | nil => exact ⟨[], e', rfl, rfl⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with ⟨domains, result', hlength, heq⟩
      exact ⟨ty' :: domains, result', by simp [hlength], by
        simp [VExpr.wrapForalls, heq]⟩

def abstractForallContext (domains : List VExpr) (Δ : VLCtx) : VLCtx :=
  (domains.reverse.map fun type => (none, .vlam type)) ++ Δ

@[simp] theorem abstractForallContext_append
    (outer inner : List VExpr) (Δ : VLCtx) :
    abstractForallContext inner (abstractForallContext outer Δ) =
      abstractForallContext (outer ++ inner) Δ := by
  simp [abstractForallContext, List.reverse_append, List.map_append,
    List.append_assoc]

/-- Abstracting a lambda telescope only prepends bound variables, so it
preserves absence of a selected set of constants in context values. -/
theorem VLCtx.NoIndConsts.abstractForallContext
    (H : VLCtx.NoIndConsts names Δ) :
    VLCtx.NoIndConsts names (abstractForallContext domains Δ) := by
  unfold Lean4Lean.VerifyInductive.abstractForallContext
  have go : ∀ (entries : List VExpr) {v : Nat ⊕ FVarId}
      {mapped type : VExpr},
      (VLCtx.find? ((entries.map fun type =>
        ((none, VLocalDecl.vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ) v =
        some (mapped, type)) →
      mapped.containsAnyConst names = false := by
    intro entries
    induction entries with
    | nil =>
      intro v mapped type hfind
      exact H hfind
    | cons type entries ih =>
      intro v mapped result hfind
      have hprefix : VLCtx.NoIndConsts names
          ((entries.map fun type =>
            ((none, VLocalDecl.vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ) := by
        intro v mapped result hfind
        exact ih hfind
      have hcons : VLCtx.NoIndConsts names
          ((none, VLocalDecl.vlam type) ::
            (entries.map fun type =>
              ((none, VLocalDecl.vlam type) :
                Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ) :=
        VLCtx.NoIndConsts.cons
          (ofv := none) (d := VLocalDecl.vlam type) hprefix (by rfl)
      exact hcons (by simpa only [List.map_cons, List.cons_append] using hfind)
  intro v mapped type hfind
  exact go domains.reverse hfind

/-- Prepending the abstract lambda domains is the canonical bound-variable
lift of the retained outer context. -/
theorem abstractForallContext.bvLift
    (domains : List VExpr) (Δ : VLCtx) :
    VLCtx.BVLift Δ (abstractForallContext domains Δ)
      domains.length 0 domains.length 0 := by
  have hprefix : ∀ (pref : List VExpr),
      VLCtx.BVLift Δ
        ((pref.map fun type => (none, .vlam type)) ++ Δ)
        pref.length 0 pref.length 0 := by
    intro pref
    induction pref with
    | nil => exact .refl
    | cons type pref ih =>
      simpa [VLocalDecl.depth, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        VLCtx.BVLift.skip (.vlam type) ih
  simpa [abstractForallContext] using hprefix domains.reverse

/-- Strengthened telescope inversion retaining the exact abstract context in
which the concrete residual is translated. -/
theorem TrExprS.forallTelescope_shape_with_context
    (Htel : Expr.ForallTelescope e arity result)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains result', domains.length = arity ∧
      e' = VExpr.wrapForalls domains result' ∧
      TrExprS env Us (abstractForallContext domains Δ) result result' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl, by simpa [abstractForallContext] using Htr⟩
  | @cons body arity result name dom bi Htel ih =>
    cases Htr with
    | @forallE ty' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with ⟨domains, result', hlength, heq, hresult⟩
      refine ⟨ty' :: domains, result', by simp [hlength], ?_, ?_⟩
      · simp [VExpr.wrapForalls, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresult

/-- A nonempty translated concrete forall telescope is an abstract type.
The translation constructor already carries exactly the two typing premises
needed for abstract forall formation. -/
theorem TrExprS.isType_of_forallTelescope
    (Htel : Expr.ForallTelescope e arity result)
    (hpositive : 0 < arity)
    (Htr : TrExprS env Us Δ e e') :
    env.IsType Us.length Δ.toCtx e' := by
  cases Htel with
  | nil => omega
  | cons _ =>
    cases Htr with
    | forallE hdomType hbodyType _ _ =>
      exact VEnv.IsType.forallE hdomType hbodyType

private theorem List.exists_append_five_of_length_eq
    (xs : List α) (a b c d e : Nat)
    (h : xs.length = a + b + c + d + e) :
    ∃ as bs cs ds es,
      xs = as ++ bs ++ cs ++ ds ++ es ∧
      as.length = a ∧ bs.length = b ∧ cs.length = c ∧
      ds.length = d ∧ es.length = e := by
  let as := xs.take a
  let restA := xs.drop a
  let bs := restA.take b
  let restB := restA.drop b
  let cs := restB.take c
  let restC := restB.drop c
  let ds := restC.take d
  let es := restC.drop d
  refine ⟨as, bs, cs, ds, es, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [as, bs, cs, ds, es, restA, restB, restC]
    symm
    simp only [List.append_assoc]
    rw [List.take_append_drop d, List.take_append_drop c,
      List.take_append_drop b, List.take_append_drop a]
  all_goals simp [as, bs, cs, ds, es, restA, restB, restC, h] <;> omega

private theorem vlamPrefix_find_bvar
    (pref : List VExpr) (Δ : VLCtx) (i : Nat) (hi : i < pref.length) :
    ∃ type, VLCtx.find? ((pref.map fun type =>
      ((none, VLocalDecl.vlam type) :
        Option (FVarId × List FVarId) × VLocalDecl)) ++ Δ)
      (Sum.inl i) = some (VExpr.bvar i, type) := by
  induction pref generalizing i with
  | nil => simp at hi
  | cons type pref ih =>
    cases i with
    | zero =>
      refine ⟨type.lift, ?_⟩
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
    | succ i =>
      have hi' : i < pref.length := by simpa using hi
      rcases ih i hi' with ⟨found, hfind⟩
      refine ⟨found.lift, ?_⟩
      simp only [List.map_cons, List.cons_append, VLCtx.find?, VLCtx.next]
      rw [hfind]
      simp [VLocalDecl.depth, VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm]

theorem abstractForallContext.find?_bvar
    (domains : List VExpr) (Δ : VLCtx) (i : Nat)
    (hi : i < domains.length) :
    ∃ type, VLCtx.find? (abstractForallContext domains Δ) (.inl i) =
      some (.bvar i, type) := by
  apply vlamPrefix_find_bvar domains.reverse Δ i
  simpa using hi

theorem TrExprS.bvar_eq_of_abstractForallContext
    (H : TrExprS env Us (abstractForallContext domains Δ) (.bvar i) out)
    (hi : i < domains.length) : out = .bvar i := by
  cases H with
  | bvar hfind =>
    rcases abstractForallContext.find?_bvar domains Δ i hi with
      ⟨type, hcanonical⟩
    rw [hcanonical] at hfind
    exact (congrArg Prod.fst (Option.some.inj hfind)).symm

private theorem TrExprS.foldl_bvars_eq
    (domains : List VExpr) (Δ : VLCtx)
    (args : List Nat) (hargs : ∀ i ∈ args, i < domains.length)
    (base : Expr) (vbase : VExpr)
    (hbase : ∀ out, TrExprS env Us (abstractForallContext domains Δ)
      base out → out = vbase)
    (H : TrExprS env Us (abstractForallContext domains Δ)
      (args.foldl (fun fn i => .app fn (.bvar i)) base) out) :
    out = args.foldl (fun fn i => .app fn (.bvar i)) vbase := by
  induction args generalizing base vbase with
  | nil => exact hbase out H
  | cons i args ih =>
    apply ih (fun j hj => hargs j (by simp [hj]))
      (.app base (.bvar i)) (.app vbase (.bvar i))
    · intro result Hresult
      cases Hresult with
      | app _ _ hfn harg =>
        rw [hbase _ hfn,
          TrExprS.bvar_eq_of_abstractForallContext harg
            (hargs i (by simp))]
    · exact H

/-- Binding a list of ordinary local declarations creates one concrete forall
per selected declaration and leaves precisely the simultaneous abstraction of
the selected free variables as its residual body. -/
theorem LocalContext.mkBindingList_forallTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (LocalContext.mkBindingList false lctx fvs body)
      fvs.length (body.abstractList fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.ForallTelescope
        (LocalContext.mkBindingList.go false lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingList.go]
      have htail := ih
        (LocalContext.mkBindingList1 false lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.ForallTelescope
          (LocalContext.mkBindingList1 false lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1, hfind]
        exact Expr.ForallTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingList, LocalContext.mkBindingList.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractList fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

/-- The production `LocalContext.mkForall` interface specialized to an
explicit list of free variables known to denote ordinary declarations. -/
theorem LocalContext.mkForall_fvars_forallTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (lctx.mkForall (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
  exact LocalContext.mkBindingList_forallTelescope hdecl

/-- A concrete expression consists of exactly `arity` leading lambda binders
and the indicated residual body. -/
inductive Expr.LambdaTelescope : Expr → Nat → Expr → Prop
  | nil (body : Expr) : LambdaTelescope body 0 body
  | cons : LambdaTelescope body arity result →
      LambdaTelescope (.lam name dom body bi) (arity + 1) result

theorem Expr.LambdaTelescope.trans
    (Houter : Expr.LambdaTelescope outer outerArity middle)
    (Hinner : Expr.LambdaTelescope middle innerArity result) :
    Expr.LambdaTelescope outer (outerArity + innerArity) result := by
  induction Houter with
  | nil => simpa using Hinner
  | @cons body outerArity middle name dom bi Houter ih =>
    have h := Expr.LambdaTelescope.cons (name := name) (dom := dom)
      (bi := bi) (ih Hinner)
    rw [← Nat.add_right_comm outerArity innerArity 1]
    exact h

theorem Expr.LambdaTelescope.abstract1
    (H : Expr.LambdaTelescope outer arity result)
    (fv : FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstract1 fv k) arity
      (result.abstract1 fv (k + arity)) := by
  induction H generalizing k with
  | nil => exact .nil _
  | cons H ih =>
    simp only [Expr.abstract1]
    apply Expr.LambdaTelescope.cons
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem Expr.LambdaTelescope.abstractList
    (H : Expr.LambdaTelescope outer arity result)
    (fvs : List FVarId) (k : Nat := 0) :
    Expr.LambdaTelescope (outer.abstractList fvs k) arity
      (result.abstractList fvs (k + arity)) := by
  induction fvs generalizing outer result k with
  | nil => simpa using H
  | cons fv fvs ih =>
    simp only [Expr.abstractList]
    exact ih (H.abstract1 fv k) k

/-- Translation of a lambda telescope retains its arity and exposes the
residual translation beneath precisely the corresponding abstract binders. -/
theorem TrExprS.lambdaTelescope_shape_with_context
    (Htel : Expr.LambdaTelescope e arity residual)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains residual', domains.length = arity ∧
      e' = VExpr.wrapLams domains residual' ∧
      TrExprS env Us (abstractForallContext domains Δ)
        residual residual' := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl,
      by simpa [abstractForallContext] using Htr⟩
  | @cons body arity residual name dom bi Htel ih =>
    cases Htr with
    | @lam dom' body' =>
      rename_i _ _ _ hbody
      rcases ih hbody with
        ⟨domains, residual', hlength, heq, hresidual⟩
      refine ⟨dom' :: domains, residual', by simp [hlength], ?_, ?_⟩
      · simp [VExpr.wrapLams, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresidual

/-- Freshness-aware lambda-telescope inversion. Each translated binder domain
is retained as recursor-free at the point where the translation constructor
exposes it; the residual remains translated in the exact abstract context. -/
theorem TrExprS.lambdaTelescope_shape_with_context_noFresh
    (hfresh : ∀ name ∈ names, env.constants name = none)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (Htel : Expr.LambdaTelescope e arity residual)
    (Htr : TrExprS env Us Δ e e') :
    ∃ domains residual', domains.length = arity ∧
      e' = VExpr.wrapLams domains residual' ∧
      TrExprS env Us (abstractForallContext domains Δ)
        residual residual' ∧
      ∀ dom ∈ domains, dom.containsAnyConst names = false := by
  induction Htel generalizing Δ e' with
  | nil =>
    exact ⟨[], e', rfl, rfl,
      by simpa [abstractForallContext] using Htr, by simp⟩
  | @cons body arity residual name dom bi Htel ih =>
    cases Htr with
    | @lam dom' body' =>
      rename_i _ hdom hbody
      have hctx' : VLCtx.NoIndConsts names
          ((none, VLocalDecl.vlam dom') :: Δ) :=
        VLCtx.NoIndConsts.cons hctx (by rfl)
      rcases ih hctx' hbody with
        ⟨domains, residual', hlength, heq, hresidual, hfree⟩
      refine ⟨dom' :: domains, residual', by simp [hlength], ?_, ?_, ?_⟩
      · simp [VExpr.wrapLams, heq]
      · simpa [abstractForallContext, List.map_append, List.append_assoc]
          using hresidual
      · intro current hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact checkPositivityStep.TrExprS.noFreshConsts
            hfresh hctx hproj hdom
        · exact hfree current hmem

/-- Binding ordinary local declarations with `mkLambda` creates one concrete
lambda per selected declaration and leaves simultaneous abstraction of those
free variables as the residual body. -/
theorem LocalContext.mkBindingList_lambdaTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (LocalContext.mkBindingList true lctx fvs body)
      fvs.length (body.abstractList fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.LambdaTelescope
        (LocalContext.mkBindingList.go true lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingList.go]
      have htail := ih
        (LocalContext.mkBindingList1 true lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.LambdaTelescope
          (LocalContext.mkBindingList1 true lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1, hfind]
        exact Expr.LambdaTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingList, LocalContext.mkBindingList.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractList fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

/-- The production `LocalContext.mkLambda` interface specialized to an
explicit array of ordinary local free variables. -/
theorem LocalContext.mkLambda_fvars_lambdaTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eq]
  exact LocalContext.mkBindingList_lambdaTelescope hdecl

/-- With distinct selected declarations, closing a concatenated free-variable
list is exactly the same as closing the suffix and then the prefix. -/
theorem LocalContext.mkBindingList_append
    (hdecl : ∀ fv ∈ xs ++ ys, ∃ decl, lctx.find? fv = some decl)
    (hnodup : (xs ++ ys).Nodup) :
    LocalContext.mkBindingList isLambda lctx (xs ++ ys) body =
      LocalContext.mkBindingList isLambda lctx xs
        (LocalContext.mkBindingList isLambda lctx ys body) := by
  rcases List.nodup_append.mp hnodup with ⟨hxs, hys, _⟩
  have hdeclXs : ∀ fv ∈ xs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    exact hdecl fv (List.mem_append_left ys hfv)
  have hdeclYs : ∀ fv ∈ ys, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    exact hdecl fv (List.mem_append_right xs hfv)
  rw [LocalContext.mkBindingList_eq_fold hdecl hnodup,
    LocalContext.mkBindingList_eq_fold hdeclXs hxs,
    LocalContext.mkBindingList_eq_fold hdeclYs hys,
    List.foldr_append]

theorem LocalContext.mkBindingList_append_four
    (hdecl : ∀ fv ∈ ((as ++ bs) ++ cs) ++ ds,
      ∃ decl, lctx.find? fv = some decl)
    (hnodup : (((as ++ bs) ++ cs) ++ ds).Nodup) :
    LocalContext.mkBindingList isLambda lctx
        (((as ++ bs) ++ cs) ++ ds) body =
      LocalContext.mkBindingList isLambda lctx as
        (LocalContext.mkBindingList isLambda lctx bs
          (LocalContext.mkBindingList isLambda lctx cs
            (LocalContext.mkBindingList isLambda lctx ds body))) := by
  have habcd := List.nodup_append.mp hnodup
  have habc := List.nodup_append.mp habcd.1
  have hab := List.nodup_append.mp habc.1
  have hasDecl : ∀ fv ∈ as, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hbsDecl : ∀ fv ∈ bs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hcsDecl : ∀ fv ∈ cs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hdsDecl : ∀ fv ∈ ds, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  rw [LocalContext.mkBindingList_eq_fold hdecl hnodup,
    LocalContext.mkBindingList_eq_fold hasDecl hab.1,
    LocalContext.mkBindingList_eq_fold hbsDecl hab.2.1,
    LocalContext.mkBindingList_eq_fold hcsDecl habc.2.1,
    LocalContext.mkBindingList_eq_fold hdsDecl habcd.2.1]
  simp only [List.foldr_append]

/-- A selected executable array consists solely of ordinary free-variable
declarations in the retained local context. -/
structure LocalForallSelection (lctx : LocalContext) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  declarations : ∀ fv ∈ fvars, ∃ index name type bi kind,
    lctx.find? fv = some (.cdecl index fv name type bi kind)

/-- Operational form of a local selection, convenient to preserve while the
reader context is extended by generated binders. -/
structure BoundFVarArray (c : AddInductive.Context) (xs : Array Expr) where
  fvars : List FVarId
  expressions : xs = (fvars.map Expr.fvar).toArray
  members : ∀ fv ∈ fvars, fv ∈ c.lctx.fvars

def BindingContextLE (c c' : AddInductive.Context) : Prop :=
  c.lctx.fvars ⊆ c'.lctx.fvars

theorem BindingContextLE.refl (c : AddInductive.Context) :
    BindingContextLE c c := fun _ => id

theorem BindingContextLE.trans
    (H₁ : BindingContextLE c₁ c₂) (H₂ : BindingContextLE c₂ c₃) :
    BindingContextLE c₁ c₃ := fun _ h => H₂ (H₁ h)

theorem BindingContextLE.withLocalDecl
    (c : AddInductive.Context) (name : Name) (ty : Expr) (bi : BinderInfo) :
    BindingContextLE c { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } := by
  intro fv hfv
  simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
    List.map_cons, LocalDecl.fvarId, List.mem_cons]
  exact Or.inr hfv

def BoundFVarArray.empty (c : AddInductive.Context) :
    BoundFVarArray c #[] where
  fvars := []
  expressions := rfl
  members _ h := by simp at h

def BoundFVarArray.weaken
    (H : BoundFVarArray c xs) (name : Name) (ty : Expr) (bi : BinderInfo) :
    BoundFVarArray { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } xs where
  fvars := H.fvars
  expressions := H.expressions
  members := by
    intro fv hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    exact Or.inr (H.members fv hfv)

def BoundFVarArray.mono
    (H : BoundFVarArray c xs) (hle : BindingContextLE c c') :
    BoundFVarArray c' xs where
  fvars := H.fvars
  expressions := H.expressions
  members fv hfv := hle (H.members fv hfv)

def BoundFVarArray.pushCurrent
    (H : BoundFVarArray c xs) (name : Name) (ty : Expr) (bi : BinderInfo) :
    BoundFVarArray { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  fvars := H.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]
  expressions := calc
    xs.push (.fvar ⟨c.ngen.curr⟩) =
        ((H.fvars.map Expr.fvar).toArray).push (.fvar ⟨c.ngen.curr⟩) :=
      congrArg (fun ys => ys.push (.fvar ⟨c.ngen.curr⟩)) H.expressions
    _ = ((H.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]).map Expr.fvar).toArray := by
      simp
  members := by
    intro fv hfv
    simp only [List.mem_append, List.mem_singleton] at hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    rcases hfv with hfv | rfl
    · exact Or.inr (H.members fv hfv)
    · exact Or.inl rfl

def BoundFVarArray.toLocalForallSelection
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c) :
    LocalForallSelection c.lctx xs where
  fvars := H.fvars
  expressions := H.expressions
  declarations fv hfv := Hc.findCDecl fv (H.members fv hfv)

def BoundFVarArray.append
    (H₁ : BoundFVarArray c xs) (H₂ : BoundFVarArray c ys) :
    BoundFVarArray c (xs ++ ys) where
  fvars := H₁.fvars ++ H₂.fvars
  expressions := by
    simp [H₁.expressions, H₂.expressions]
  members := by
    intro fv hfv
    simp only [List.mem_append] at hfv
    rcases hfv with hfv | hfv
    · exact H₁.members fv hfv
    · exact H₂.members fv hfv

/-- A retained array introduced strictly after `root`. Besides recording that
its entries remain selectable, this packages the two facts needed to combine
it with selections already present at `root`: its entries are distinct and
none of them occurred in the root context. -/
structure FreshBoundFVarArray (root c : AddInductive.Context)
    (xs : Array Expr) extends BoundFVarArray c xs where
  nodup : toBoundFVarArray.fvars.Nodup
  fresh : ∀ fv ∈ toBoundFVarArray.fvars, fv ∉ root.lctx.fvars

def FreshBoundFVarArray.empty (c : AddInductive.Context) :
    FreshBoundFVarArray c c #[] where
  toBoundFVarArray := BoundFVarArray.empty c
  nodup := List.nodup_nil
  fresh _ h := nomatch h

def FreshBoundFVarArray.pushCurrent
    (H : FreshBoundFVarArray root c xs)
    (Hc : BindingContextWF c) (Hroot : BindingContextLE root c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FreshBoundFVarArray root { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toBoundFVarArray := H.toBoundFVarArray.pushCurrent name ty bi
  nodup := by
    rw [show (H.toBoundFVarArray.pushCurrent name ty bi).fvars =
      H.toBoundFVarArray.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)] from rfl]
    apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro fv hfv fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact fun heq => Hc.current_not_mem <| heq ▸
      H.toBoundFVarArray.members fv hfv
  fresh := by
    intro fv hfv
    change fv ∈ H.toBoundFVarArray.fvars ++
      [(⟨c.ngen.curr⟩ : FVarId)] at hfv
    simp only [List.mem_append, List.mem_singleton] at hfv
    rcases hfv with hfv | rfl
    · exact H.fresh fv hfv
    · intro hroot
      exact Hc.current_not_mem (Hroot hroot)

def FreshBoundFVarArray.weaken
    (H : FreshBoundFVarArray root c xs)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FreshBoundFVarArray root { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } xs where
  toBoundFVarArray := H.toBoundFVarArray.weaken name ty bi
  nodup := H.nodup
  fresh := H.fresh

def BoundFVarArray.get
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    BoundFVarArray c #[xs[i]] := by
  rcases H with ⟨fvars, rfl, members⟩
  let fv := fvars[i]'(by simpa using hi)
  refine {
    fvars := [fv]
    expressions := ?_
    members := ?_
  }
  · simp [fv]
  · intro fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact members fv (List.getElem_mem (by simpa using hi))

/-- Every indexed entry of a bound-fvar array is literally a free variable
present in the retained executable local context. -/
theorem BoundFVarArray.get_eq_fvar
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    ∃ fv, xs[i] = .fvar fv ∧ fv ∈ c.lctx.fvars := by
  rcases H with ⟨fvars, rfl, members⟩
  have hifvars : i < fvars.length := by simpa using hi
  refine ⟨fvars[i], ?_, members fvars[i] (List.getElem_mem hifvars)⟩
  simp

theorem BoundFVarArray.getElem_eq_fvar
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    ∃ hiFvars : i < H.fvars.length,
      xs[i] = .fvar H.fvars[i] := by
  rcases H with ⟨fvars, rfl, members⟩
  refine ⟨by simpa using hi, by simp⟩

theorem BoundFVarArray.length_fvars
    (H : BoundFVarArray c xs) : H.fvars.length = xs.size := by
  have := congrArg Array.size H.expressions
  simpa using this.symm

theorem BoundFVarArray.get_fvars_sublist
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    (H.get i hi).fvars <+ H.fvars := by
  rcases H with ⟨fvars, rfl, members⟩
  simp [BoundFVarArray.get, List.getElem_mem]

theorem BoundFVarArray.fvars_eq
    (H₁ : BoundFVarArray c xs) (H₂ : BoundFVarArray c ys)
    (hxy : xs = ys) : H₁.fvars = H₂.fvars := by
  have harr : (H₁.fvars.map Expr.fvar).toArray =
      (H₂.fvars.map Expr.fvar).toArray := by
    rw [← H₁.expressions, ← H₂.expressions, hxy]
  have hlist : H₁.fvars.map Expr.fvar = H₂.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harr
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist

/-- Ordered selection of one bound-fvar array from another implies the
corresponding inclusion of retained free-variable identifiers. -/
theorem BoundFVarArray.fvars_subset_of_sublist
    (H₁ : BoundFVarArray c xs) (H₂ : BoundFVarArray c ys)
    (hxy : xs.toList.Sublist ys.toList) : H₁.fvars ⊆ H₂.fvars := by
  intro fv hfv
  have hx : Expr.fvar fv ∈ xs.toList := by
    rw [H₁.expressions]
    simpa using hfv
  have hy : Expr.fvar fv ∈ ys.toList := hxy.subset hx
  rw [H₂.expressions] at hy
  simpa using hy

def recursorFVarId : Expr → FVarId
  | .fvar fv => fv
  | _ => default

def ExprArrayFVarIds (xs : Array Expr) : List FVarId :=
  xs.toList.map recursorFVarId

theorem BoundFVarArray.exprArrayFVarIds
    (H : BoundFVarArray c xs) : ExprArrayFVarIds xs = H.fvars := by
  calc
    ExprArrayFVarIds xs =
        ExprArrayFVarIds ((H.fvars.map Expr.fvar).toArray) :=
      congrArg ExprArrayFVarIds H.expressions
    _ = H.fvars := by
      simp [ExprArrayFVarIds, recursorFVarId, Function.comp_def]

/-- All local free-variable arrays retained by the executable recursor-info
records, aligned with the production array operations. -/
structure RecInfoBindings (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) where
  motives : BoundFVarArray c (recInfos.map (·.motive))
  majors : BoundFVarArray c (recInfos.map (·.major))
  indices : ∀ i (hi : i < recInfos.size),
    BoundFVarArray c recInfos[i]!.indices
  minors : ∀ i (hi : i < recInfos.size),
    BoundFVarArray c recInfos[i]!.minors

def RecInfoBindings.flatMinors
    (H : RecInfoBindings c recInfos) :
    BoundFVarArray c (recInfos.flatMap (·.minors)) where
  fvars := (List.ofFn fun i : Fin recInfos.size =>
    (H.minors i i.isLt).fvars).flatten
  expressions := by
    rw [← Array.toList_inj]
    simp only [Array.toList_flatMap, List.map_flatten]
    rw [← List.ofFn_getElem (xs := recInfos.toList)]
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      simpa [Array.getElem!_eq_getD, Array.getD, hn] using
        congrArg Array.toList (H.minors n hn).expressions
  members := by
    intro fv hfv
    simp only [List.mem_flatten, List.mem_ofFn] at hfv
    rcases hfv with ⟨fvs, ⟨i, rfl⟩, hfv⟩
    exact (H.minors i i.isLt).members fv hfv

def RecInfoBindings.flatIndices
    (H : RecInfoBindings c recInfos) :
    BoundFVarArray c (recInfos.flatMap (·.indices)) where
  fvars := (List.ofFn fun i : Fin recInfos.size =>
    (H.indices i i.isLt).fvars).flatten
  expressions := by
    rw [← Array.toList_inj]
    simp only [Array.toList_flatMap, List.map_flatten]
    rw [← List.ofFn_getElem (xs := recInfos.toList)]
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      simpa [Array.getElem!_eq_getD, Array.getD, hn] using
        congrArg Array.toList (H.indices n hn).expressions
  members := by
    intro fv hfv
    simp only [List.mem_flatten, List.mem_ofFn] at hfv
    rcases hfv with ⟨fvs, ⟨i, rfl⟩, hfv⟩
    exact (H.indices i i.isLt).members fv hfv

/-- All binder identities retained for recursor generation, in the category
order used by the generated telescope. Keeping this global list distinct is
stronger than the per-owner fact needed by any one recursor. -/
def RecInfoBindings.allFvars
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) : List FVarId :=
  ExprArrayFVarIds stats.params ++
    (ExprArrayFVarIds (recInfos.map (·.motive)) ++
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
        (ExprArrayFVarIds (recInfos.flatMap (·.indices)) ++
          ExprArrayFVarIds (recInfos.map (·.major)))))

theorem RecInfoBindings.allFvars_eq
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) :
    H.allFvars Hparams =
      Hparams.fvars ++
        (H.motives.fvars ++
          (H.flatMinors.fvars ++ (H.flatIndices.fvars ++ H.majors.fvars))) := by
  unfold RecInfoBindings.allFvars
  rw [Hparams.exprArrayFVarIds, H.motives.exprArrayFVarIds,
    H.flatMinors.exprArrayFVarIds, H.flatIndices.exprArrayFVarIds,
    H.majors.exprArrayFVarIds]

def RecInfoBindings.NoAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) : Prop :=
  (H.allFvars Hparams).Nodup

theorem RecInfoBindings.allFvars_members
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) :
    ∀ fv ∈ H.allFvars Hparams, fv ∈ c.lctx.fvars := by
  intro fv hfv
  rw [H.allFvars_eq Hparams] at hfv
  simp only [List.mem_append] at hfv
  rcases hfv with hp | hm | hmi | hi | hma
  · exact Hparams.members fv hp
  · exact H.motives.members fv hm
  · exact H.flatMinors.members fv hmi
  · exact H.flatIndices.members fv hi
  · exact H.majors.members fv hma

def RecInfoBindings.major
    (H : RecInfoBindings c recInfos) (i : Nat) (hi : i < recInfos.size) :
    BoundFVarArray c #[recInfos[i]!.major] := by
  have hsize : H.majors.fvars.length = recInfos.size := by
    have h := congrArg Array.size H.majors.expressions
    simpa using h.symm
  let fv := H.majors.fvars[i]'(by simpa [hsize] using hi)
  refine {
    fvars := [fv]
    expressions := ?_
    members := ?_
  }
  · apply congrArg (fun e => #[e])
    have hget := congrArg (fun xs => xs[i]!) H.majors.expressions
    simpa [fv, Array.getElem!_eq_getD, Array.getD, hi, hsize] using hget
  · intro fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact H.majors.members fv (List.getElem_mem (by simpa [hsize] using hi))

/-- The five executable binder groups used to build one production recursor
type, all selected from the same retained local context. -/
structure RecursorLocalSelections (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) where
  params : LocalForallSelection c.lctx stats.params
  motives : LocalForallSelection c.lctx (recInfos.map (·.motive))
  minors : LocalForallSelection c.lctx (recInfos.flatMap (·.minors))
  indices : LocalForallSelection c.lctx recInfos[ownerIdx]!.indices
  major : LocalForallSelection c.lctx #[recInfos[ownerIdx]!.major]

def RecursorLocalSelections.allFvars
    (H : RecursorLocalSelections c stats recInfos ownerIdx) : List FVarId :=
  H.params.fvars ++
    (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))

def RecursorLocalSelections.NoAlias
    (H : RecursorLocalSelections c stats recInfos ownerIdx) : Prop :=
  H.allFvars.Nodup

structure RecursorLocalSelections.NoAliasParts
    (H : RecursorLocalSelections c stats recInfos ownerIdx) : Prop where
  params : H.params.fvars.Nodup
  motives : H.motives.fvars.Nodup
  minors : H.minors.fvars.Nodup
  indices : H.indices.fvars.Nodup
  major : H.major.fvars.Nodup
  params_later : ∀ fv ∈ H.params.fvars,
    ∀ fv' ∈ H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)), fv ≠ fv'
  motives_later : ∀ fv ∈ H.motives.fvars,
    ∀ fv' ∈ H.minors.fvars ++
      (H.indices.fvars ++ H.major.fvars), fv ≠ fv'
  minors_later : ∀ fv ∈ H.minors.fvars,
    ∀ fv' ∈ H.indices.fvars ++ H.major.fvars, fv ≠ fv'
  indices_major : ∀ fv ∈ H.indices.fvars,
    ∀ fv' ∈ H.major.fvars, fv ≠ fv'

theorem RecursorLocalSelections.NoAlias.parts
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (h : H.NoAlias) : H.NoAliasParts := by
  unfold RecursorLocalSelections.NoAlias
    RecursorLocalSelections.allFvars at h
  rcases List.nodup_append.mp h with ⟨hp, hrest, hpLater⟩
  rcases List.nodup_append.mp hrest with ⟨hm, hrest, hmLater⟩
  rcases List.nodup_append.mp hrest with ⟨hmi, hrest, hmiLater⟩
  rcases List.nodup_append.mp hrest with ⟨hi, hma, hiMajor⟩
  exact ⟨hp, hm, hmi, hi, hma, hpLater, hmLater, hmiLater, hiMajor⟩

def RecInfoBindings.toRecursorLocalSelections
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (ownerIdx : Nat) (howner : ownerIdx < recInfos.size) :
    RecursorLocalSelections c stats recInfos ownerIdx where
  params := Hparams.toLocalForallSelection Hc
  motives := H.motives.toLocalForallSelection Hc
  minors := H.flatMinors.toLocalForallSelection Hc
  indices := (H.indices ownerIdx howner).toLocalForallSelection Hc
  major := (H.major ownerIdx howner).toLocalForallSelection Hc

theorem RecInfoBindings.selectionNoAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams)
    (ownerIdx : Nat) (howner : ownerIdx < recInfos.size) :
    (H.toRecursorLocalSelections Hc Hparams ownerIdx howner).NoAlias := by
  let rows := List.ofFn fun i : Fin recInfos.size =>
    (H.indices i i.isLt).fvars
  have hrowMem : (H.indices ownerIdx howner).fvars ∈ rows := by
    simp only [rows, List.mem_ofFn]
    exact ⟨⟨ownerIdx, howner⟩, rfl⟩
  have hindices : (H.indices ownerIdx howner).fvars <+
      H.flatIndices.fvars := by
    exact List.sublist_flatten_of_mem hrowMem
  have hmajor : (H.major ownerIdx howner).fvars <+ H.majors.fvars := by
    have himap : ownerIdx < (recInfos.map (·.major)).size := by
      simpa using howner
    let Hget := H.majors.get ownerIdx himap
    have heq : #[recInfos[ownerIdx]!.major] =
        #[(recInfos.map (·.major))[ownerIdx]] := by
      simp [Array.getElem!_eq_getD, Array.getD, howner]
    rw [BoundFVarArray.fvars_eq (H.major ownerIdx howner) Hget heq]
    exact BoundFVarArray.get_fvars_sublist _ _ _
  have hsub :
      Hparams.fvars ++
        (H.motives.fvars ++
          (H.flatMinors.fvars ++
            ((H.indices ownerIdx howner).fvars ++
              (H.major ownerIdx howner).fvars))) <+
      H.allFvars Hparams :=
    H.allFvars_eq Hparams ▸
      ((List.Sublist.refl Hparams.fvars).append <|
        (List.Sublist.refl H.motives.fvars).append <|
          (List.Sublist.refl H.flatMinors.fvars).append <|
            hindices.append hmajor)
  apply hnoalias.sublist hsub

/-- The replayed index telescope of every accumulated recursor frame has the
arity recorded by the checked inductive header. -/
def RecInfoArities (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size →
    recInfos[i]!.indices.size = stats.nindices[i]!

theorem RecInfoArities.empty (stats : AddInductive.InductiveStats) :
    RecInfoArities stats #[] := by
  intro i hi
  simp at hi

theorem RecInfoArities.push
    (H : RecInfoArities stats recInfos)
    (hnew : indices.size = stats.nindices[recInfos.size]!) :
    RecInfoArities stats (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simpa using hnew
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

def RecInfoMinorsEmpty (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size → recInfos[i]!.minors.size = 0

theorem RecInfoMinorsEmpty.empty : RecInfoMinorsEmpty #[] := by
  intro i hi
  simp at hi

theorem RecInfoMinorsEmpty.push
    (H : RecInfoMinorsEmpty recInfos) :
    RecInfoMinorsEmpty (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simp
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

theorem RecInfoArities.modifyMinors
    (H : RecInfoArities stats recInfos) (dIdx : Nat)
    (f : Array Expr → Array Expr) :
    RecInfoArities stats (recInfos.modify dIdx fun info =>
      { info with minors := f info.minors }) := by
  intro i hi
  have hiOld : i < recInfos.size := by simpa using hi
  by_cases hdi : dIdx = i
  · subst i
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
    exact H dIdx hiOld
  · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
      hiOld hdi]
    exact H i hiOld

def RecInfoBindings.empty (c : AddInductive.Context) :
    RecInfoBindings c #[] where
  motives := by simpa using BoundFVarArray.empty c
  majors := by simpa using BoundFVarArray.empty c
  indices i hi := by simp at hi
  minors i hi := by simp at hi

def RecInfoBindings.mono
    (H : RecInfoBindings c recInfos) (hle : BindingContextLE c c') :
    RecInfoBindings c' recInfos where
  motives := H.motives.mono hle
  majors := H.majors.mono hle
  indices i hi := (H.indices i hi).mono hle
  minors i hi := (H.minors i hi).mono hle

theorem RecInfoBindings.empty_noAlias
    {stats : AddInductive.InductiveStats}
    (c : AddInductive.Context) (Hparams : BoundFVarArray c stats.params)
    (hparams : Hparams.fvars.Nodup) :
    (RecInfoBindings.empty c).NoAlias Hparams := by
  have hm : (RecInfoBindings.empty c).motives.fvars = [] := by
    exact BoundFVarArray.fvars_eq (RecInfoBindings.empty c).motives
      (BoundFVarArray.empty c) (by simp)
  have hma : (RecInfoBindings.empty c).majors.fvars = [] := by
    exact BoundFVarArray.fvars_eq (RecInfoBindings.empty c).majors
      (BoundFVarArray.empty c) (by simp)
  unfold RecInfoBindings.NoAlias RecInfoBindings.allFvars
  rw [Hparams.exprArrayFVarIds]
  simpa [ExprArrayFVarIds] using hparams

theorem RecInfoBindings.mono_noAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos) (Hparams : BoundFVarArray c stats.params)
    (hle : BindingContextLE c c') (hnoalias : H.NoAlias Hparams) :
    (H.mono hle).NoAlias (Hparams.mono hle) := by
  simpa [RecInfoBindings.NoAlias, RecInfoBindings.allFvars,
    RecInfoBindings.mono, BoundFVarArray.mono,
    RecInfoBindings.flatMinors, RecInfoBindings.flatIndices] using hnoalias

def RecInfoBindings.pushFrame
    {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (hle : BindingContextLE c cIndices)
    (Hindices : BoundFVarArray cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    RecInfoBindings cMotive (recInfos.push {
      motive := .fvar ⟨cMajor.ngen.curr⟩
      minors := #[]
      indices
      major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
  dsimp only
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  let cMotive : AddInductive.Context := { cMajor with
    ngen := cMajor.ngen.next
    lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
      motiveName motiveTy motiveBi }
  let hMajor := BindingContextLE.withLocalDecl cIndices
    majorName majorTy majorBi
  let hMotive := BindingContextLE.withLocalDecl cMajor
    motiveName motiveTy motiveBi
  let hall : BindingContextLE c cMotive := hle.trans (hMajor.trans hMotive)
  refine {
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
  }
  · simpa [cMajor, cMotive] using
      ((H.motives.mono (hle.trans hMajor)).pushCurrent
        motiveName motiveTy motiveBi)
  · simpa [cMajor, cMotive] using
      (((H.majors.mono hle).pushCurrent majorName majorTy majorBi).weaken
        motiveName motiveTy motiveBi)
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      simpa [cMajor, cMotive] using Hindices.mono (hMajor.trans hMotive)
    · have hiSize : i < recInfos.size + 1 := by simpa using hi
      have hiOld : i < recInfos.size := by omega
      have hget : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hget]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      simpa using BoundFVarArray.empty cMotive
    · have hiSize : i < recInfos.size + 1 := by simpa using hi
      have hiOld : i < recInfos.size := by omega
      have hget : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hget]
      exact (H.minors i hiOld).mono hall

theorem RecInfoBindings.pushFrame_allFvars_perm
    {stats : AddInductive.InductiveStats} {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hle : BindingContextLE c cIndices)
    (Hindices : BoundFVarArray cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    let hall : BindingContextLE c cMotive := hle.trans <|
      (BindingContextLE.withLocalDecl cIndices majorName majorTy majorBi).trans <|
        BindingContextLE.withLocalDecl cMajor motiveName motiveTy motiveBi
    ((H.pushFrame hle Hindices majorName majorTy majorBi
      motiveName motiveTy motiveBi).allFvars (Hparams.mono hall)).Perm
      (H.allFvars Hparams ++ Hindices.fvars ++
        [(⟨cIndices.ngen.curr⟩ : FVarId),
          (⟨cMajor.ngen.curr⟩ : FVarId)]) := by
  dsimp only
  rw [← Hindices.exprArrayFVarIds]
  simp only [RecInfoBindings.allFvars, Array.map_push, Array.flatMap_push,
    Array.flatMap_append, ExprArrayFVarIds, Array.toList_push,
    Array.toList_append, List.map_append, List.map_cons, List.map_nil,
    recursorFVarId]
  simp only [List.nil_append, List.append_assoc]
  apply List.Perm.append (List.Perm.refl _) <|
    List.Perm.append (List.Perm.refl _) ?_
  have reorder (minors oldIndices newIndices majors : List FVarId)
      (major motive : FVarId) :
      ([motive] ++ minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ~
        (minors ++ oldIndices ++ majors ++ newIndices ++ [major, motive]) := by
    have hswap : newIndices ++ majors ~ majors ++ newIndices :=
      List.perm_append_comm
    have hmiddle :
        minors ++ oldIndices ++ newIndices ++ majors ++ [major] ~
        minors ++ oldIndices ++ majors ++ newIndices ++ [major] := by
      simpa only [List.append_assoc] using
        (List.Perm.refl (minors ++ oldIndices)).append
          (hswap.append_right [major])
    have hmove :
        [motive] ++ (minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ~
        (minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ++
          [motive] := List.perm_append_comm
    exact hmove.trans <| by
      simpa [List.append_assoc] using hmiddle.append_right [motive]
  simpa only [List.append_assoc] using reorder
    ((Array.flatMap (fun x => x.minors) recInfos).toList.map recursorFVarId)
    ((Array.flatMap (fun x => x.indices) recInfos).toList.map recursorFVarId)
    (indices.toList.map recursorFVarId)
    ((Array.map (fun x => x.major) recInfos).toList.map recursorFVarId)
    ⟨cIndices.ngen.curr⟩ ⟨cIndices.ngen.next.curr⟩

theorem RecInfoBindings.pushFrame_noAlias
    {stats : AddInductive.InductiveStats} {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : FreshBoundFVarArray c cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    let hall : BindingContextLE c cMotive := hle.trans <|
      (BindingContextLE.withLocalDecl cIndices majorName majorTy majorBi).trans <|
        BindingContextLE.withLocalDecl cMajor motiveName motiveTy motiveBi
    (H.pushFrame hle Hindices.toBoundFVarArray majorName majorTy majorBi
      motiveName motiveTy motiveBi).NoAlias (Hparams.mono hall) := by
  dsimp only
  let old := H.allFvars Hparams
  let indexFVars := Hindices.toBoundFVarArray.fvars
  let major : FVarId := ⟨cIndices.ngen.curr⟩
  let motive : FVarId := ⟨cIndices.ngen.next.curr⟩
  have hOldIndices : (old ++ indexFVars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnoalias, Hindices.nodup, ?_⟩
    intro fv hfv fv' hfv'
    exact fun heq => Hindices.fresh fv' hfv' <| heq ▸
      H.allFvars_members Hparams fv hfv
  have hMajorFresh : major ∉ old ++ indexFVars := by
    intro hmem
    simp only [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact HcIndices.current_not_mem <| hle <|
        H.allFvars_members Hparams major hmem
    · exact HcIndices.current_not_mem <|
        Hindices.toBoundFVarArray.members major hmem
  have hWithMajor : (old ++ indexFVars ++ [major]).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hOldIndices, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hMajorFresh (heq ▸ hfv)⟩
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  have hMotiveFresh : motive ∉ old ++ indexFVars ++ [major] := by
    intro hmem
    apply (HcIndices.withLocalDecl majorName majorTy majorBi).current_not_mem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hOld | hIndex) | hMajor
    · exact Or.inr <| hle <| H.allFvars_members Hparams motive hOld
    · exact Or.inr <| Hindices.toBoundFVarArray.members motive hIndex
    · exact Or.inl hMajor
  have hCombined : (old ++ indexFVars ++ [major, motive]).Nodup := by
    rw [show [major, motive] = [major] ++ [motive] by rfl,
      ← List.append_assoc]
    apply List.nodup_append.mpr
    exact ⟨hWithMajor, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hMotiveFresh (heq ▸ hfv)⟩
  apply (H.pushFrame_allFvars_perm Hparams hle
    Hindices.toBoundFVarArray majorName majorTy majorBi
    motiveName motiveTy motiveBi).symm.nodup
  simpa [old, indexFVars, major, motive, List.append_assoc] using hCombined

def RecInfoBindings.addMinor
    (H : RecInfoBindings c recInfos) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    RecInfoBindings cMinor (recInfos.modify dIdx fun info =>
      { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }) := by
  dsimp only
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy
    minorName minorTy minorBi
  let hall := hle.trans hstep
  refine {
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
  }
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map (·.motive) =
        recInfos.map (·.motive) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.motives.mono hall
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map (·.major) =
        recInfos.map (·.major) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.majors.mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases heq : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      exact (H.indices dIdx hidx).mono hall
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hiOld heq]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases heq : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      simpa [cMinor] using
        ((H.minors dIdx hidx).mono hle).pushCurrent
          minorName minorTy minorBi
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hiOld heq]
      exact (H.minors i hiOld).mono hall

private def recInfoMinorIds (info : AddInductive.RecInfo) : List FVarId :=
  ExprArrayFVarIds info.minors

private theorem recInfoMinorIds_modify_perm
    (infos : List AddInductive.RecInfo) (i : Nat) (hi : i < infos.length)
    (minor : Expr) :
    ((infos.modify i fun info =>
      { info with minors := info.minors.push minor }).flatMap
        recInfoMinorIds).Perm
      (infos.flatMap recInfoMinorIds ++ [recursorFVarId minor]) := by
  induction infos generalizing i with
  | nil => simp at hi
  | cons info infos ih =>
    cases i with
    | zero =>
      rw [List.modify, List.modifyTailIdx_zero, List.modifyHead_cons]
      simp only [List.flatMap_cons, recInfoMinorIds,
        ExprArrayFVarIds, Array.toList_push, List.map_append,
        List.map_cons, List.map_nil]
      simpa [List.append_assoc] using
        (List.Perm.refl
          (info.minors.toList.map recursorFVarId)).append
            (List.perm_append_comm :
              [recursorFVarId minor] ++ infos.flatMap recInfoMinorIds ~
                infos.flatMap recInfoMinorIds ++ [recursorFVarId minor])
    | succ i =>
      have hi' : i < infos.length := by simpa using hi
      rw [List.modify, List.modifyTailIdx_succ_cons]
      change (recInfoMinorIds info ++
        (infos.modify i fun info =>
          { info with minors := info.minors.push minor }).flatMap
            recInfoMinorIds).Perm _
      simpa only [List.flatMap_cons, List.append_assoc] using
        (List.Perm.refl (recInfoMinorIds info)).append
          (ih i hi')

theorem RecInfoBindings.addMinor_allFvars_perm
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    let hall : BindingContextLE c cMinor := hle.trans <|
      BindingContextLE.withLocalDecl cMinorTy minorName minorTy minorBi
    ((H.addMinor dIdx hidx hle minorName minorTy minorBi).allFvars
      (Hparams.mono hall)).Perm
      (H.allFvars Hparams ++ [(⟨cMinorTy.ngen.curr⟩ : FVarId)]) := by
  dsimp only
  let minor := Expr.fvar ⟨cMinorTy.ngen.curr⟩
  let next := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push minor }
  have hMotives : next.map (·.motive) = recInfos.map (·.motive) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hMajors : next.map (·.major) = recInfos.map (·.major) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hIndexRows : next.map (·.indices) = recInfos.map (·.indices) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hIndices : next.flatMap (·.indices) =
      recInfos.flatMap (·.indices) := by
    rw [Array.flatMap_def, Array.flatMap_def, hIndexRows]
  have hMinors :
      (ExprArrayFVarIds (next.flatMap (·.minors))).Perm
        (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
          [(⟨cMinorTy.ngen.curr⟩ : FVarId)]) := by
    have h := recInfoMinorIds_modify_perm recInfos.toList dIdx
      (by simpa using hidx) minor
    change ((recInfos.toList.modify dIdx fun info =>
        { info with minors := info.minors.push minor }).flatMap
          (fun info => info.minors.toList.map recursorFVarId)).Perm
      (recInfos.toList.flatMap
        (fun info => info.minors.toList.map recursorFVarId) ++
          [recursorFVarId minor]) at h
    dsimp [minor, recursorFVarId] at h
    simpa [next, minor, ExprArrayFVarIds, Array.toList_flatMap,
      List.map_flatMap] using h
  unfold RecInfoBindings.allFvars
  change (ExprArrayFVarIds stats.params ++
    (ExprArrayFVarIds (next.map (·.motive)) ++
      (ExprArrayFVarIds (next.flatMap (·.minors)) ++
        (ExprArrayFVarIds (next.flatMap (·.indices)) ++
          ExprArrayFVarIds (next.map (·.major)))))).Perm _
  rw [hMotives, hIndices, hMajors]
  let pre := ExprArrayFVarIds stats.params ++
    ExprArrayFVarIds (recInfos.map (·.motive))
  let suffix := ExprArrayFVarIds (recInfos.flatMap (·.indices)) ++
    ExprArrayFVarIds (recInfos.map (·.major))
  have hMove :
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
        [(⟨cMinorTy.ngen.curr⟩ : FVarId)]) ++ suffix ~
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++ suffix) ++
        [(⟨cMinorTy.ngen.curr⟩ : FVarId)] := by
    simpa [List.append_assoc] using
      (List.Perm.refl
        (ExprArrayFVarIds (recInfos.flatMap (·.minors)))).append
          (List.perm_append_comm :
            [(⟨cMinorTy.ngen.curr⟩ : FVarId)] ++ suffix ~
              suffix ++ [(⟨cMinorTy.ngen.curr⟩ : FVarId)])
  have hTail := (hMinors.append (List.Perm.refl suffix)).trans hMove
  simpa [pre, suffix, List.append_assoc] using
    (List.Perm.refl pre).append hTail

theorem RecInfoBindings.addMinor_noAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    let hall : BindingContextLE c cMinor := hle.trans <|
      BindingContextLE.withLocalDecl cMinorTy minorName minorTy minorBi
    (H.addMinor dIdx hidx hle minorName minorTy minorBi).NoAlias
      (Hparams.mono hall) := by
  dsimp only
  let minor : FVarId := ⟨cMinorTy.ngen.curr⟩
  have hfresh : minor ∉ H.allFvars Hparams := by
    intro hmem
    exact HcMinorTy.current_not_mem <| hle <|
      H.allFvars_members Hparams minor hmem
  have hcombined : (H.allFvars Hparams ++ [minor]).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hnoalias, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hfresh (heq ▸ hfv)⟩
  apply (H.addMinor_allFvars_perm Hparams dIdx hidx hle
    minorName minorTy minorBi).symm.nodup
  simpa [minor] using hcombined

namespace mkRecInfos.loopArgs1

/-- Operational strengthening of `continueWith`: every non-parameter binder
opened while replaying an inductive header is retained in the local context
and appended to the certified index array. -/
theorem continueWithBindings {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    (Hk : ∀ indices c, BindingContextWF c →
      FreshBoundFVarArray root c indices →
      BindingContextLE root c → (k indices c).WF Q) :
    ∀ type i indices fuel c,
      BindingContextWF c → FreshBoundFVarArray root c indices →
      BindingContextLE root c →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, 0, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, i, indices, fuel + 1, c, Hc, Hindices, Hroot => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        by_cases hparam : i < stats.params.size
        · rw [if_pos hparam]
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 stats.params[i]!)) :
                AddInductive.M Expr) c).WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWithBindings stats k Hk next (i + 1) indices fuel c
              Hc Hindices Hroot
        · rw [if_neg hparam]
          unfold Lean4Lean.withLocalDecl
            MonadLocalNameGenerator.withFreshId
            AddInductive.instMonadLocalNameGeneratorM
            AddInductive.instMonadWithReaderOfLocalContextM
          let c' : AddInductive.Context := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }
          change ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c' >>= fun next =>
              AddInductive.mkRecInfos.loopArgs1 stats next i
                (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel k c').WF Q
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
                AddInductive.M Expr) c').WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWithBindings stats k Hk next i
              (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel c'
              (Hc.withLocalDecl name dom.consumeTypeAnnotations bi)
              (Hindices.pushCurrent Hc Hroot name
                dom.consumeTypeAnnotations bi)
              (Hroot.trans <| BindingContextLE.withLocalDecl c name
                dom.consumeTypeAnnotations bi)
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          simpa [AddInductive.mkRecInfos.loopArgs1] using
            Hk indices c Hc Hindices Hroot

end mkRecInfos.loopArgs1

namespace mkRecInfos.loopInd1

/-- The first mutual pass retains selectable motive, index, and major binders
for every appended `RecInfo`. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hprogress : recInfos.size = dIdx)
    (Harities : RecInfoArities stats recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hk : ∀ out c,
      out.size = recInfos.size + (indTypes.size - dIdx) →
      BindingContextWF c → (Hbindings : RecInfoBindings c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoArities stats out →
      RecInfoMinorsEmpty out →
      BindingContextLE root c → (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context)
      hread fun ctx hctx => ?_
    subst ctx
    have hwhnf :
        ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
          AddInductive.M Expr) c).WF (fun _ => True) := by
      intro _ _
      trivial
    refine hwhnf.bind fun type _ => ?_
    apply mkRecInfos.loopArgs1.continueWithBindings
      (root := c) stats
    · intro indices cIndices HcIndices Hindices hIndices
      by_cases harity : (indices.size == stats.nindices[dIdx]!) = true
      · rw [if_pos harity]
        let majorTy :=
          (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
            indices).consumeTypeAnnotations
        apply withLocalDecl.continueRaw
        let cMajor : AddInductive.Context := { cIndices with
          ngen := cIndices.ngen.next
          lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
            majorTy .default }
        have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
            (fun lctx => lctx = cMajor.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        let major := Expr.fvar ⟨cIndices.ngen.curr⟩
        let motiveTy := cMajor.lctx.mkForall indices <|
          cMajor.lctx.mkForall #[major] <| .sort elimLevel
        let motiveName := if indTypes.size > 1 then
          (`motive).appendIndexAfter (dIdx + 1) else `motive
        apply withLocalDecl.continueRaw
        let cMotive : AddInductive.Context := { cMajor with
          ngen := cMajor.ngen.next
          lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩ motiveName
            motiveTy.consumeTypeAnnotations .default }
        refine mkRecInfos.loopInd1.resultBindings (root := root) (Q := Q)
          stats indTypes elimLevel
          (dIdx + 1) (recInfos.push {
            motive := .fvar ⟨cMajor.ngen.curr⟩
            minors := #[]
            indices
            major }) k cMotive ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · exact (HcIndices.withLocalDecl `t majorTy .default).withLocalDecl
            motiveName motiveTy.consumeTypeAnnotations .default
        · exact Hbindings.pushFrame hIndices Hindices.toBoundFVarArray
            `t majorTy .default
            motiveName motiveTy.consumeTypeAnnotations .default
        · exact Hparams.mono <| hIndices.trans <|
            (BindingContextLE.withLocalDecl cIndices `t majorTy .default).trans <|
              BindingContextLE.withLocalDecl cMajor motiveName
                motiveTy.consumeTypeAnnotations .default
        · exact Hbindings.pushFrame_noAlias Hparams HnoAlias hIndices
            HcIndices Hindices `t majorTy .default motiveName
              motiveTy.consumeTypeAnnotations .default
        · exact Hroot.trans <| hIndices.trans <|
            (BindingContextLE.withLocalDecl cIndices `t majorTy .default).trans <|
              BindingContextLE.withLocalDecl cMajor motiveName
                motiveTy.consumeTypeAnnotations .default
        · simp [hprogress]
        · apply Harities.push
          have hnew : indices.size = stats.nindices[dIdx]! := by
            simpa using harity
          simpa [hprogress] using hnew
        · exact Hempty.push
        · intro out cOut houtSize HcOut HbindingsOut HparamsOut
            HnoAliasOut HaritiesOut HemptyOut HrootOut
          have houtSize' : out.size = recInfos.size +
              (indTypes.size - dIdx) := by
            simp only [Array.size_push] at houtSize
            omega
          exact Hk out cOut houtSize' HcOut HbindingsOut HparamsOut
            HnoAliasOut HaritiesOut HemptyOut HrootOut
      · rw [if_neg harity]
        exact Except.WF.throw
    · exact Hc
    · exact FreshBoundFVarArray.empty c
    · exact BindingContextLE.refl c
  · rw [dif_neg hidx]
    exact Hk recInfos c (by omega) Hc Hbindings Hparams HnoAlias
      Harities Hempty Hroot
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd1

namespace mkRecInfos.loopUArgs.loop

/-- Every higher-order argument opened while exposing a recursive field is a
fresh ordinary local declaration, retained in the exact array later passed to
`LocalContext.mkLambda`. -/
theorem resultBindings {alpha : Type}
    (k : Expr → Array Expr → AddInductive.M alpha)
    {uiTy : Expr} {xs : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hxs : FreshBoundFVarArray root c xs)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ uiTy xs c, BindingContextWF c →
      FreshBoundFVarArray root c xs → BindingContextLE root c →
      (k uiTy xs c).WF Q) :
    (AddInductive.mkRecInfos.loopUArgs.loop k uiTy xs fuel c).WF Q := by
  induction fuel generalizing c uiTy xs with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopUArgs.loop] at h
  | succ fuel ih =>
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          dom.consumeTypeAnnotations bi }
      unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
        AddInductive.instMonadLocalNameGeneratorM
        AddInductive.instMonadWithReaderOfLocalContextM
      change ((monadLift (TypeChecker.whnf
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
          AddInductive.M Expr) c' >>= fun normalized =>
        AddInductive.mkRecInfos.loopUArgs.loop k normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) fuel c').WF Q
      have hwhnf :
          ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c').WF (fun _ => True) := by
        intro _ _
        trivial
      exact hwhnf.bind fun normalized _ =>
        ih (Hc.withLocalDecl name dom.consumeTypeAnnotations bi)
          (Hxs.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
          (Hroot.trans <| BindingContextLE.withLocalDecl c name
            dom.consumeTypeAnnotations bi)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change (k _ xs c).WF Q
      exact Hk _ _ _ Hc Hxs Hroot

end mkRecInfos.loopUArgs.loop

/-- Public binder-aware interface for `loopUArgs`, starting from its empty
local-argument accumulator. -/
theorem mkRecInfos.loopUArgs.resultBindings {alpha : Type}
    (ui : Expr) (k : Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hk : ∀ uiTy xs c', BindingContextWF c' →
      FreshBoundFVarArray c c' xs → BindingContextLE c c' →
      (k uiTy xs c').WF Q) :
    (AddInductive.mkRecInfos.loopUArgs ui k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopUArgs
  have hinfer :
      ((monadLift (TypeChecker.inferType ui) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hinfer.bind fun inferred _ => ?_
  have hwhnf :
      ((monadLift (TypeChecker.whnf inferred) : AddInductive.M Expr) c).WF
        (fun _ => True) := by
    intro _ _
    trivial
  refine hwhnf.bind fun normalized _ => ?_
  change (AddInductive.mkRecInfos.loopUArgs.loop k normalized #[]
    c.fuel.inductiveFuel c).WF Q
  exact mkRecInfos.loopUArgs.loop.resultBindings k Hc
    (FreshBoundFVarArray.empty c) (BindingContextLE.refl c) Hk

/-- Exact recursive-call syntax together with the inner binding context used
to close its higher-order arguments. -/
structure BoundGeneratedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context) (field value : Expr) where
  exposedType : Expr
  localArgs : Array Expr
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  arguments_bound : FreshBoundFVarArray root current localArgs
  value_eq :
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN
      (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices
    value = (current.lctx.mkLambda localArgs <|
      recursor.app (mkAppN field localArgs))

theorem BoundGeneratedRecursiveCall.generated
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    checkPositivityStep.GeneratedRecursiveCall
      indTypes stats motives minors lvls field value := by
  exact ⟨H.exposedType, H.localArgs, H.current.lctx, H.value_eq⟩

def BoundGeneratedRecursiveCall.body
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let (typeIdx, indices) := AddInductive.getIIndices stats H.exposedType
  let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
  let recursor := mkAppN
    (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
    indices
  recursor.app (mkAppN field H.localArgs)

theorem BoundGeneratedRecursiveCall.value_eq_body
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    value = H.current.lctx.mkLambda H.localArgs H.body := by
  simpa [BoundGeneratedRecursiveCall.body] using H.value_eq

/-- The exact lambda telescope closed by one generated recursive call. -/
theorem BoundGeneratedRecursiveCall.lambdaTelescope
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    Expr.LambdaTelescope value H.localArgs.size
      (H.body.abstractList H.arguments_bound.fvars) := by
  rcases H with ⟨exposedType, localArgs, current, Hwf, Hle, Hargs, Hvalue⟩
  let callBody : Expr :=
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN
      (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices
    recursor.app (mkAppN field localArgs)
  have Hvalue' : value = current.lctx.mkLambda localArgs callBody := by
    simpa [callBody] using Hvalue
  change Expr.LambdaTelescope value localArgs.size
    (callBody.abstractList Hargs.fvars)
  rw [Hvalue']
  let Hselection :=
    Hargs.toBoundFVarArray.toLocalForallSelection Hwf
  have Hfvars : Hselection.fvars = Hargs.fvars := rfl
  rcases Hselection with ⟨fvars, rfl, Hdecl⟩
  rw [← Hfvars]
  simpa using
    (LocalContext.mkLambda_fvars_lambdaTelescope
      (body := callBody) Hdecl)

/-- Translating a bound generated call exposes the exact abstract lambda
domains and the translation of its simultaneously abstracted call body. -/
theorem BoundGeneratedRecursiveCall.translatedLambdaShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result) :
    ∃ domains residual, domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains residual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.body.abstractList H.arguments_bound.fvars) residual := by
  exact TrExprS.lambdaTelescope_shape_with_context H.lambdaTelescope Htr

/-- Closing a generated call over an additional rule-level binder list
preserves its higher-order lambda arity. The residual records the necessary
binder-depth shift explicitly, avoiding any assumption that translation and
simultaneous abstraction commute definitionally. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedLambdaTelescope
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) :
    Expr.LambdaTelescope (value.abstractList binders)
      H.localArgs.size
      ((H.body.abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size) := by
  simpa using H.lambdaTelescope.abstractList binders

theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedLambdaShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result) :
    ∃ domains residual, domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains residual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        ((H.body.abstractList H.arguments_bound.fvars).abstractList
          binders H.localArgs.size) residual := by
  exact TrExprS.lambdaTelescope_shape_with_context
    (H.outerAbstractedLambdaTelescope binders) Htr

theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedLambdaShape_noFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains residual, domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains residual ∧
      TrExprS env Us (abstractForallContext domains Δ)
        ((H.body.abstractList H.arguments_bound.fvars).abstractList
          binders H.localArgs.size) residual ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false := by
  exact TrExprS.lambdaTelescope_shape_with_context_noFresh
    hfresh hctx hproj (H.outerAbstractedLambdaTelescope binders) Htr

/-- Simultaneous abstraction preserves the generated recursor spine and
turns the freshly opened local arguments into the canonical de Bruijn spine
on the recursive field. -/
theorem BoundGeneratedRecursiveCall.abstractedBody_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    let (typeIdx, indices) :=
      AddInductive.getIIndices stats H.exposedType
    H.body.abstractList H.arguments_bound.fvars =
      (mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[typeIdx]!.name) lvls)
              (stats.params.map fun e =>
                e.abstractList H.arguments_bound.fvars))
            (motives.map fun e =>
              e.abstractList H.arguments_bound.fvars))
          (minors.map fun e =>
            e.abstractList H.arguments_bound.fvars))
        (indices.map fun e =>
          e.abstractList H.arguments_bound.fvars)).app
        (mkAppN (field.abstractList H.arguments_bound.fvars)
          (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
            Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray) := by
  rcases hindices : AddInductive.getIIndices stats H.exposedType with
    ⟨typeIdx, indices⟩
  have hlocal :
      H.localArgs.map (fun e =>
        e.abstractList H.arguments_bound.fvars) =
      (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      H.localArgs.map (fun e =>
          e.abstractList H.arguments_bound.fvars) =
          ((H.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractList H.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractList H.arguments_bound.fvars)
            H.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          H.arguments_bound.fvars 0 H.arguments_bound.nodup
  simp only [BoundGeneratedRecursiveCall.body, hindices,
    Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hlocal]
  have hconst :
      (Expr.const (Lean.mkRecName indTypes[typeIdx]!.name) lvls).abstractList
        H.arguments_bound.fvars =
      .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls := by
    induction H.arguments_bound.fvars with
    | nil => simp
    | cons fv fvs ih =>
      simp only [Expr.abstractList]
      simpa [Expr.abstract1] using ih
  rw [hconst]

def BoundGeneratedRecursiveCall.recursorName
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Name :=
  Lean.mkRecName indTypes[(AddInductive.getIIndices stats H.exposedType).1]!.name

def BoundGeneratedRecursiveCall.abstractedRecursor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let indices := (AddInductive.getIIndices stats H.exposedType).2
  mkAppN
    (mkAppN
      (mkAppN
        (mkAppN (.const H.recursorName lvls)
          (stats.params.map fun e =>
            e.abstractList H.arguments_bound.fvars))
        (motives.map fun e =>
          e.abstractList H.arguments_bound.fvars))
      (minors.map fun e =>
        e.abstractList H.arguments_bound.fvars))
    (indices.map fun e =>
      e.abstractList H.arguments_bound.fvars)

def BoundGeneratedRecursiveCall.abstractedMajor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  mkAppN (field.abstractList H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray

def BoundGeneratedRecursiveCall.outerAbstractedRecursor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) : Expr :=
  H.abstractedRecursor.abstractList binders H.localArgs.size

def BoundGeneratedRecursiveCall.outerAbstractedMajor
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) : Expr :=
  H.abstractedMajor.abstractList binders H.localArgs.size

def BoundGeneratedRecursiveCall.localIndices
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) : List Nat :=
  List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
    H.arguments_bound.fvars.length - 1 - i

/-- Rule-level abstraction turns the selected field free variable into its
outer de Bruijn index beneath the generated call's local lambda binders. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedMajor_eq_bvar
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      H.outerAbstractedMajor binders =
        mkAppN (.bvar (H.localArgs.size + fieldVar))
          (H.localIndices.map Expr.bvar).toArray := by
  rcases List.mem_iff_getElem.mp hfield with ⟨i, hi, hget⟩
  let fieldVar := binders.length - 1 - i
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldLocal :
      (Expr.fvar fv).abstractList H.arguments_bound.fvars = .fvar fv :=
    Expr.abstractList_fvar_of_not_mem hfresh
  have hlocalSize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  have hfieldOuter := Expr.abstractList_fvar_getElem
    hbinders i hi (k := H.localArgs.size)
  rw [hget] at hfieldOuter
  have hfieldOuter' :
      (Expr.fvar fv).abstractList binders H.localArgs.size =
        .bvar (H.localArgs.size + fieldVar) := by
    simpa [fieldVar] using hfieldOuter
  have hfieldBase := Expr.abstractList_fvar_getElem
    hbinders i hi (k := 0)
  rw [hget] at hfieldBase
  have hfieldBase' : (Expr.fvar fv).abstractList binders =
      .bvar fieldVar := by
    simpa [fieldVar] using hfieldBase
  have hsourceArgs :
      (List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i)) =
      H.localIndices.map Expr.bvar := by
    simp [BoundGeneratedRecursiveCall.localIndices,
      List.map_ofFn, Function.comp_def]
  refine ⟨fieldVar, by omega, hfieldBase', ?_⟩
  unfold BoundGeneratedRecursiveCall.outerAbstractedMajor
    BoundGeneratedRecursiveCall.abstractedMajor
  rw [Expr.abstractList_mkAppN, hfieldLocal, hfieldOuter']
  apply congrArg (mkAppN (.bvar (H.localArgs.size + fieldVar)))
  rw [hsourceArgs]
  apply Array.ext
  · simp
  · intro j hjLeft hjRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map]
    apply Expr.abstractList_bvar_lt
    have hj : j < H.localIndices.length := by simpa using hjRight
    have hj' : j < H.arguments_bound.fvars.length := by
      simpa [BoundGeneratedRecursiveCall.localIndices] using hj
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.getElem_ofFn]
    omega

theorem BoundGeneratedRecursiveCall.abstractedBody_eq_named
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.body.abstractList H.arguments_bound.fvars =
      H.abstractedRecursor.app H.abstractedMajor := by
  simpa [BoundGeneratedRecursiveCall.abstractedRecursor,
    BoundGeneratedRecursiveCall.abstractedMajor,
    BoundGeneratedRecursiveCall.recursorName] using H.abstractedBody_eq

theorem BoundGeneratedRecursiveCall.outerAbstractedBody_eq_named
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    (H.body.abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size =
      (H.outerAbstractedRecursor binders).app
        (H.outerAbstractedMajor binders) := by
  rw [H.abstractedBody_eq_named]
  exact Expr.abstractList_app

theorem BoundGeneratedRecursiveCall.abstractedRecursor_head
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.abstractedRecursor.getAppFn = .const H.recursorName lvls := by
  have getAppFn_mkAppN : ∀ (fn : Expr) (args : Array Expr),
      (mkAppN fn args).getAppFn = fn.getAppFn := by
    intro fn args
    unfold mkAppN
    rw [← Array.foldl_toList]
    generalize args.toList = list
    induction list generalizing fn with
    | nil => rfl
    | cons arg args ih =>
      simp only [List.foldl_cons]
      simpa [Expr.getAppFn] using ih (.app fn arg)
  simp only [BoundGeneratedRecursiveCall.abstractedRecursor]
  repeat' rw [getAppFn_mkAppN]
  rfl

theorem BoundGeneratedRecursiveCall.outerAbstractedRecursor_head
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    (H.outerAbstractedRecursor binders).getAppFn =
      .const H.recursorName lvls := by
  have getAppFn_mkAppN : ∀ (fn : Expr) (args : Array Expr),
      (mkAppN fn args).getAppFn = fn.getAppFn := by
    intro fn args
    unfold mkAppN
    rw [← Array.foldl_toList]
    generalize args.toList = list
    induction list generalizing fn with
    | nil => rfl
    | cons arg args ih =>
      simp only [List.foldl_cons]
      simpa [Expr.getAppFn] using ih (.app fn arg)
  simp only [BoundGeneratedRecursiveCall.outerAbstractedRecursor,
    BoundGeneratedRecursiveCall.abstractedRecursor,
    Expr.abstractList_mkAppN]
  repeat' rw [getAppFn_mkAppN]
  simp [Expr.getAppFn]

/-- Exact translation of the generated major premise for a selected field
free variable. Outer translations are shifted under the generated lambdas;
the newly opened arguments translate to their canonical de Bruijn variables. -/
theorem BoundGeneratedRecursiveCall.translatedMajor_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (henv : env.Ordered)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (Hfield : TrExprS env Us Δ (.fvar fv) recursiveArg)
    (hdomains : domains.length = H.localArgs.size)
    (Hmajor : TrExprS env Us (abstractForallContext domains Δ)
      H.abstractedMajor major) :
    major = VExpr.mkApps (recursiveArg.liftN domains.length 0)
      (H.localIndices.map VExpr.bvar) := by
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldAbstract :
      (Expr.fvar fv).abstractList H.arguments_bound.fvars = .fvar fv :=
    Expr.abstractList_fvar_of_not_mem hfresh
  have hlocalSize :
      H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  have hindexBound : ∀ i ∈ H.localIndices, i < domains.length := by
    intro i hi
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.mem_ofFn] at hi
    rcases hi with ⟨j, rfl⟩
    omega
  have HfieldWeak : TrExprS env Us (abstractForallContext domains Δ)
      (.fvar fv) (recursiveArg.liftN domains.length 0) := by
    have Hweak := Hfield.weakBV henv
      (abstractForallContext.bvLift domains Δ)
    simpa [Expr.liftLooseBVars'] using Hweak
  have Hmajor' := Hmajor
  have hsourceArgs :
      (List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i)) =
      H.localIndices.map Expr.bvar := by
    simp [BoundGeneratedRecursiveCall.localIndices,
      List.map_ofFn, Function.comp_def]
  unfold BoundGeneratedRecursiveCall.abstractedMajor at Hmajor'
  rw [hfieldAbstract] at Hmajor'
  unfold mkAppN at Hmajor'
  rw [← Array.foldl_toList] at Hmajor'
  rw [List.toList_toArray] at Hmajor'
  rw [hsourceArgs, List.foldl_map] at Hmajor'
  change TrExprS env Us (abstractForallContext domains Δ)
    (H.localIndices.foldl (fun fn i => .app fn (.bvar i)) (.fvar fv))
      major at Hmajor'
  have heq := TrExprS.foldl_bvars_eq domains Δ H.localIndices
    hindexBound (.fvar fv) (recursiveArg.liftN domains.length 0)
    (fun out Hout => TrExprS.unique (e := (.fvar fv))
      (by trivial) Hout HfieldWeak) Hmajor'
  simpa [VExpr.mkApps, List.foldl_map] using heq

theorem BoundGeneratedRecursiveCall.translatedMajor_isField
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (henv : env.Ordered)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (Hfield : TrExprS env Us Δ (.fvar fv) recursiveArg)
    (hfield : recursiveArg.IsFieldApp fieldVars 0)
    (hdomains : domains.length = H.localArgs.size)
    (Hmajor : TrExprS env Us (abstractForallContext domains Δ)
      H.abstractedMajor major) :
    major.IsFieldApp fieldVars domains.length := by
  rw [H.translatedMajor_eq henv hfieldRoot Hfield hdomains Hmajor]
  simpa using VExpr.IsFieldApp.appendApps
    (VExpr.IsFieldApp.lift hfield domains.length)
      (H.localIndices.map VExpr.bvar)

/-- The major premise in a closed rule is a designated outer field shifted
beneath exactly the generated call's local lambda domains. -/
theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedMajor_isField
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hlocalDomains : localDomains.length = H.localArgs.size)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars)
    (Hmajor : TrExprS env Us
      (abstractForallContext localDomains
        (abstractForallContext ruleDomains Δ))
      (H.outerAbstractedMajor binders) major) :
    major.IsFieldApp fieldVars localDomains.length := by
  rcases H.outerAbstractedMajor_eq_bvar hfieldRoot hbinders hfield with
    ⟨fieldVar, hfieldVar, hfieldSource, hsource⟩
  rw [hsource] at Hmajor
  have Hmajor' : TrExprS env Us
      (abstractForallContext (ruleDomains ++ localDomains) Δ)
      (mkAppN (.bvar (H.localArgs.size + fieldVar))
        (H.localIndices.map Expr.bvar).toArray) major := by
    simpa using Hmajor
  unfold mkAppN at Hmajor'
  rw [← Array.foldl_toList, List.toList_toArray,
    List.foldl_map] at Hmajor'
  have htotal : H.localArgs.size + fieldVar <
      (ruleDomains ++ localDomains).length := by
    simp only [List.length_append]
    omega
  have hindices : ∀ index ∈ H.localIndices,
      index < (ruleDomains ++ localDomains).length := by
    intro index hindex
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.mem_ofFn] at hindex
    rcases hindex with ⟨j, rfl⟩
    simp only [List.length_append]
    have hlocalSize : H.localArgs.size =
        H.arguments_bound.fvars.length := by
      have := congrArg Array.size H.arguments_bound.expressions
      simpa using this
    omega
  have hmajorEq := TrExprS.foldl_bvars_eq
    (ruleDomains ++ localDomains) Δ H.localIndices hindices
    (.bvar (H.localArgs.size + fieldVar))
    (.bvar (H.localArgs.size + fieldVar))
    (fun out Hout => TrExprS.bvar_eq_of_abstractForallContext
      Hout htotal) Hmajor'
  have hmajorEq' : major =
      VExpr.mkApps (.bvar (H.localArgs.size + fieldVar))
        (H.localIndices.map VExpr.bvar) := by
    simpa [VExpr.mkApps, List.foldl_map] using hmajorEq
  have hbase : (VExpr.bvar fieldVar).IsFieldApp fieldVars 0 := by
    refine ⟨fieldVar, hfieldVars fieldVar hfieldSource, [], ?_⟩
    rfl
  have hlift := VExpr.IsFieldApp.lift hbase localDomains.length
  have happ := VExpr.IsFieldApp.appendApps hlift
    (H.localIndices.map VExpr.bvar)
  rw [hmajorEq']
  simpa [hlocalDomains, Nat.add_comm, VExpr.liftN, liftVar] using happ

/-- Syntax-directed translation of a generated higher-order recursive call.
The semantic guard is intentionally not assumed here: initial arguments and
the major premise remain exposed with their exact translation derivations. -/
theorem BoundGeneratedRecursiveCall.translatedCallShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        H.abstractedRecursor.getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        H.abstractedMajor major := by
  rcases H.translatedLambdaShape Htr with
    ⟨domains, residual, hdomains, hresult, hresidual⟩
  rw [H.abstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.abstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Freshness-aware generated-call translation. Unlike freshness of the
complete result (which deliberately contains the new recursor), this retains
freshness exactly for the enclosing higher-order domains. -/
theorem BoundGeneratedRecursiveCall.translatedCallShape_noFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        H.abstractedRecursor.getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        H.abstractedMajor major ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false := by
  rcases TrExprS.lambdaTelescope_shape_with_context_noFresh
      hfresh hctx hproj H.lambdaTelescope Htr with
    ⟨domains, residual, hdomains, hresult, hresidual, hfree⟩
  rw [H.abstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.abstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor, hfree⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Generated-call spine inversion for the form that occurs inside a closed
rule RHS, after simultaneous abstraction over the rule binders. -/
theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedCallShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        (H.outerAbstractedRecursor binders).getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.outerAbstractedMajor binders) major := by
  rcases H.translatedOuterAbstractedLambdaShape Htr with
    ⟨domains, residual, hdomains, hresult, hresidual⟩
  rw [H.outerAbstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.outerAbstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedCallShape_noFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        (H.outerAbstractedRecursor binders).getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.outerAbstractedMajor binders) major ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false := by
  rcases H.translatedOuterAbstractedLambdaShape_noFresh
      Htr hfresh hctx hproj with
    ⟨domains, residual, hdomains, hresult, hresidual, hfree⟩
  rw [H.outerAbstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.outerAbstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor, hfree⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Guarded recursive-result certificate for the simultaneously abstracted
generated value that occurs in a closed rule RHS. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedIotaResultCertificate_ofFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (Htr : TrExprS env Us (abstractForallContext ruleDomains Δ)
      (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursorName ∈ recursors)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedOuterAbstractedCallShape_noFresh
      Htr hfresh hctx hproj with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor, hdomainsFree⟩
  have hctx' : VLCtx.NoIndConsts recursors
      (abstractForallContext domains
        (abstractForallContext ruleDomains Δ)) :=
    VLCtx.NoIndConsts.abstractForallContext
      (domains := domains) hctx
  have hinitFree : ∀ arg ∈ init,
      arg.containsAnyConst recursors = false :=
    checkPositivityStep.List.Forall₂.targets_noFreshConsts
      hinit hfresh hctx' hproj
  have hmajorFree : major.containsAnyConst recursors = false :=
    checkPositivityStep.TrExprS.noFreshConsts
      hfresh hctx' hproj hmajor
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := by
      intro arg harg
      rcases List.mem_append.mp harg with harg | harg
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse
          (hinitFree arg harg)
      · simp only [List.mem_singleton] at harg
        subst arg
        exact VExpr.GuardedIota.ofContainsAnyConstFalse hmajorFree
    major_is_field := H.translatedOuterAbstractedMajor_isField
      hfieldRoot hbinders hfield hruleDomains hdomains hfieldVars hmajor }⟩

/-- Equality-oriented wrapper that keeps call-dependent evidence, notably
recursor membership, synchronized while identifying the selected field. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedIotaResultCertificate_ofFresh_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (Htr : TrExprS env Us (abstractForallContext ruleDomains Δ)
      (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursorName ∈ recursors)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  subst field
  exact H.outerAbstractedIotaResultCertificate_ofFresh Htr hfresh hctx
    hproj hrecursor hfieldRoot hbinders hfield hruleDomains hfieldVars

/-- A generated recursive result is semantically guarded whenever the new
recursor names are fresh in the translation environment and the selected
constructor field is already identified in the outer abstract context. -/
theorem BoundGeneratedRecursiveCall.iotaResultCertificate_ofFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (Htr : TrExprS env Us Δ value result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursorName ∈ recursors)
    (henv : env.Ordered)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (Hfield : TrExprS env Us Δ (.fvar fv) recursiveArg)
    (hfield : recursiveArg.IsFieldApp fieldVars 0) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedCallShape_noFresh Htr hfresh hctx hproj with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor, hdomainsFree⟩
  have hctx' : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ) :=
    VLCtx.NoIndConsts.abstractForallContext
      (domains := domains) hctx
  have hinitFree : ∀ arg ∈ init,
      arg.containsAnyConst recursors = false :=
    checkPositivityStep.List.Forall₂.targets_noFreshConsts
      hinit hfresh hctx' hproj
  have hmajorFree : major.containsAnyConst recursors = false :=
    checkPositivityStep.TrExprS.noFreshConsts
      hfresh hctx' hproj hmajor
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := by
      intro arg harg
      rcases List.mem_append.mp harg with harg | harg
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse
          (hinitFree arg harg)
      · simp only [List.mem_singleton] at harg
        subst arg
        exact VExpr.GuardedIota.ofContainsAnyConstFalse hmajorFree
    major_is_field := H.translatedMajor_isField henv hfieldRoot Hfield
      hfield hdomains hmajor }⟩

/-- Turn the syntax-directed call translation into the semantic guarded-call
certificate. The remaining callback is precisely the guard proof; executable
syntax, lambda closure, recursor name, and translated spine are fixed here. -/
theorem BoundGeneratedRecursiveCall.iotaResultCertificate
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result)
    (hrecursor : H.recursorName ∈ recursors)
    (Hguard : ∀ (domains : List VExpr) (levels : List VLevel)
      (init : List VExpr) (major : VExpr),
      domains.length = H.localArgs.size →
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        H.abstractedRecursor.getAppArgsList init →
      TrExprS env Us (abstractForallContext domains Δ)
        H.abstractedMajor major →
      (∀ dom ∈ domains, dom.containsAnyConst recursors = false) ∧
      (∀ arg ∈ init ++ [major],
        arg.GuardedIota recursors fieldVars domains.length) ∧
      major.IsFieldApp fieldVars domains.length) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedCallShape Htr with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor⟩
  rcases Hguard domains levels init major hdomains hinit hmajor with
    ⟨hdomainsFree, harguments, hmajorField⟩
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := harguments
    major_is_field := hmajorField }⟩

/-- Prefix invariant for rule generation retaining both exact syntax and the
binding evidence needed to translate every higher-order recursive result. -/
structure BoundGeneratedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    Nonempty (BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root u[i] v[i]!)

def BoundGeneratedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context) (u : Array Expr) :
    BoundGeneratedRecursiveCalls indTypes stats motives minors lvls root
      u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

def BoundGeneratedRecursiveCalls.push
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v done)
    (hdone : done < u.size)
    (Hentry : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root u[done] value) :
    BoundGeneratedRecursiveCalls indTypes stats motives minors lvls root
      u (v.push value) (done + 1) where
  covered := by omega
  size := by simp [H.size]
  entries i hi hiu := by
    by_cases h : i = done
    · subst i
      have hpush : done < (v.push value).size := by simp [H.size]
      have hbang : (v.push value)[done]! = value := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush]
        simpa [H.size] using (@Array.getElem_push_eq Expr v value)
      rw [hbang]
      exact ⟨Hentry⟩
    · have hold : i < done := by omega
      have hv : i < v.size := by simpa [H.size] using hold
      have hpush : i < (v.push value).size := by
        simpa using Nat.lt_succ_of_lt hv
      have hbang : (v.push value)[i]! = v[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hv]
        exact Array.getElem_push_lt hv
      rw [hbang]
      exact H.entries i hold hiu

theorem BoundGeneratedRecursiveCalls.generated
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v done) :
    checkPositivityStep.GeneratedRecursiveCalls indTypes stats motives minors
      lvls u v done where
  covered := H.covered
  size := H.size
  entries i hi hiu := by
    rcases H.entries i hi hiu with ⟨Hentry⟩
    exact Hentry.generated

/-- Convert the binder-aware executable call array into the aligned semantic
recursive-result certificate. Only the genuinely pointwise call proof remains
as a premise; all array/list indexing and translation alignment are handled
here. -/
theorem BoundGeneratedRecursiveCalls.iotaResults
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      u.toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      v.toList recursiveResults)
    (Hpoint : ∀ i (hi : i < u.size)
      (harg : i < recursiveArgs.length)
      (hresult : i < recursiveResults.length),
      BoundGeneratedRecursiveCall indTypes stats motives minors lvls
        root u[i] v[i]! →
      TrExprS env Us Δ u[i] recursiveArgs[i] →
      TrExprS env Us Δ v[i]! recursiveResults[i] →
      Nonempty (IotaRecursiveResultCertificate recursors fieldVars
        recursiveArgs[i] recursiveResults[i])) :
    IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults := by
  have hargsLen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hresultsLen :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hresults
  have hargsSize : u.size = recursiveArgs.length := by
    simpa using hargsLen
  have hresultsSize : v.size = recursiveResults.length := by
    simpa using hresultsLen
  have hvSize : v.size = u.size := H.size
  refine ⟨List.forall₂_of_getElem (by omega) ?_⟩
  intro i hiArg hiResult
  have hiU : i < u.size := by
    simpa using (show i < u.toList.length by omega)
  have hiV : i < v.toList.length := by omega
  rcases H.entries i hiU hiU with ⟨Hentry⟩
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hiU) hiArg
  have Hresult := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hresults i hiV hiResult
  apply Hpoint i hiU hiArg hiResult Hentry
  · simpa using Harg
  · have hiVSize : i < v.size := by simpa using hiV
    simpa [Array.getElem!_eq_getD, Array.getD, hiVSize] using Hresult

/-- Array-alignment lift for generated calls after simultaneous abstraction
over the surrounding rule binders. -/
theorem BoundGeneratedRecursiveCalls.abstractedIotaResults
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      (u.map fun arg => arg.abstractList binders).toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      (v.map fun result => result.abstractList binders).toList
      recursiveResults)
    (Hpoint : ∀ i (hi : i < u.size)
      (harg : i < recursiveArgs.length)
      (hresult : i < recursiveResults.length),
      BoundGeneratedRecursiveCall indTypes stats motives minors lvls
        root u[i] v[i]! →
      TrExprS env Us Δ (u[i].abstractList binders) recursiveArgs[i] →
      TrExprS env Us Δ (v[i]!.abstractList binders)
        recursiveResults[i] →
      Nonempty (IotaRecursiveResultCertificate recursors fieldVars
        recursiveArgs[i] recursiveResults[i])) :
    IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults := by
  have hargsLen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hresultsLen :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hresults
  have hargsSize : u.size = recursiveArgs.length := by
    simpa using hargsLen
  have hresultsSize : v.size = recursiveResults.length := by
    simpa using hresultsLen
  have hvSize : v.size = u.size := H.size
  refine ⟨List.forall₂_of_getElem (by omega) ?_⟩
  intro i hiArg hiResult
  have hiU : i < u.size := by omega
  have hiV : i < v.size := by omega
  rcases H.entries i hiU hiU with ⟨Hentry⟩
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hiU) hiArg
  have Hresult := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hresults i (by simpa using hiV) hiResult
  apply Hpoint i hiU hiArg hiResult Hentry
  · simpa using Harg
  · have hiVSize : i < v.size := hiV
    simpa [Array.getElem!_eq_getD, Array.getD, hiVSize] using Hresult

/-- Exact recursor-name coverage required by a generated call array. This
avoids quantifying over arbitrary exposed expressions whose computed owner
index has not been validated. -/
def BoundGeneratedRecursiveCalls.RecursorsPresent
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size) (recursors : List Name) : Prop :=
  ∀ i (hi : i < u.size)
      (Hentry : BoundGeneratedRecursiveCall indTypes stats motives minors
        lvls root u[i] v[i]!),
    Hentry.recursorName ∈ recursors

/-- Pointwise owner alignment between typed recursive-field classification
and the later recursive-call generator. Establishing this relation is the
remaining local determinism obligation between the two production passes. -/
structure BoundGeneratedRecursiveCalls.OwnerAlignment
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (decl : VInductDecl)
    (certs : List (RecursorRecursiveDomain domainEnv decl)) : Prop where
  length : certs.length = u.size
  recursorName : ∀ i (hi : i < u.size)
      (Hentry : BoundGeneratedRecursiveCall indTypes stats motives minors
        lvls root u[i] v[i]!),
    Hentry.recursorName =
      Lean.mkRecName indTypes[(certs[i]'(by omega)).ownerIdx]!.name

theorem BoundGeneratedRecursiveCalls.abstractedIotaResults_ofFresh
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hbound : BoundFVarArray root u)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext ruleDomains Δ))
      (u.map fun arg => arg.abstractList binders).toList recursiveArgs)
    (Hresults : List.Forall₂
      (TrExprS env Us (abstractForallContext ruleDomains Δ))
      (v.map fun result => result.abstractList binders).toList
      recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.RecursorsPresent recursors)
    (hbinders : binders.Nodup)
    (hruleDomains : ruleDomains.length = binders.length)
    (hselected : ∀ fv ∈ Hbound.fvars, fv ∈ binders) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  refine H.abstractedIotaResults Hargs Hresults ?_
  intro i hi hiarg hiresult Hentry Harg Hresult
  rcases Hbound.getElem_eq_fvar i hi with
    ⟨hiFvars, hsource⟩
  let fv := Hbound.fvars[i]
  have hargTr := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hi) hiarg
  have hfieldRoot : fv ∈ root.lctx.fvars :=
    Hbound.members fv (List.getElem_mem hiFvars)
  have hfield : fv ∈ binders :=
    hselected fv (List.getElem_mem hiFvars)
  have hsource' : u[i] = .fvar fv := hsource
  have HArgFv : TrExprS env Us (abstractForallContext ruleDomains Δ)
      ((Expr.fvar fv).abstractList binders) recursiveArgs[i] := by
    simpa [hsource'] using hargTr
  have hrecursorMemBefore : Hentry.recursorName ∈ recursors :=
    hrecursor i hi Hentry
  apply Hentry.outerAbstractedIotaResultCertificate_ofFresh_eq hsource'
    Hresult hfresh hctx hproj hrecursorMemBefore hfieldRoot hbinders hfield
      hruleDomains
  intro fieldVar hfieldSource
  have HArg' := HArgFv
  rw [hfieldSource] at HArg'
  have hfieldBound : fieldVar < ruleDomains.length := by
    rcases List.mem_iff_getElem.mp hfield with ⟨j, hj, hget⟩
    have hcanonical := Expr.abstractList_fvar_getElem
      hbinders j hj (k := 0)
    rw [hget, hfieldSource] at hcanonical
    have : fieldVar = binders.length - 1 - j := by
      cases hcanonical
      simp
    rw [hruleDomains]
    omega
  have hargEq : recursiveArgs[i] = .bvar fieldVar :=
    TrExprS.bvar_eq_of_abstractForallContext HArg' hfieldBound
  have hhead : recursiveArgs[i].bvarHead? = some fieldVar := by
    rw [hargEq]
    rfl
  exact List.mem_filterMap.mpr
    ⟨recursiveArgs[i], List.getElem_mem hiarg, hhead⟩

/-- Lift the freshness-derived pointwise result certificate across the exact
recursive-call array. The only remaining rule-local facts are recursor-name
membership and the de Bruijn head selected for each translated field. -/
theorem BoundGeneratedRecursiveCalls.iotaResults_ofFresh
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hbound : BoundFVarArray root u)
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      u.toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      v.toList recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (henv : env.Ordered)
    (hrecursor : ∀ exposedType,
      Lean.mkRecName
        indTypes[(AddInductive.getIIndices stats exposedType).1]!.name ∈
          recursors)
    (hheads : ∀ i (hi : i < recursiveArgs.length),
      ∃ field, recursiveArgs[i].bvarHead? = some field) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  apply H.iotaResults Hargs Hresults
  intro i hi hiarg hiresult Hentry Harg Hresult
  rcases Hbound.get_eq_fvar i hi with ⟨fv, hsource, hfieldRoot⟩
  rw [hsource] at Hentry Harg
  have hrecursorMem : Hentry.recursorName ∈ recursors := by
    simpa [BoundGeneratedRecursiveCall.recursorName] using
      hrecursor Hentry.exposedType
  rcases hheads i hiarg with ⟨field, hhead⟩
  have hfield : recursiveArgs[i].IsFieldApp
      (recursiveArgs.filterMap VExpr.bvarHead?) 0 :=
    VExpr.IsFieldApp.ofRecursiveArg
      (List.getElem_mem hiarg) hhead
  exact Hentry.iotaResultCertificate_ofFresh Hresult hfresh hctx hproj
    hrecursorMem henv hfieldRoot Harg hfield

/-- One generated iota rule retaining the constructor-field context and the
binder-aware certificate for every recursive result. -/
structure BoundGeneratedRecursorRule
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx : Nat) (rule : RecursorRule) where
  root : AddInductive.Context
  root_wf : BindingContextWF root
  target : Expr
  allArgs : Array Expr
  recursiveArgs : Array Expr
  recursiveResults : Array Expr
  minor_valid : minorIdx < minors.size
  params_bound : BoundFVarArray root stats.params
  motives_bound : BoundFVarArray root motives
  minors_bound : BoundFVarArray root minors
  outer_binders_nodup :
    ((params_bound.fvars ++ motives_bound.fvars) ++
      minors_bound.fvars).Nodup
  all_args_bound : BoundFVarArray root allArgs
  recursive_args_bound : BoundFVarArray root recursiveArgs
  recursive_args_sublist : recursiveArgs.toList.Sublist allArgs.toList
  all_args_nodup : all_args_bound.fvars.Nodup
  recursive_args_nodup : recursive_args_bound.fvars.Nodup
  all_args_outer_fresh : ∀ fv ∈ all_args_bound.fvars,
    fv ∉ (params_bound.fvars ++ motives_bound.fvars) ++ minors_bound.fvars
  recursive_calls : BoundGeneratedRecursiveCalls indTypes stats motives
    minors lvls root recursiveArgs recursiveResults recursiveArgs.size
  ctor_eq : rule.ctor = ctor.name
  fields_eq : rule.nfields = allArgs.size
  rhs_eq : rule.rhs =
    (root.lctx.mkLambda stats.params <| root.lctx.mkLambda motives <|
     root.lctx.mkLambda minors <| root.lctx.mkLambda allArgs <|
     mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults)

/-- Rule-local interface to the guarded recursive-result proof. Array
alignment and the fact that selected source fields are genuine retained free
variables are discharged by the binder-aware rule certificate. -/
theorem BoundGeneratedRecursorRule.iotaResults_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs recursiveResults : List VExpr}
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      H.recursiveArgs.toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      H.recursiveResults.toList recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (henv : env.Ordered)
    (hrecursor : ∀ exposedType,
      Lean.mkRecName
        indTypes[(AddInductive.getIIndices stats exposedType).1]!.name ∈
          recursors)
    (hheads : ∀ i (hi : i < recursiveArgs.length),
      ∃ field, recursiveArgs[i].bvarHead? = some field) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults :=
  H.recursive_calls.iotaResults_ofFresh H.recursive_args_bound
    Hargs Hresults hfresh hctx hproj henv hrecursor hheads

/-- All source binders closed by a generated rule are globally distinct:
outer recursor binders are no-alias by construction, while constructor fields
are fresh relative to that outer context. -/
theorem BoundGeneratedRecursorRule.binders_nodup
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    (((H.params_bound.fvars ++ H.motives_bound.fvars) ++
      H.minors_bound.fvars) ++ H.all_args_bound.fvars).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨H.outer_binders_nodup, H.all_args_nodup, ?_⟩
  intro outer houter field hfield heq
  subst outer
  exact H.all_args_outer_fresh field hfield houter

def BoundGeneratedRecursorRule.binders
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : List FVarId :=
  ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
    H.minors_bound.fvars) ++ H.all_args_bound.fvars

def BoundGeneratedRecursorRule.sourceRhsBody
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  mkAppN (mkAppN minors[minorIdx]! H.allArgs) H.recursiveResults

/-- Constructor application appearing as the major premise of the generated
iota left-hand side. -/
def BoundGeneratedRecursorRule.sourceConstructorMajor
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) H.allArgs

/-- Canonical source left-hand-side body determined by the residual target
returned from `loopCtorArgs`. -/
def BoundGeneratedRecursorRule.sourceLhsBody
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  let (ownerIdx, indices) := AddInductive.getIIndices stats H.target
  let recursor := .const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls
  (mkAppN
    (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices).app H.sourceConstructorMajor

/-- Proof-side source equation LHS closed over exactly the binders used by
the production RHS. `RecursorRule` stores only the RHS; the kernel reconstructs
this matching pattern from its recursor metadata. -/
def BoundGeneratedRecursorRule.sourceLhs
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  LocalContext.mkBindingList true H.root.lctx H.binders H.sourceLhsBody

def BoundGeneratedRecursorRule.all_binders_bound
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : BoundFVarArray H.root
      (stats.params ++ motives ++ minors ++ H.allArgs) :=
  ((H.params_bound.append H.motives_bound).append H.minors_bound).append
    H.all_args_bound

/-- The four nested production `mkLambda` calls are one exact, globally
no-alias lambda telescope over the retained binder sequence. -/
theorem BoundGeneratedRecursorRule.rhs_eq_bindingList
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    rule.rhs = LocalContext.mkBindingList true H.root.lctx
      H.binders H.sourceRhsBody := by
  rw [H.rhs_eq]
  symm
  unfold BoundGeneratedRecursorRule.binders
    BoundGeneratedRecursorRule.sourceRhsBody
  have hdecl : ∀ fv ∈
      ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
        H.minors_bound.fvars) ++ H.all_args_bound.fvars,
      ∃ decl, H.root.lctx.find? fv = some decl := by
    intro fv hfv
    have hmem : fv ∈ H.root.lctx.fvars := by
      rcases List.mem_append.mp hfv with houter | hall
      · rcases List.mem_append.mp houter with hpm | hminor
        · rcases List.mem_append.mp hpm with hparam | hmotive
          · exact H.params_bound.members fv hparam
          · exact H.motives_bound.members fv hmotive
        · exact H.minors_bound.members fv hminor
      · exact H.all_args_bound.members fv hall
    rcases H.root_wf.findCDecl fv hmem with
      ⟨index, name, type, bi, kind, hfind⟩
    exact ⟨.cdecl index fv name type bi kind, hfind⟩
  rw [LocalContext.mkBindingList_append_four hdecl H.binders_nodup]
  simp only [LocalContext.mkLambda, ← LocalContext.mkBinding_eq]
  have hp : ({ toList := H.params_bound.fvars.map Expr.fvar } :
      Array Expr) = stats.params := by
    simpa using H.params_bound.expressions.symm
  have hm : ({ toList := H.motives_bound.fvars.map Expr.fvar } :
      Array Expr) = motives := by
    simpa using H.motives_bound.expressions.symm
  have hmi : ({ toList := H.minors_bound.fvars.map Expr.fvar } :
      Array Expr) = minors := by
    simpa using H.minors_bound.expressions.symm
  have ha : ({ toList := H.all_args_bound.fvars.map Expr.fvar } :
      Array Expr) = H.allArgs := by
    simpa using H.all_args_bound.expressions.symm
  rw [hp, hm, hmi, ha]

theorem BoundGeneratedRecursorRule.rhsLambdaTelescope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    Expr.LambdaTelescope rule.rhs H.binders.length
      (H.sourceRhsBody.abstractList H.binders) := by
  rw [H.rhs_eq_bindingList]
  exact LocalContext.mkBindingList_lambdaTelescope
    (H.all_binders_bound.toLocalForallSelection
      H.root_wf).declarations

theorem BoundGeneratedRecursorRule.lhsLambdaTelescope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    Expr.LambdaTelescope H.sourceLhs H.binders.length
      (H.sourceLhsBody.abstractList H.binders) := by
  unfold BoundGeneratedRecursorRule.sourceLhs
  exact LocalContext.mkBindingList_lambdaTelescope
    (H.all_binders_bound.toLocalForallSelection
      H.root_wf).declarations

theorem BoundGeneratedRecursorRule.translatedLhsShape
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Htr : TrExprS env Us Δ H.sourceLhs lhs) :
    ∃ domains lhsBody,
      domains.length = H.binders.length ∧
      lhs = VExpr.wrapLams domains lhsBody ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.sourceLhsBody.abstractList H.binders) lhsBody :=
  TrExprS.lambdaTelescope_shape_with_context H.lhsLambdaTelescope Htr

/-- Simultaneous closing preserves the canonical recursor/constructor LHS
spines and abstracts every source argument pointwise. -/
theorem BoundGeneratedRecursorRule.abstractedSourceLhs
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let (ownerIdx, indices) := AddInductive.getIIndices stats H.target
    H.sourceLhsBody.abstractList H.binders =
      (mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls)
              (stats.params.map fun arg => arg.abstractList H.binders))
            (motives.map fun arg => arg.abstractList H.binders))
          (minors.map fun arg => arg.abstractList H.binders))
        (indices.map fun arg => arg.abstractList H.binders)).app
      (mkAppN
        (mkAppN (.const ctor.name stats.levels)
          (stats.params.map fun arg => arg.abstractList H.binders))
        (H.allArgs.map fun arg => arg.abstractList H.binders)) := by
  rcases htarget : AddInductive.getIIndices stats H.target with
    ⟨ownerIdx, indices⟩
  simp only [BoundGeneratedRecursorRule.sourceLhsBody, htarget,
    BoundGeneratedRecursorRule.sourceConstructorMajor,
    Expr.abstractList_app, Expr.abstractList_mkAppN,
    Expr.abstractList_const]

/-- Inverting the translated canonical LHS exposes the exact recursor and
constructor constant spines used by `IotaEquationCertificate`. -/
theorem BoundGeneratedRecursorRule.translatedLhsResidual
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceLhsBody.abstractList H.binders) lhsBody) :
    ∃ recursorLevels leadingArgs ctorLevels ctorArgs,
      lhsBody = VExpr.mkApps
        (.const (Lean.mkRecName indTypes[ownerIdx]!.name) recursorLevels)
        (leadingArgs ++
          [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs]) ∧
      lvls.mapM (VLevel.ofLevel Us) = some recursorLevels ∧
      stats.levels.mapM (VLevel.ofLevel Us) = some ctorLevels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        ((stats.params.map fun arg => arg.abstractList H.binders).toList ++
          (motives.map fun arg => arg.abstractList H.binders).toList ++
          (minors.map fun arg => arg.abstractList H.binders).toList ++
          (indices.map fun arg => arg.abstractList H.binders).toList)
        leadingArgs ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        ((stats.params.map fun arg => arg.abstractList H.binders).toList ++
          (H.allArgs.map fun arg => arg.abstractList H.binders).toList)
        ctorArgs := by
  have hsource := H.abstractedSourceLhs
  rw [htarget] at hsource
  rw [hsource] at Htr
  let leadingSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList ++
    (motives.map fun arg => arg.abstractList H.binders).toList ++
    (minors.map fun arg => arg.abstractList H.binders).toList ++
    (indices.map fun arg => arg.abstractList H.binders).toList
  let ctorArgsSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList ++
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
  let ctorSource :=
    mkAppN
      (mkAppN (.const ctor.name stats.levels)
        (stats.params.map fun arg => arg.abstractList H.binders))
      (H.allArgs.map fun arg => arg.abstractList H.binders)
  have hrecursorHead :
      ((mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls)
              (stats.params.map fun arg => arg.abstractList H.binders))
            (motives.map fun arg => arg.abstractList H.binders))
          (minors.map fun arg => arg.abstractList H.binders))
        (indices.map fun arg => arg.abstractList H.binders)).app
          ctorSource).getAppFn =
        .const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls := by
    simp only [Expr.getAppFn, Expr.getAppFn_mkAppN]
  rcases checkPositivityStep.TrExprS.constAppSpine Htr hrecursorHead with
    ⟨recursorLevels, translatedArgs, hrecursorSpine, hrecursorLevels,
      HtranslatedArgs⟩
  have HtranslatedArgs' : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (leadingSource ++ [ctorSource]) translatedArgs := by
    simpa only [leadingSource, ctorSource, Expr.getAppArgsList_app,
      Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append, List.append_assoc]
      using HtranslatedArgs
  rcases checkPositivityStep.List.Forall₂.split_left HtranslatedArgs' with
    ⟨leadingArgs, translatedMajorTail, rfl, Hleading, HmajorTail⟩
  have hmajor : ∃ translatedMajor,
      translatedMajorTail = [translatedMajor] ∧
      TrExprS env Us (abstractForallContext domains Δ)
        ctorSource translatedMajor := by
    cases HmajorTail with
    | cons Hctor Hnil =>
      cases Hnil
      exact ⟨_, rfl, Hctor⟩
  rcases hmajor with ⟨translatedMajor, rfl, Hctor⟩
  have hctorHead : ctorSource.getAppFn =
      .const ctor.name stats.levels := by
    simp only [ctorSource, Expr.getAppFn_mkAppN, Expr.getAppFn]
  rcases checkPositivityStep.TrExprS.constAppSpine Hctor hctorHead with
    ⟨ctorLevels, ctorArgs, hctorSpine, hctorLevels, HctorArgs⟩
  have HctorArgs' : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ctorArgsSource ctorArgs := by
    simpa only [ctorArgsSource, ctorSource,
      Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append,
      List.append_assoc] using HctorArgs
  have hmajorRebuild := VExpr.mkApps_getAppFnArgs translatedMajor
  rw [hctorSpine] at hmajorRebuild
  have hlhsRebuild := VExpr.mkApps_getAppFnArgs lhsBody
  rw [hrecursorSpine] at hlhsRebuild
  refine ⟨recursorLevels, leadingArgs, ctorLevels, ctorArgs, ?_,
    hrecursorLevels, hctorLevels, ?_, ?_⟩
  · rw [← hmajorRebuild] at hlhsRebuild
    exact hlhsRebuild.symm
  · simpa [leadingSource] using Hleading
  · simpa [ctorArgsSource] using HctorArgs'

/-- Proof-side construction record for the `VDefEq` corresponding to one
production `RecursorRule`. The executable record stores only its constructor,
field count, and RHS; this certificate makes the reconstructed LHS, common
telescope, and equation type an explicit refinement boundary. -/
structure BoundGeneratedRecursorRule.EquationTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx) (rule : VDefEq) where
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  domains_length : domains.length = H.binders.length
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  lhs_residual : TrExprS trEnv Us (abstractForallContext domains Δ)
    (H.sourceLhsBody.abstractList H.binders) lhsBody
  rhs_residual : TrExprS trEnv Us (abstractForallContext domains Δ)
    (H.sourceRhsBody.abstractList H.binders) rhsBody

/-- Common recursor parameters become closed de Bruijn variables under the
generated rule telescope, so their syntax translation is unique. -/
theorem BoundGeneratedRecursorRule.abstractedParamsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (stats.params.map fun arg =>
      arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, heq⟩
  have hiArray : i < stats.params.size := by simpa using hi
  rcases H.params_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.params_bound.fvars[i]
  have hsource' : stats.params[i] = .fvar fv := hsource
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_left _ <| List.mem_append_left _ <|
      List.mem_append_left _ (List.getElem_mem hiFvars)
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let paramVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar paramVar := by
    simpa [BoundGeneratedRecursorRule.binders, paramVar,
      List.append_assoc] using habstract
  have hentry :
      (stats.params.map fun arg => arg.abstractList H.binders).toList[i] =
        .bvar paramVar := by
    calc
      _ = stats.params[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource']
      _ = .bvar paramVar := habstract'
  rw [← heq, hentry]
  trivial

/-- Equation shape together with the exact translated constructor-field
suffix needed by the recursive-field and RHS certificates. -/
structure BoundGeneratedRecursorRule.IotaEquationTranslationCertificate
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx)
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  shape : IotaEquationCertificate decl block owner ctor rule
  domains_length : shape.domains.length = H.binders.length
  rhs_residual : TrExprS trEnv Us
    (abstractForallContext shape.domains Δ)
    (H.sourceRhsBody.abstractList H.binders) shape.rhsBody
  field_args : List.Forall₂
    (TrExprS trEnv Us (abstractForallContext shape.domains Δ))
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
    (shape.ctorArgs.drop decl.nparams)

/-- The retained source rule and its explicit `VDefEq` translation determine
the complete non-recursive iota-equation shape. Arity premises are deliberately
stated at the concrete array boundary so `RecursorCardinalityCertificate` can
discharge them without coupling this local theorem to the outer loop. -/
theorem BoundGeneratedRecursorRule.iotaEquationCertificate
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.EquationTranslation trEnv Us Δ rule)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (hparams : stats.params.size = decl.nparams)
    (hmotives : motives.size = decl.types.length)
    (hminors : minors.size = decl.ownedConstructors.length)
    (hindices : indices.size = owner.numIndices)
    (hownerName : indTypes[ownerIdx]!.name = owner.name)
    (recursor : VConstVal)
    (hrecursorMem : recursor ∈ block.recursors)
    (hrecursorName : recursor.name = decl.recursorName owner)
    (hrecursorUvars : lvls.length = recursor.uvars)
    (ctor : VConstVal)
    (hctorName : sourceCtor.name = ctor.name)
    (hctorUvars : stats.levels.length = decl.uvars)
    (hruleUvars : rule.uvars = recursor.uvars) :
    Nonempty (H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule) := by
  rcases H.translatedLhsResidual htarget Htr.lhs_residual with
    ⟨recursorLevels, leadingArgs, ctorLevels, ctorArgs, hlhs,
      hrecursorLevels, hctorLevels, Hleading, HctorArgs⟩
  let paramSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList
  let leadingTailSource :=
    (motives.map fun arg => arg.abstractList H.binders).toList ++
    (minors.map fun arg => arg.abstractList H.binders).toList ++
    (indices.map fun arg => arg.abstractList H.binders).toList
  let ctorTailSource :=
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
  have Hleading' : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Htr.domains Δ))
      (paramSource ++ leadingTailSource) leadingArgs := by
    simpa only [paramSource, leadingTailSource, List.append_assoc]
      using Hleading
  have HctorArgs' : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Htr.domains Δ))
      (paramSource ++ ctorTailSource) ctorArgs := by
    simpa only [paramSource, ctorTailSource] using HctorArgs
  rcases checkPositivityStep.List.Forall₂.split_left Hleading' with
    ⟨leadingParams, leadingTail, hleadingArgs, HleadingParams, _⟩
  rcases checkPositivityStep.List.Forall₂.split_left HctorArgs' with
    ⟨ctorParams, ctorTail, hctorArgs, HctorParams, HctorTail⟩
  have hparamTargets : leadingParams = ctorParams :=
    Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
      HleadingParams HctorParams (by
        simpa only [paramSource] using H.abstractedParamsUnique)
  have hparamSourceLength : paramSource.length = decl.nparams := by
    simp [paramSource, hparams]
  have hleadingParamsLength : leadingParams.length = decl.nparams := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      HleadingParams
    omega
  have hctorParamsLength : ctorParams.length = decl.nparams := by
    rw [← hparamTargets]
    exact hleadingParamsLength
  have hleadingLength : leadingArgs.length = decl.nparams +
      decl.types.length + decl.ownedConstructors.length + owner.numIndices := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hleading
    simpa [hparams, hmotives, hminors, hindices, Nat.add_assoc]
      using hlen.symm
  have hctorLength : ctorArgs.length = decl.nparams + H.allArgs.size := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' HctorArgs
    simpa [hparams] using hlen.symm
  have hbindersLength : H.binders.length = stats.params.size + motives.size +
      minors.size + H.allArgs.size := by
    have hp : stats.params.size = H.params_bound.fvars.length := by
      simpa using congrArg Array.size H.params_bound.expressions
    have hm : motives.size = H.motives_bound.fvars.length := by
      simpa using congrArg Array.size H.motives_bound.expressions
    have hmi : minors.size = H.minors_bound.fvars.length := by
      simpa using congrArg Array.size H.minors_bound.expressions
    have ha : H.allArgs.size = H.all_args_bound.fvars.length := by
      simpa using congrArg Array.size H.all_args_bound.expressions
    unfold BoundGeneratedRecursorRule.binders
    simp only [List.length_append]
    omega
  let Hshape : IotaEquationCertificate decl block owner ctor rule := {
    recursor := recursor
    recursor_mem := hrecursorMem
    recursor_name := hrecursorName
    rule_uvars := hruleUvars
    domains := Htr.domains
    lhsBody := Htr.lhsBody
    rhsBody := Htr.rhsBody
    typeBody := Htr.typeBody
    lhs_wrapped := Htr.lhs_wrapped
    rhs_wrapped := Htr.rhs_wrapped
    type_wrapped := Htr.type_wrapped
    recursorLevels := recursorLevels
    leadingArgs := leadingArgs
    ctorLevels := ctorLevels
    ctorArgs := ctorArgs
    lhs_pattern := by
      rw [hrecursorName, VInductDecl.recursorName_eq_mkRecName]
      simpa [hownerName, hctorName] using hlhs
    recursor_levels := by
      rw [← hrecursorUvars]
      exact (checkPositivityStep.List.mapM_some_length
        hrecursorLevels).symm
    ctor_levels := by
      rw [← hctorUvars]
      exact (checkPositivityStep.List.mapM_some_length hctorLevels).symm
    leading_arity := hleadingLength
    constructor_arity := by omega
    parameter_args := by
      rw [hleadingArgs, hctorArgs, ← hparamTargets]
      rw [← hleadingParamsLength]
      simp
    domains_arity := by
      rw [Htr.domains_length, hbindersLength, hparams, hmotives, hminors,
        hctorLength]
      omega }
  refine ⟨{
    shape := Hshape
    domains_length := Htr.domains_length
    rhs_residual := Htr.rhs_residual
    field_args := ?_ }⟩
  change List.Forall₂
    (TrExprS trEnv Us (abstractForallContext Htr.domains Δ))
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
    (ctorArgs.drop decl.nparams)
  rw [hctorArgs]
  simpa [ctorTailSource, hctorParamsLength] using HctorTail

/-- Outer-loop form of `iotaEquationCertificate`: the header statistics and
`mkRecInfos` cardinality certificates discharge every local arity premise,
while source declaration translation identifies the selected mutual owner. -/
theorem BoundGeneratedRecursorRule.iotaEquationCertificate_ofCardinality
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.EquationTranslation trEnv Us Δ rule)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (Hstats : checkPositivityStep.ValidAppStatsWF statsEnv statsParams statsCtx
      stats decl depth)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (hmotives : motives = recInfos.map (·.motive))
    (hminors : minors = recInfos.flatMap (·.minors))
    (hvalid : AddInductive.isValidIndApp? stats H.target = some ownerIdx)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (hownerLt : ownerIdx < decl.types.length)
    (howner : decl.types[ownerIdx]'hownerLt = owner)
    (recursor : VConstVal)
    (hrecursorMem : recursor ∈ block.recursors)
    (hrecursorName : recursor.name = decl.recursorName owner)
    (hrecursorUvars : lvls.length = recursor.uvars)
    (ctor : VConstVal)
    (hctorName : sourceCtor.name = ctor.name)
    (hruleUvars : rule.uvars = recursor.uvars) :
    Nonempty (H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule) := by
  have hdeclOwner : ownerIdx < decl.types.length := hownerLt
  have hsourceOwner : ownerIdx < indTypes.size := by
    have hlen := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
    have hsize : indTypes.size = decl.types.length := by simpa using hlen
    rw [hsize]
    exact hdeclOwner
  have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hdecl
    ownerIdx (by simpa using hsourceOwner) hdeclOwner
  have hownerName : indTypes[ownerIdx]!.name = owner.name := by
    have htranslated : decl.types[ownerIdx].name =
        indTypes[ownerIdx].name := by
      simpa using Howner.header.name
    rw [← howner]
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using
      htranslated.symm
  have hindexArity : indices.size = owner.numIndices := by
    have h := checkPositivityStep.getIIndices.index_arity hvalid
    rw [htarget] at h
    have hlen : stats.nindices.size = decl.types.length := by
      have := congrArg List.length Hstats.indices
      simpa using this
    have hget := congrArg (fun xs => xs[ownerIdx]?) Hstats.indices
    have hn : stats.nindices[ownerIdx]! =
        decl.types[ownerIdx].numIndices := by
      simpa [Array.getElem!_eq_getD, Array.getD, hownerLt, hlen] using hget
    calc
      indices.size = stats.nindices[ownerIdx]! := h
      _ = decl.types[ownerIdx].numIndices := hn
      _ = owner.numIndices := by rw [howner]
  apply H.iotaEquationCertificate (recursor := recursor) (ctor := ctor)
    Htr htarget Hcard.params
  · rw [hmotives]
    exact Hcard.motives
  · rw [hminors]
    exact Hcard.minors
  · exact hindexArity
  · exact hownerName
  · exact hrecursorMem
  · exact hrecursorName
  · exact hrecursorUvars
  · exact hctorName
  · exact Hstats.levels
  · exact hruleUvars

/-- Simultaneous abstraction turns the selected minor free variable into one
in-scope de Bruijn variable and preserves the field/result application
spines pointwise. -/
theorem BoundGeneratedRecursorRule.abstractedSourceRhs
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∃ minorVar,
      minorVar < H.binders.length ∧
      H.sourceRhsBody.abstractList H.binders =
        mkAppN
          (mkAppN (.bvar minorVar)
            (H.allArgs.map fun arg => arg.abstractList H.binders))
          (H.recursiveResults.map fun result =>
            result.abstractList H.binders) := by
  rcases H.minors_bound.getElem_eq_fvar minorIdx H.minor_valid with
    ⟨hiFvars, hminor⟩
  let fv := H.minors_bound.fvars[minorIdx]
  have hmem : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders fv
    simp [List.getElem_mem hiFvars]
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
  let minorVar := H.binders.length - 1 - i
  refine ⟨minorVar, by omega, ?_⟩
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup i hi (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar minorVar := by
    simpa [BoundGeneratedRecursorRule.binders, minorVar] using habstract
  have hminorBang : minors[minorIdx]! = .fvar fv := by
    rw [Array.getElem!_eq_getD, Array.getD, dif_pos H.minor_valid]
    exact hminor
  unfold BoundGeneratedRecursorRule.sourceRhsBody
  rw [Expr.abstractList_mkAppN, Expr.abstractList_mkAppN,
    hminorBang, habstract']

/-- Translation of the exact production rule RHS exposes the abstract rule
telescope and leaves only the simultaneously abstracted minor application as
the residual translation obligation. -/
theorem BoundGeneratedRecursorRule.translatedRhsShape
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Htr : TrExprS env Us Δ rule.rhs rhs) :
    ∃ domains rhsBody,
      domains.length = H.binders.length ∧
      rhs = VExpr.wrapLams domains rhsBody ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.sourceRhsBody.abstractList H.binders) rhsBody :=
  TrExprS.lambdaTelescope_shape_with_context H.rhsLambdaTelescope Htr

theorem BoundGeneratedRecursorRule.translatedRhsShape_noFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Htr : TrExprS env Us Δ rule.rhs rhs)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains rhsBody,
      domains.length = H.binders.length ∧
      rhs = VExpr.wrapLams domains rhsBody ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.sourceRhsBody.abstractList H.binders) rhsBody ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false :=
  TrExprS.lambdaTelescope_shape_with_context_noFresh
    hfresh hctx hproj H.rhsLambdaTelescope Htr

/-- Inverting the translated residual yields the exact abstract minor spine,
split between translated constructor fields and translated recursive
results. -/
theorem BoundGeneratedRecursorRule.translatedRhsResidual
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody) :
    ∃ minorVar fieldArgs recursiveResults,
      minorVar < domains.length ∧
      List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
        (H.allArgs.map fun arg => arg.abstractList H.binders).toList
        fieldArgs ∧
      List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders).toList recursiveResults ∧
      rhsBody = VExpr.mkApps (.bvar minorVar)
        (fieldArgs ++ recursiveResults) := by
  rcases H.abstractedSourceRhs with ⟨minorVar, hminor, habstract⟩
  rw [habstract] at Htr
  have Houter : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList
        (mkAppN (.bvar minorVar)
          (H.allArgs.map fun arg => arg.abstractList H.binders))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders).toList) rhsBody := by
    simpa only [mkAppN, Expr.mkAppList_eq_foldl,
      ← Array.foldl_toList, Array.toList_map,
      Expr.foldl_mkApp_eq] using Htr
  rcases checkPositivityStep.TrExprS.mkAppList_inv Houter with
    ⟨minorApp, recursiveResults, HminorApp, Hresults, hrhs⟩
  have Hinner : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList (.bvar minorVar)
        (H.allArgs.map fun arg => arg.abstractList H.binders).toList)
      minorApp := by
    simpa only [mkAppN, Expr.mkAppList_eq_foldl,
      ← Array.foldl_toList, Array.toList_map,
      Expr.foldl_mkApp_eq] using HminorApp
  rcases checkPositivityStep.TrExprS.mkAppList_inv Hinner with
    ⟨minor, fieldArgs, Hminor, Hfields, hminorApp⟩
  have hminorEq := TrExprS.bvar_eq_of_abstractForallContext Hminor
    (by omega)
  subst minor
  refine ⟨minorVar, fieldArgs, recursiveResults, by omega,
    Hfields, Hresults, ?_⟩
  rw [hrhs, hminorApp]
  simp [VExpr.mkApps, List.foldl_append]

/-- The rule certificate itself supplies the selected-field membership needed
to guard every recursively generated result after closing the rule telescope. -/
theorem BoundGeneratedRecursorRule.abstractedIotaResults_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs recursiveResults : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (Hresults : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveResults.map fun result =>
        result.abstractList H.binders).toList recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursive_calls.RecursorsPresent recursors)
    (hdomains : domains.length = H.binders.length) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  apply H.recursive_calls.abstractedIotaResults_ofFresh
    H.recursive_args_bound Hargs Hresults hfresh hctx hproj hrecursor
      H.binders_nodup hdomains
  intro fv hfv
  have hfield : fv ∈ H.all_args_bound.fvars :=
    H.recursive_args_bound.fvars_subset_of_sublist H.all_args_bound
      H.recursive_args_sublist hfv
  unfold BoundGeneratedRecursorRule.binders
  exact List.mem_append_right _ hfield

/-- Every de Bruijn head obtained from a translated selected constructor
field is in the closed rule telescope. -/
theorem BoundGeneratedRecursorRule.abstractedRecursiveHeadsInScope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hdomains : domains.length = H.binders.length) :
    ∀ field ∈ recursiveArgs.filterMap VExpr.bvarHead?,
      field < domains.length := by
  intro field hfield
  rcases List.mem_filterMap.mp hfield with ⟨arg, harg, hhead⟩
  rcases List.mem_iff_getElem.mp harg with ⟨i, hiArgs, hargEq⟩
  have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hiSource : i <
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList.length :=
    by omega
  have hiArray : i < H.recursiveArgs.size := by simpa using hiSource
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i hiSource hiArgs
  rcases H.recursive_args_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.recursive_args_bound.fvars[i]
  have hsource' : H.recursiveArgs[i] = .fvar fv := hsource
  have hselectedAll : fv ∈ H.all_args_bound.fvars :=
    H.recursive_args_bound.fvars_subset_of_sublist H.all_args_bound
      H.recursive_args_sublist (List.getElem_mem hiFvars)
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ hselectedAll
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let fieldVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar fieldVar := by
    simpa [BoundGeneratedRecursorRule.binders, fieldVar] using habstract
  have hsourceAbstract :
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList[i] =
        .bvar fieldVar := by
    calc
      _ = H.recursiveArgs[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource']
      _ = .bvar fieldVar := habstract'
  rw [hsourceAbstract] at Harg
  have hfieldVarBound : fieldVar < domains.length := by
    rw [hdomains]
    omega
  have htranslated := TrExprS.bvar_eq_of_abstractForallContext
    Harg hfieldVarBound
  rw [hargEq] at htranslated
  have hfieldEq : field = fieldVar := by
    rw [htranslated] at hhead
    unfold VExpr.bvarHead? at hhead
    exact (Option.some.inj hhead).symm
  rw [hfieldEq]
  exact hfieldVarBound

/-- Closing the generated rule turns every constructor-field source into a
de Bruijn variable, hence into syntax with a unique translation. -/
theorem BoundGeneratedRecursorRule.abstractedAllArgsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (H.allArgs.map fun arg => arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, heq⟩
  have hiArray : i < H.allArgs.size := by simpa using hi
  rcases H.all_args_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.all_args_bound.fvars[i]
  have hsource' : H.allArgs[i] = .fvar fv := hsource
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ (List.getElem_mem hiFvars)
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let fieldVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar fieldVar := by
    simpa [BoundGeneratedRecursorRule.binders, fieldVar] using habstract
  have hentry :
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList[i] =
        .bvar fieldVar := by
    calc
      _ = H.allArgs[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource']
      _ = .bvar fieldVar := habstract'
  rw [← heq, hentry]
  trivial

/-- Selected recursive fields inherit translation uniqueness from the full
constructor-field array after simultaneous closing. -/
theorem BoundGeneratedRecursorRule.abstractedRecursiveArgsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (H.recursiveArgs.map fun arg =>
      arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  apply H.abstractedAllArgsUnique e
  have hsub := H.recursive_args_sublist.map
    (fun arg => arg.abstractList H.binders)
  exact List.Sublist.mem he (by simpa using hsub)

/-- Assemble the abstract iota RHS certificate directly from the translated
production RHS and the independently translated selected-field spine. -/
theorem BoundGeneratedRecursorRule.iotaRhsCertificate_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs : List VExpr}
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursive_calls.RecursorsPresent recursors) :
    ∃ fieldArgs,
      Nonempty (IotaRhsCertificate recursors domains fieldArgs recursiveArgs
        rhsBody) := by
  rcases H.translatedRhsResidual hdomains Htr with
    ⟨minorVar, fieldArgs, recursiveResults, hminor, Hfields,
      Hresults, hrhs⟩
  refine ⟨fieldArgs, ⟨{
    minorVar := minorVar
    minor_in_scope := hminor
    recursiveResults := recursiveResults
    rhs_eq := hrhs
    fieldVars := recursiveArgs.filterMap VExpr.bvarHead?
    fieldVars_eq := rfl
    fields_in_scope := H.abstractedRecursiveHeadsInScope Hargs hdomains
    fields_recursor_free :=
      checkPositivityStep.List.Forall₂.targets_noFreshConsts
        Hfields hfresh hctx hproj
    recursive_results := H.abstractedIotaResults_ofFresh
      Hargs Hresults hfresh hctx hproj hrecursor hdomains
  }⟩⟩

/-- Exact-spine form of `iotaRhsCertificate_ofFresh`. Syntactic uniqueness of
the closed constructor fields identifies the RHS inversion output with the
field spine shared by the equation and recursive-field certificates. -/
theorem BoundGeneratedRecursorRule.iotaRhsCertificateFor_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {fieldArgs recursiveArgs : List VExpr}
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody)
    (Hfields : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList
      fieldArgs)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursive_calls.RecursorsPresent recursors) :
    Nonempty (IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) := by
  rcases H.translatedRhsResidual hdomains Htr with
    ⟨minorVar, generatedFields, recursiveResults, hminor,
      HgeneratedFields, Hresults, hrhs⟩
  have hfieldsEq : generatedFields = fieldArgs :=
    Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
      HgeneratedFields Hfields H.abstractedAllArgsUnique
  subst generatedFields
  exact ⟨{
    minorVar := minorVar
    minor_in_scope := hminor
    recursiveResults := recursiveResults
    rhs_eq := hrhs
    fieldVars := recursiveArgs.filterMap VExpr.bvarHead?
    fieldVars_eq := rfl
    fields_in_scope := H.abstractedRecursiveHeadsInScope Hargs hdomains
    fields_recursor_free :=
      checkPositivityStep.List.Forall₂.targets_noFreshConsts
        Hfields hfresh hctx hproj
    recursive_results := H.abstractedIotaResults_ofFresh
      Hargs Hresults hfresh hctx hproj hrecursor hdomains
  }⟩

/-- Final pointwise semantic bridge for a generated rule. The equation and
recursive-field certificates remain independent inputs; all executable RHS
shape and guardedness obligations are discharged here. -/
theorem BoundGeneratedRecursorRule.iotaRule_ofCertificates
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hshape : IotaEquationCertificate decl block owner ctor rule)
    {fields : List (decl.RecursiveField env)}
    {recursiveArgs : List VExpr}
    (Hfield : IotaFieldCertificate env decl
      (Hshape.ctorArgs.drop decl.nparams) fields recursiveArgs)
    (hdomains : Hshape.domains.length = H.binders.length)
    (Htr : TrExprS trEnv Us
      (abstractForallContext Hshape.domains Δ)
      (H.sourceRhsBody.abstractList H.binders) Hshape.rhsBody)
    (Hfields : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Hshape.domains Δ))
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList
      (Hshape.ctorArgs.drop decl.nparams))
    (Hargs : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Hshape.domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hshape.domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false)
    (hrecursor : H.recursive_calls.RecursorsPresent
      (block.recursors.map (·.name))) :
    Nonempty (decl.IotaRule env block owner ctor rule) := by
  have Hrhs := H.iotaRhsCertificateFor_ofFresh hdomains Htr Hfields Hargs
    hfresh hctx hproj hrecursor
  rcases Hrhs with ⟨Hrhs⟩
  exact ⟨VInductDecl.IotaRule.ofCertificates Hshape Hfield Hrhs⟩

/-- Complete pointwise bridge from an explicitly reconstructed equation and
the executable recursive-field selection trace to the independent iota-rule
judgment. This removes `IotaEquationCertificate` and `IotaFieldCertificate`
as arbitrary external premises at the generated-rule boundary. -/
theorem BoundGeneratedRecursorRule.iotaRule_ofTranslationCertificate
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl H.allArgs
      H.recursiveArgs selections)
    {recursiveArgs : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS trEnv Us
        (abstractForallContext Hequation.shape.domains Δ))
      (H.recursiveArgs.map fun arg =>
        arg.abstractList H.binders).toList recursiveArgs)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hequation.shape.domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false)
    (hrecursor : H.recursive_calls.RecursorsPresent
      (block.recursors.map (·.name))) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) := by
  let Hselection' := Hselection.map
    (fun arg => arg.abstractList H.binders)
  rcases Hselection'.exists_materialization Hargs with ⟨fields, Hfields⟩
  let Hfield := Hfields.iotaFieldCertificate Hselection'
    Hequation.field_args Hargs H.abstractedRecursiveArgsUnique
  exact H.iotaRule_ofCertificates Hequation.shape Hfield
    Hequation.domains_length Hequation.rhs_residual
    Hequation.field_args Hargs hfresh hctx hproj hrecursor

/-- Complete local translation payload for one generated source rule. Unlike
`IotaRule`, every field refers directly to retained executable data; global
recursor installation and freshness are supplied once for the enclosing
batch. -/
structure BoundGeneratedRecursorRule.IotaRuleTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx)
    (semanticEnv : VEnv) (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  equation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
    owner ctor rule
  selections : List (RecursorRecursiveDomain semanticEnv decl)
  selection : RecursorFieldSelections semanticEnv decl H.allArgs
    H.recursiveArgs selections
  owner_alignment : H.recursive_calls.OwnerAlignment decl selections
  recursiveArgs : List VExpr
  args : List.Forall₂
    (TrExprS trEnv Us
      (abstractForallContext equation.shape.domains Δ))
    (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
    recursiveArgs
  context_free : VLCtx.NoIndConsts (block.recursors.map (·.name))
    (abstractForallContext equation.shape.domains Δ)

/-- Ordered binder-aware coverage of a constructor suffix. -/
inductive BoundGeneratedRecursorRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      [] start []
  | cons :
      Nonempty (BoundGeneratedRecursorRule indTypes stats motives minors
        lvls ctor start rule) →
      BoundGeneratedRecursorRules indTypes stats motives minors lvls
        ctors (start + 1) rules →
      BoundGeneratedRecursorRules indTypes stats motives minors lvls
        (ctor :: ctors) start (rule :: rules)

theorem BoundGeneratedRecursorRules.length
    (H : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) : rules.length = ctors.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem BoundGeneratedRecursorRules.entry
    (H : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      Nonempty (BoundGeneratedRecursorRule indTypes stats motives minors
        lvls ctors[i] (start + i) rules[i]) := by
  induction H with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor start rule ctors rules Hrule Htail ih =>
      intro i hctor hrule
      cases i with
      | zero => simpa using Hrule
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        simpa only [List.getElem_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 i] using h

namespace mkRecRules.loopU

/-- Binder-aware refinement of the production recursive-result loop. -/
theorem boundGeneratedCalls
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hc : BindingContextWF c)
    (Hprefix : BoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls c u v i)
    (Hk : ∀ v,
      BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
        c u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      fun uiTy xs => do
        let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
        let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
        let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
          motives) minors) itIndices
        return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => Nonempty (BoundGeneratedRecursiveCall indTypes stats
            motives minors lvls c u[i] value)) := by
      refine mkRecInfos.loopUArgs.resultBindings
        (Q := fun value => Nonempty (BoundGeneratedRecursiveCall indTypes
          stats motives minors lvls c u[i] value)) u[i] buildCall c Hc ?_
      intro uiTy xs c' Hc' Hxs Hle
      exact Except.WF.pure ⟨{
        exposedType := uiTy
        localArgs := xs
        current := c'
        current_wf := Hc'
        current_extends := Hle
        arguments_bound := Hxs
        value_eq := rfl }⟩
    exact hval.bind fun value Hvalue => by
      rcases Hvalue with ⟨Hvalue⟩
      exact boundGeneratedCalls Hc
        (Hprefix.push hnext Hvalue) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.boundGeneratedCallsFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hc : BindingContextWF c)
    (Hk : ∀ v,
      BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
        c u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.boundGeneratedCalls Hc
    (BoundGeneratedRecursiveCalls.empty
      indTypes stats motives minors lvls c u) Hk

namespace mkRecInfos.loopCtorArgs.loop

/-- Operational binder refinement for constructor-field classification. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hbu : FreshBoundFVarArray root c bu)
    (Hu : FreshBoundFVarArray root c u)
    (Hselected : u.toList.Sublist bu.toList)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ t bu u c, BindingContextWF c →
      FreshBoundFVarArray root c bu → FreshBoundFVarArray root c u →
      u.toList.Sublist bu.toList → BindingContextLE root c →
      (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      cases hparam : stats.params[i]? with
      | some param =>
        change (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
          (body.instantiate1 param) (i + 1) bu u fuel c).WF Q
        exact ih Hc Hbu Hu Hselected Hroot
      | none =>
        change (Lean4Lean.withLocalDecl name bi dom.consumeTypeAnnotations
          (fun arg => do
            let bu := bu.push arg
            let u := if (← AddInductive.isRecArg stats dom).isSome then
              u.push arg else u
            AddInductive.mkRecInfos.loopCtorArgs.loop stats k
              (body.instantiate1 arg) (i + 1) bu u fuel) c).WF Q
        unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
          AddInductive.instMonadLocalNameGeneratorM
          AddInductive.instMonadWithReaderOfLocalContextM
        let c' : AddInductive.Context := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }
        change (AddInductive.isRecArg stats dom c' >>= fun selected =>
          AddInductive.mkRecInfos.loopCtorArgs.loop stats
            k (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            (bu.push (.fvar ⟨c.ngen.curr⟩))
            (if selected.isSome then u.push (.fvar ⟨c.ngen.curr⟩) else u)
            fuel c') |>.WF Q
        have hclass : (AddInductive.isRecArg stats dom c').WF
            (fun _ => True) := by
          intro _ _
          trivial
        refine hclass.bind fun selected _ => ?_
        let Hc' := Hc.withLocalDecl name dom.consumeTypeAnnotations bi
        let hstep := BindingContextLE.withLocalDecl c name
          dom.consumeTypeAnnotations bi
        cases selected with
        | none =>
          have hselected' : u.toList.Sublist
              (bu.push (.fvar ⟨c.ngen.curr⟩)).toList := by
            simpa using Hselected.trans
              (List.sublist_append_left bu.toList
                [.fvar ⟨c.ngen.curr⟩])
          exact ih Hc'
            (Hbu.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
            (Hu.weaken name dom.consumeTypeAnnotations bi)
            hselected'
            (Hroot.trans hstep)
        | some target =>
          have hselected' : (u.push (.fvar ⟨c.ngen.curr⟩)).toList.Sublist
              (bu.push (.fvar ⟨c.ngen.curr⟩)).toList := by
            simpa using
              Hselected.append_right [.fvar ⟨c.ngen.curr⟩]
          exact ih Hc'
            (Hbu.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
            (Hu.pushCurrent Hc Hroot name dom.consumeTypeAnnotations bi)
            hselected'
            (Hroot.trans hstep)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj =>
      change (k _ bu u c).WF Q
      exact Hk _ _ _ _ Hc Hbu Hu Hselected Hroot

end mkRecInfos.loopCtorArgs.loop

theorem mkRecInfos.loopCtorArgs.resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (t : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hk : ∀ t bu u c', BindingContextWF c' →
      FreshBoundFVarArray c c' bu → FreshBoundFVarArray c c' u →
      u.toList.Sublist bu.toList → BindingContextLE c c' →
      (k t bu u c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopCtorArgs
  exact mkRecInfos.loopCtorArgs.loop.resultBindings stats k Hc
    (FreshBoundFVarArray.empty c) (FreshBoundFVarArray.empty c)
    .slnil (BindingContextLE.refl c) Hk

namespace mkRecRules.loopCtors

/-- The complete rule traversal retains the constructor-field binding context
and the bound recursive-call evidence for every emitted rule. -/
theorem boundGeneratedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule)
    (start : Nat) (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminorsRoom : start + ctors.length ≤ minors.size) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          BoundGeneratedRecursorRules indTypes stats motives minors lvls
            ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start c with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      refine ⟨[], ?_, .nil, by simp⟩
      simp
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecRules.loopCtors]
      have hone :
          ((fun minorIdx => AddInductive.mkRecInfos.loopCtorArgs stats
            ctor.type fun _ bu u =>
              AddInductive.mkRecRules.loopU indTypes stats motives minors
                lvls u 0 #[] fun v => do
                  let lctx ← getLCtx
                  let rule := {
                    ctor := ctor.name
                    nfields := bu.size
                    rhs := lctx.mkLambda stats.params <|
                      lctx.mkLambda motives <| lctx.mkLambda minors <|
                      lctx.mkLambda bu <|
                      mkAppN (mkAppN minors[minorIdx]! bu) v }
                  return (rule, minorIdx + 1)) start c).WF fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1 := by
        dsimp only
        apply mkRecInfos.loopCtorArgs.resultBindings stats ctor.type
          (Q := fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1)
          (k := fun _ bu u =>
            AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
              u 0 #[] fun v => do
                let lctx ← getLCtx
                let rule : RecursorRule := {
                  ctor := ctor.name
                  nfields := bu.size
                  rhs := lctx.mkLambda stats.params <|
                    lctx.mkLambda motives <| lctx.mkLambda minors <|
                    lctx.mkLambda bu <|
                    mkAppN (mkAppN minors[start]! bu) v }
                return (rule, start + 1))
          (c := c) (Hc := Hc)
        intro target bu u c' Hc' Hbu Hu hselected hroot
        let buildRule : Array Expr →
            AddInductive.M (RecursorRule × Nat) := fun v => do
          let lctx ← getLCtx
          let rule := {
            ctor := ctor.name
            nfields := bu.size
            rhs := lctx.mkLambda stats.params <|
              lctx.mkLambda motives <| lctx.mkLambda minors <|
              lctx.mkLambda bu <|
              mkAppN (mkAppN minors[start]! bu) v }
          return (rule, start + 1)
        change (AddInductive.mkRecRules.loopU indTypes stats motives minors
          lvls u 0 #[] buildRule c').WF _
        apply mkRecRules.loopU.boundGeneratedCallsFromEmpty
          (Q := fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1)
          (indTypes := indTypes) (stats := stats) (motives := motives)
          (minors := minors) (lvls := lvls) (u := u) (k := buildRule)
          (c := c') Hc'
        intro v Hcalls
        simp only [buildRule, getLCtx, readThe, read, ReaderT.read]
        refine Except.WF.pure ⟨?_, rfl⟩
        let Hparams' := Hparams.mono hroot
        let Hmotives' := Hmotives.mono hroot
        let Hminors' := Hminors.mono hroot
        have HouterNodup' :
            ((Hparams'.fvars ++ Hmotives'.fvars) ++
              Hminors'.fvars).Nodup := by
          change ((Hparams.fvars ++ Hmotives.fvars) ++
            Hminors.fvars).Nodup
          exact HouterNodup
        exact ⟨{
          root := c'
          root_wf := Hc'
          target := target
          allArgs := bu
          recursiveArgs := u
          recursiveResults := v
          minor_valid := by simp at hminorsRoom; omega
          params_bound := Hparams'
          motives_bound := Hmotives'
          minors_bound := Hminors'
          outer_binders_nodup := HouterNodup'
          all_args_bound := Hbu.toBoundFVarArray
          recursive_args_bound := Hu.toBoundFVarArray
          recursive_args_sublist := hselected
          all_args_nodup := Hbu.nodup
          recursive_args_nodup := Hu.nodup
          all_args_outer_fresh := by
            intro fv hfv houter
            apply Hbu.fresh fv hfv
            rcases List.mem_append.mp houter with hpm | hminor
            · rcases List.mem_append.mp hpm with hparam | hmotive
              · exact Hparams.members fv hparam
              · exact Hmotives.members fv hmotive
            · exact Hminors.members fv hminor
          recursive_calls := Hcalls
          ctor_eq := rfl
          fields_eq := rfl
          rhs_eq := rfl }⟩
      exact hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, hnext⟩
        have htail := ih (acc := acc.push out.1)
          (start := out.2) (c := c) Hc Hparams Hmotives Hminors
            HouterNodup (by simp at hminorsRoom; omega)
        exact htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, .cons Hrule ?_, ?_⟩
          · simpa [hout]
          · simpa [hnext] using Hgenerated
          · simp at hend ⊢
            omega

end mkRecRules.loopCtors

/-- Public binder-aware rule-generator boundary. -/
theorem mkRecRules.boundGeneratedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminorsRoom : start + indTypes[dIdx]!.ctors.length ≤ minors.size) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        BoundGeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.boundGeneratedRules indTypes stats
    motives minors (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start c Hc Hparams Hmotives Hminors
      HouterNodup hminorsRoom
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- Binder-aware analogue of `appendGeneratedRules`. Traversal, ordering, and
flattened constructor indexing are discharged here; the remaining pointwise
premise receives all local-binding evidence needed to construct `IotaRule`. -/
theorem IotaBuildCertificate.appendBoundGeneratedRules
    (Hbuild : IotaBuildCertificate env decl block prior)
    (Hgenerated : BoundGeneratedRecursorRules
      indTypes stats motives minors lvls ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (hsemantic : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length),
      BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) sourceRules[i] →
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i])) :
    IotaBuildCertificate env decl block (prior ++ abstractRules) := by
  apply Hbuild.append hroom
  intro i habstract
  have hsource : i < sourceRules.length := by omega
  have hctor : i < ctors.length := by
    rw [← Hgenerated.length]
    exact hsource
  rcases Hgenerated.entry i hctor hsource with ⟨Hrule⟩
  exact hsemantic i hctor hsource habstract Hrule

namespace mkRecInfos.loopU

/-- Every induction-hypothesis declaration introduced by `loopU` is retained
and appended to the certified hypothesis array. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha) {Q : alpha → Prop}
    (i : Nat) (v : Array Expr) (c : AddInductive.Context)
    (Hc : BindingContextWF c) (Hv : BoundFVarArray c v)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ v c, BindingContextWF c → BoundFVarArray c v →
      BindingContextLE root c → (k v c).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopU]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hviTy :
        ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
          let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
          let motiveApp := .app
            (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
          return (← getLCtx).mkForall xs motiveApp) c).WF
          (fun _ => True) := by
      intro _ _
      trivial
    refine hviTy.bind fun viTy _ => ?_
    have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
        (fun lctx => lctx = c.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName := (c.lctx.get! u[i].fvarId!).userName.appendAfter "_ih"
    apply withLocalDecl.continueRaw
    exact resultBindings stats u recInfos k (i + 1)
      (v.push (.fvar ⟨c.ngen.curr⟩)) _
      (Hc.withLocalDecl vName viTy.consumeTypeAnnotations .default)
      (Hv.pushCurrent vName viTy.consumeTypeAnnotations .default)
      (Hroot.trans <| BindingContextLE.withLocalDecl c vName
        viTy.consumeTypeAnnotations .default) Hk
  · rw [dif_neg hnext]
    exact Hk v c Hc Hv Hroot
termination_by u.size - i

end mkRecInfos.loopU

namespace mkRecInfos.loopCtors

/-- Processing constructors retains every field and induction-hypothesis
binder and appends the resulting minor binder to the certificate of its
owning inductive. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors : List Constructor)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (Harities : RecInfoArities stats recInfos)
    (Hk : ∀ out c, out.size = recInfos.size →
      out[dIdx]!.minors.size =
        recInfos[dIdx]!.minors.size + ctors.length →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      BindingContextWF c →
      (Hbindings : RecInfoBindings c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams → RecInfoArities stats out →
      BindingContextLE root c →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
      ctors k c).WF Q := by
  induction ctors generalizing recInfos c with
  | nil =>
      simpa [AddInductive.mkRecInfos.loopCtors] using
        Hk recInfos c rfl (by simp) (by intros; rfl)
          Hc Hbindings Hparams HnoAlias Harities Hroot
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecInfos.loopCtors]
      refine mkRecInfos.loopCtorArgs.resultBindings (Q := Q) stats ctor.type
        (fun t bu u =>
          let (itIdx, itIndices) := AddInductive.getIIndices stats t
          let introApp := mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params) bu
          let motiveApp := Expr.app
            (mkAppN recInfos[itIdx]!.motive itIndices) introApp
          AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] fun v => do
            let lctx ← getLCtx
            let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
            let minorName := ctor.name.replacePrefix indTypeName .anonymous
            withLocalDecl minorName .default minorTy.consumeTypeAnnotations fun minor =>
              let recInfos := recInfos.modify dIdx fun s =>
                { s with minors := s.minors.push minor }
              AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
                ctors k)
        c Hc ?_
      intro t bu u cArgs HcArgs Hbu Hu _hselected hArgs
      rcases hindices : AddInductive.getIIndices stats t with
        ⟨itIdx, itIndices⟩
      simp only
      let introApp := mkAppN
        (mkAppN (.const ctor.name stats.levels) stats.params) bu
      let motiveApp := Expr.app
        (mkAppN recInfos[itIdx]!.motive itIndices) introApp
      apply mkRecInfos.loopU.resultBindings (root := cArgs) (Q := Q)
        stats u recInfos
        (fun v => do
          let lctx ← getLCtx
          let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
          let minorName := ctor.name.replacePrefix indTypeName .anonymous
          withLocalDecl minorName .default minorTy.consumeTypeAnnotations fun minor =>
            let recInfos := recInfos.modify dIdx fun s =>
              { s with minors := s.minors.push minor }
            AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
              ctors k)
        0 #[] cArgs HcArgs (BoundFVarArray.empty cArgs)
          (BindingContextLE.refl cArgs)
      intro v cIH HcIH Hv hIH
      have hget : ((getLCtx : AddInductive.M LocalContext) cIH).WF
          (fun lctx => lctx = cIH.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      let minorTy := cIH.lctx.mkForall bu <| cIH.lctx.mkForall v motiveApp
      let minorName := ctor.name.replacePrefix indTypeName .anonymous
      apply withLocalDecl.continueRaw
      let next := recInfos.modify dIdx fun s =>
        { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) }
      let cMinor : AddInductive.Context := { cIH with
        ngen := cIH.ngen.next
        lctx := cIH.lctx.mkLocalDecl ⟨cIH.ngen.curr⟩ minorName
          minorTy.consumeTypeAnnotations .default }
      let HcMinor := HcIH.withLocalDecl minorName
        minorTy.consumeTypeAnnotations .default
      let HbindingsMinor := Hbindings.addMinor dIdx hidx (hArgs.trans hIH)
        minorName minorTy.consumeTypeAnnotations .default
      let HparamsMinor := Hparams.mono <| (hArgs.trans hIH).trans <|
          BindingContextLE.withLocalDecl cIH minorName
            minorTy.consumeTypeAnnotations .default
      let HnoAliasMinor := Hbindings.addMinor_noAlias Hparams HnoAlias
        dIdx hidx (hArgs.trans hIH) HcIH minorName
          minorTy.consumeTypeAnnotations .default
      let HrootMinor := (Hroot.trans hArgs).trans <| hIH.trans <|
          BindingContextLE.withLocalDecl cIH minorName
            minorTy.consumeTypeAnnotations .default
      refine ih next cMinor HcMinor HbindingsMinor HparamsMinor HnoAliasMinor
        HrootMinor ?_ ?_ ?_
      · simpa [next] using hidx
      · exact Harities.modifyMinors dIdx (fun minors =>
          minors.push (.fvar ⟨cIH.ngen.curr⟩))
      · intro out cOut houtSize houtCount houtOther HcOut HbindingsOut
          HparamsOut HnoAliasOut HaritiesOut HrootOut
        have houtSize' : out.size = recInfos.size := by
          simpa [next] using houtSize
        have houtCount' : out[dIdx]!.minors.size =
            recInfos[dIdx]!.minors.size + (ctor :: ctors).length := by
          rw [houtCount]
          dsimp [next]
          rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _
            hidx]
          simp
          omega
        have houtOther' : ∀ i, i < recInfos.size → dIdx ≠ i →
            out[i]!.minors.size = recInfos[i]!.minors.size := by
          intro i hi hine
          rw [houtOther i (by simpa [next] using hi) hine]
          rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
            hi hine]
        exact Hk out cOut houtSize' houtCount' houtOther' HcOut HbindingsOut
          HparamsOut HnoAliasOut HaritiesOut HrootOut

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

/-- The second mutual pass preserves all retained recursor binders while it
visits each owner and inserts that owner's constructor minors. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hsize : recInfos.size = indTypes.size)
    (Harities : RecInfoArities stats recInfos)
    (Hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (Hsuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      BindingContextWF c →
      (Hbindings : RecInfoBindings c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams → RecInfoArities stats out →
      BindingContextLE root c →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultBindings (Q := Q) stats
      indTypes[dIdx].name dIdx recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes
        (dIdx + 1) out k)
      c Hc Hbindings Hparams HnoAlias Hroot
      (by simpa [hsize] using hidx)
      Harities
    intro out cOut houtSize houtCount houtOther HcOut HbindingsOut
      HparamsOut HnoAliasOut HaritiesOut HrootOut
    apply resultBindings (root := root) (Q := Q) stats indTypes (dIdx + 1)
      out k cOut HcOut HbindingsOut HparamsOut HnoAliasOut HrootOut
    · exact houtSize.trans hsize
    · exact HaritiesOut
    · intro i hiDone hiOut
      by_cases hieq : i = dIdx
      · subst i
        rw [houtCount, Hsuffix dIdx (Nat.le_refl _) (by
          simpa [houtSize] using hiOut)]
        simp [Array.getElem!_eq_getD, Array.getD, hidx]
      · rw [houtOther i (by simpa [houtSize] using hiOut) (Ne.symm hieq)]
        exact Hprefix i (by omega) (by simpa [houtSize] using hiOut)
    · intro i hiNext hiOut
      have hine : dIdx ≠ i := by omega
      rw [houtOther i (by simpa [houtSize] using hiOut) hine]
      exact Hsuffix i (by omega) (by simpa [houtSize] using hiOut)
    · exact Hk
  · rw [dif_neg hidx]
    exact Hk recInfos c hsize (fun i hi => Hprefix i (by omega) hi)
      Hc Hbindings Hparams HnoAlias Harities Hroot
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

/-- End-to-end operational certificate for `mkRecInfos`: every successful
result has one retained frame per mutual inductive, and all binders created by
both passes remain selectable in the final local context. -/
theorem mkRecInfos.resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hparamsNodup : Hparams.fvars.Nodup)
    (Hk : ∀ out cOut, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      BindingContextWF cOut → (Hbindings : RecInfoBindings cOut out) →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoArities stats out →
      BindingContextLE c cOut → (k out cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  unfold AddInductive.mkRecInfos
  apply mkRecInfos.loopInd1.resultBindings (root := c) (Q := Q)
    stats indTypes elimLevel 0 #[]
    (fun recInfos => AddInductive.mkRecInfos.loopInd2 stats indTypes 0
      recInfos k)
    c Hc (RecInfoBindings.empty c) Hparams
      (RecInfoBindings.empty_noAlias c Hparams hparamsNodup)
      (BindingContextLE.refl c) rfl
      (RecInfoArities.empty stats) RecInfoMinorsEmpty.empty
  intro recInfos cFrames hsize HcFrames HbindingsFrames HparamsFrames
    HnoAliasFrames HaritiesFrames HemptyFrames HrootFrames
  apply mkRecInfos.loopInd2.resultBindings (root := c) (Q := Q)
    stats indTypes 0 recInfos k cFrames HcFrames HbindingsFrames HparamsFrames
      HnoAliasFrames HrootFrames
  · simpa using hsize
  · exact HaritiesFrames
  · intro i hi
    omega
  · intro i _ hi
    exact HemptyFrames i hi
  · intro out cOut houtSize houtCounts HcOut HbindingsOut HparamsOut
      HnoAliasOut HaritiesOut HrootOut
    exact Hk out cOut houtSize houtCounts HcOut HbindingsOut HparamsOut
      HnoAliasOut HaritiesOut HrootOut

/-- Unified projection used by recursor generation: a single successful run
supplies both the retained executable binders and the independent cardinality
certificate derived from the translated source declaration. -/
theorem mkRecInfos.resultCertificate {alpha : Type} {Q : alpha → Prop}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hparamsNodup : Hparams.fvars.Nodup)
    (Hk : ∀ out cOut, BindingContextWF cOut →
      (Hbindings : RecInfoBindings cOut out) →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecursorCardinalityCertificate stats out decl →
      BindingContextLE c cOut → (k out cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultBindings (Q := Q) stats indTypes elimLevel k c Hc
    Hparams hparamsNodup
  intro out cOut hsize hcounts HcOut Hbindings HparamsOut HnoAlias
    Harities Hroot
  apply Hk out cOut HcOut Hbindings HparamsOut HnoAlias
  · exact RecursorCardinalityCertificate.ofResult Hdecl Hmaterialized
      hsize hcounts Harities
  · exact Hroot

theorem LocalForallSelection.size
    (H : LocalForallSelection lctx xs) : xs.size = H.fvars.length := by
  rcases H with ⟨fvars, rfl, declarations⟩
  simp

theorem LocalForallSelection.forallTelescope
    (H : LocalForallSelection lctx xs) (body : Expr) :
    Expr.ForallTelescope (lctx.mkForall xs body) xs.size
      (body.abstractList H.fvars) := by
  rcases H with ⟨fvars, rfl, declarations⟩
  simpa using LocalContext.mkForall_fvars_forallTelescope declarations

/-- Prepending one retained binder group to an existing telescope preserves
the inner telescope and abstracts its residual below exactly the inner arity. -/
theorem LocalForallSelection.prependTelescope
    (Hsel : LocalForallSelection lctx xs)
    (Hinner : Expr.ForallTelescope inner innerArity result) :
    Expr.ForallTelescope (lctx.mkForall xs inner)
      (xs.size + innerArity)
      (result.abstractList Hsel.fvars innerArity) := by
  exact (Hsel.forallTelescope inner).trans <| by
    simpa using Hinner.abstractList Hsel.fvars

def RecursorLocalSelections.residual
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (body : Expr) : Expr :=
  let afterMajor := body.abstractList H.major.fvars
  let afterIndices := afterMajor.abstractList H.indices.fvars 1
  let afterMinors := afterIndices.abstractList H.minors.fvars
    (recInfos[ownerIdx]!.indices.size + 1)
  let afterMotives := afterMinors.abstractList H.motives.fvars
    ((recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
  afterMotives.abstractList H.params.fvars
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)

def concreteRecursorResult
    (numMotives numMinors numIndices ownerIdx : Nat) : Expr :=
  let motiveOffset :=
    1 + numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indexVars := (List.ofFn fun i : Fin numIndices =>
    Expr.bvar (1 + (numIndices - 1 - i))).toArray
  .app (mkAppN (.bvar motiveOffset) indexVars) (.bvar 0)

private theorem indexBVarOffsets_eq (n : Nat) :
    List.ofFn (fun i : Fin n => 1 + (n - 1 - i)) =
      (List.range n).reverse.map (fun i => i + 1) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hleft
    simp only [List.getElem_ofFn]
    rw [List.getElem_map, List.getElem_reverse]
    simp only [List.length_range]
    rw [List.getElem_range]
    omega

/-- Translation of the normalized executable result is forced to be the
same de Bruijn application used by the abstract recursor specification. -/
theorem TrExprS.concreteRecursorResult_eq
    (howner : ownerIdx < numMotives)
    (htotal : numParams + numMotives + numMinors + numIndices + 1 ≤
      domains.length)
    (H : TrExprS env Us (abstractForallContext domains Δ)
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx)
      result) :
    result = VExpr.mkApps
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (((List.range numIndices).reverse.map fun i => .bvar (i + 1)) ++
        [.bvar 0]) := by
  unfold concreteRecursorResult at H
  cases H with
  | app _ _ hfn hmajor =>
    have hmajorEq := TrExprS.bvar_eq_of_abstractForallContext hmajor
      (by omega)
    let indices := List.ofFn fun i : Fin numIndices =>
      1 + (numIndices - 1 - i)
    have hindexBound : ∀ i ∈ indices, i < domains.length := by
      intro i hi
      simp only [indices, List.mem_ofFn] at hi
      rcases hi with ⟨j, rfl⟩
      omega
    have hmotiveBound :
        1 + numIndices + numMinors + (numMotives - 1 - ownerIdx) <
          domains.length := by omega
    have hfn' := hfn
    unfold mkAppN at hfn'
    rw [← Array.foldl_toList] at hfn'
    change TrExprS env Us (abstractForallContext domains Δ)
      (List.foldl mkApp
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))
        (List.ofFn ((fun i => Expr.bvar i) ∘
          fun i : Fin numIndices => 1 + (numIndices - 1 - i)))) _ at hfn'
    rw [← List.map_ofFn, List.foldl_map] at hfn'
    change TrExprS env Us (abstractForallContext domains Δ)
      (indices.foldl (fun fn i => .app fn (.bvar i))
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))) _ at hfn'
    have hfnEq := TrExprS.foldl_bvars_eq domains Δ indices hindexBound
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (fun out Hout => TrExprS.bvar_eq_of_abstractForallContext Hout
        hmotiveBound)
      hfn'
    rw [hmajorEq, hfnEq]
    unfold VExpr.mkApps
    have hindices : indices =
        (List.range numIndices).reverse.map (fun i => i + 1) := by
      exact indexBVarOffsets_eq numIndices
    rw [hindices, ← List.foldl_map]
    simp [Function.comp_def]

/-- Distinct retained binders make the executable five-stage abstraction
compute to the canonical de Bruijn result used by the abstract recursor
specification. -/
theorem RecursorLocalSelections.residual_eq_concreteRecursorResult
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size) (hnoalias : H.NoAlias) :
    H.residual
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major) =
      concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx := by
  let motiveFVars := H.motives.fvars
  let minorFVars := H.minors.fvars
  let indexFVars := H.indices.fvars
  let majorFVars := H.major.fvars
  have hmotivesLen : motiveFVars.length = recInfos.size := by
    have h := H.motives.size
    simpa [motiveFVars] using h.symm
  have hownerMotive : ownerIdx < motiveFVars.length := by
    simpa [hmotivesLen] using howner
  have hindicesLen : indexFVars.length =
      recInfos[ownerIdx]!.indices.size := by
    simpa [indexFVars] using H.indices.size.symm
  have hmajorLen : majorFVars.length = 1 := by
    simpa [majorFVars] using H.major.size.symm
  have hmotive : recInfos[ownerIdx]!.motive =
      .fvar motiveFVars[ownerIdx] := by
    have hget := congrArg (fun xs => xs[ownerIdx]!) H.motives.expressions
    simpa [motiveFVars, Array.getElem!_eq_getD, Array.getD, howner,
      hownerMotive] using hget
  have hindices : recInfos[ownerIdx]!.indices =
      (indexFVars.map Expr.fvar).toArray := H.indices.expressions
  have hmajor : recInfos[ownerIdx]!.major = .fvar majorFVars[0] := by
    have hget := congrArg (fun xs => xs[0]!) H.major.expressions
    simpa [majorFVars, hmajorLen] using hget
  let body : Expr := .app (mkAppN (.fvar motiveFVars[ownerIdx])
    (indexFVars.map Expr.fvar).toArray) (.fvar majorFVars[0])
  have hbody :
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major) = body := by
    simp [body, hmotive, hindices, hmajor]
  rw [hbody]
  let parts := hnoalias.parts
  have hmotiveMajor : motiveFVars[ownerIdx] ∉ majorFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simpa [minorFVars, indexFVars, majorFVars, hmem]) rfl
  have hmotiveIndices : motiveFVars[ownerIdx] ∉ indexFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simpa [minorFVars, indexFVars, majorFVars, hmem]) rfl
  have hmotiveMinors : motiveFVars[ownerIdx] ∉ minorFVars := by
    intro hmem
    exact parts.motives_later motiveFVars[ownerIdx]
      (List.getElem_mem hownerMotive) motiveFVars[ownerIdx]
      (by simpa [minorFVars, indexFVars, majorFVars, hmem]) rfl
  have hindicesMajor : ∀ fv ∈ indexFVars, fv ∉ majorFVars := by
    intro fv hfv hmem
    exact parts.indices_major fv hfv fv hmem rfl
  let afterMajor := body.abstractList majorFVars
  have hmajorBound : 0 < majorFVars.length := by omega
  have hmajorOffset : majorFVars.length - 1 = 0 := by omega
  have hAfterMajor : afterMajor =
      .app (mkAppN (.fvar motiveFVars[ownerIdx])
        (indexFVars.map Expr.fvar).toArray) (.bvar 0) := by
    unfold afterMajor body
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_of_not_mem hmotiveMajor,
      Expr.abstractList_fvarArray_of_disjoint indexFVars majorFVars 0
        hindicesMajor,
      Expr.abstractList_fvar_getElem parts.major 0 hmajorBound]
    simp [majorFVars, hmajorOffset]
  let indexBVars := (List.ofFn fun i : Fin indexFVars.length =>
    Expr.bvar (1 + (indexFVars.length - 1 - i))).toArray
  let afterIndices := afterMajor.abstractList indexFVars 1
  have hAfterIndices : afterIndices =
      .app (mkAppN (.fvar motiveFVars[ownerIdx]) indexBVars) (.bvar 0) := by
    unfold afterIndices
    rw [hAfterMajor]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_of_not_mem hmotiveIndices,
      Expr.abstractList_fvarArray indexFVars 1 parts.indices]
    rw [Expr.abstractList_bvar_lt indexFVars (by omega : 0 < 1)]
  let afterMinors := afterIndices.abstractList minorFVars
    (indexFVars.length + 1)
  have hAfterMinors : afterMinors =
      .app (mkAppN (.fvar motiveFVars[ownerIdx]) indexBVars) (.bvar 0) := by
    unfold afterMinors
    rw [hAfterIndices]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_of_not_mem hmotiveMinors,
      Expr.abstractList_indexBVars minorFVars indexFVars.length
        (indexFVars.length + 1) (by omega),
      Expr.abstractList_bvar_lt minorFVars (by omega : 0 < indexFVars.length + 1)]
  let motiveBase := minorFVars.length + indexFVars.length + 1
  let afterMotives := afterMinors.abstractList motiveFVars motiveBase
  have hAfterMotives : afterMotives =
      .app (mkAppN
        (.bvar (motiveBase + (motiveFVars.length - 1 - ownerIdx)))
        indexBVars) (.bvar 0) := by
    unfold afterMotives
    rw [hAfterMinors]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_fvar_getElem parts.motives ownerIdx hownerMotive,
      Expr.abstractList_indexBVars motiveFVars indexFVars.length motiveBase
        (by simp [motiveBase]; omega)]
    rw [Expr.abstractList_bvar_lt motiveFVars (by simp [motiveBase])]
  let allBase := motiveFVars.length + motiveBase
  have hAfterParams : afterMotives.abstractList H.params.fvars allBase =
      .app (mkAppN
        (.bvar (motiveBase + (motiveFVars.length - 1 - ownerIdx)))
        indexBVars) (.bvar 0) := by
    rw [hAfterMotives]
    unfold indexBVars
    rw [Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.abstractList_bvar_lt H.params.fvars (by
        simp [allBase, motiveBase]
        omega),
      Expr.abstractList_indexBVars H.params.fvars indexFVars.length allBase
        (by simp [allBase, motiveBase]; omega),
      Expr.abstractList_bvar_lt H.params.fvars (by
        simp [allBase, motiveBase]
        omega)]
  dsimp only [RecursorLocalSelections.residual]
  change ((afterIndices.abstractList minorFVars
      (recInfos[ownerIdx]!.indices.size + 1)).abstractList motiveFVars
        ((recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)).abstractList H.params.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1) = _
  rw [← hindicesLen, H.minors.size, H.motives.size]
  simpa [afterMotives, afterMinors, afterIndices, afterMajor,
    concreteRecursorResult, indexBVars, motiveBase, allBase,
    motiveFVars, minorFVars, indexFVars,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAfterParams

/-- Exact concrete telescope produced by the five nested `mkForall` calls in
`AddInductive.run`. -/
theorem RecursorLocalSelections.forallTelescope
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (body : Expr) :
    Expr.ForallTelescope
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major] body)
      (stats.params.size + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1)
      (H.residual body) := by
  have hMajor := H.major.prependTelescope (.nil body)
  have hIndices := H.indices.prependTelescope hMajor
  have hMinors := H.minors.prependTelescope hIndices
  have hMotives := H.motives.prependTelescope hMinors
  have hParams := H.params.prependTelescope hMotives
  simpa [RecursorLocalSelections.residual, Nat.add_assoc] using hParams

/-- The retained executable binder selections, their global no-alias
invariant, and the independent cardinality certificate determine the exact
abstract shape of one generated recursor. -/
theorem RecursorLocalSelections.recursorShape
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : H.NoAlias)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (hdeclOwner : ownerIdx < decl.types.length)
    (recursor : VConstVal)
    (hname : recursor.name =
      decl.recursorName (decl.types[ownerIdx]'(hdeclOwner)))
    (huvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (Htr : TrExprS env Us Δ
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major))
      recursor.type) :
    Nonempty (decl.RecursorShape
      (decl.types[ownerIdx]'(hdeclOwner)) recursor) := by
  have Htel := H.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  have hresidual := H.residual_eq_concreteRecursorResult howner hnoalias
  rw [hresidual] at Htel
  rcases TrExprS.forallTelescope_shape_with_context Htel Htr with
    ⟨domains, result, hdomainsLength, htype, Hresult⟩
  have htotal : stats.params.size + (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 ≤ domains.length := by
    omega
  have hownerMotive : ownerIdx < (recInfos.map (·.motive)).size := by
    simpa using howner
  have hresultConcrete := TrExprS.concreteRecursorResult_eq
    (numParams := stats.params.size) hownerMotive htotal Hresult
  have hdomainsSpec : domains.length =
      decl.nparams + decl.types.length + decl.ownedConstructors.length +
        (decl.types[ownerIdx]'(hdeclOwner)).numIndices + 1 := by
    rw [hdomainsLength, Hcard.params, Hcard.motives, Hcard.minors,
      Hcard.indices ownerIdx howner]
  rcases List.exists_append_five_of_length_eq domains decl.nparams
      decl.types.length decl.ownedConstructors.length
      (decl.types[ownerIdx]'(hdeclOwner)).numIndices 1 hdomainsSpec with
    ⟨params, motives, minors, indices, major, hdomains,
      hparams, hmotives, hminors, hindices, hmajor⟩
  have hresult : result =
      decl.recursorResult ownerIdx minors.length
        (decl.types[ownerIdx]'(hdeclOwner)) := by
    simpa [VInductDecl.recursorResult, Hcard.records, Hcard.motives,
      Hcard.minors, Hcard.indices ownerIdx howner, hminors] using
        hresultConcrete
  refine ⟨VInductDecl.RecursorShape.ofWrapped hdeclOwner rfl hname huvars
    hparams hmotives hminors hindices hmajor ?_ hresult⟩
  simpa [hdomains] using htype

/-- Metadata and translation of the actual production `.recInfo` constant
discharge the remaining premises of `recursorShape`. This is the boundary
used by the outer installation loop after `inferImplicit`. -/
theorem RecursorLocalSelections.recursorShape_of_recInfo
    {indTypes : Array InductiveType}
    {envTypes envCtors : VEnv}
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : H.NoAlias)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hsourceOwner : ownerIdx < indTypes.size)
    (elimLevel : Level) (info : RecursorVal) (recursor : VConstVal)
    (Hinfo : TrConstVal safety env (.recInfo info) recursor)
    (hlevels : info.levelParams =
      AddInductive.getRecLevelParams elimLevel lparams)
    (hname : info.name =
      Lean.mkRecName (indTypes[ownerIdx]'(hsourceOwner)).name)
    (htype : info.type =
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
        1000 false) :
    Nonempty (decl.RecursorShape
      (decl.types[ownerIdx]'(by simpa [Hcard.records] using howner))
      recursor) := by
  have hdeclOwner : ownerIdx < decl.types.length := by
    simpa [Hcard.records] using howner
  have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hdecl
    ownerIdx (by simpa using hsourceOwner) hdeclOwner
  have hinfoName : info.name = recursor.name := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hinfo.2
  have hownerName : (decl.types[ownerIdx]'(hdeclOwner)).name =
      (indTypes[ownerIdx]'(hsourceOwner)).name := by
    simpa using Howner.header.name
  have hrecName : recursor.name =
      decl.recursorName (decl.types[ownerIdx]'(hdeclOwner)) := by
    rw [← hinfoName, hname, VInductDecl.recursorName_eq_mkRecName,
      hownerName]
  have hrecUvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1 := by
    have htranslated : info.levelParams.length = recursor.uvars := by
      simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
        Hinfo.1.2.1
    have hdeclUvars : decl.uvars = lparams.length := Hdecl.uvars
    rw [hlevels] at htranslated
    rcases AddInductive.getRecLevelParams_length
        (elimLevel := elimLevel) (lparams := lparams) with hsame | hextra
    · left
      omega
    · right
      omega
  have htranslated : TrExprS env info.levelParams [] info.type
      recursor.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using Hinfo.1.2.2
  rw [htype] at htranslated
  have hpre := TrExprS.of_inferImplicit htranslated
  exact H.recursorShape howner hnoalias Hcard hdeclOwner recursor
    hrecName hrecUvars hpre

/-- The same installed `.recInfo` translation independently proves semantic
well-formedness of the generated recursor constant. -/
theorem RecursorLocalSelections.recursorWF_of_recInfo
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (info : RecursorVal) (recursor : VConstVal)
    (Hinfo : TrConstVal safety env (.recInfo info) recursor)
    (htype : info.type =
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive
           recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
        1000 false) :
    recursor.toVConstant.WF env := by
  have htranslated : TrExprS env info.levelParams [] info.type
      recursor.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using Hinfo.1.2.2
  rw [htype] at htranslated
  have hpre := TrExprS.of_inferImplicit htranslated
  have Htel := H.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  have hpositive : 0 < stats.params.size +
      (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 := by omega
  have hwf := TrExprS.isType_of_forallTelescope Htel hpositive hpre
  have huvars : info.levelParams.length = recursor.uvars := by
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hinfo.1.2.1
  rw [huvars] at hwf
  exact hwf

/-- Pointwise record emitted by one iteration of the production recursor
loop. It retains only the metadata needed to connect that iteration to the
independent shape and semantic-typing judgments. -/
structure GeneratedRecursorEntry
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (ownerIdx : Nat) (entry : ConstantInfo × VConstVal) where
  info : RecursorVal
  source_eq : entry.1 = .recInfo info
  translated : TrConstVal safety env (.recInfo info) entry.2
  levels : info.levelParams =
    AddInductive.getRecLevelParams elimLevel lparams
  name : info.name = Lean.mkRecName indTypes[ownerIdx]!.name
  type : info.type =
    (c.lctx.mkForall stats.params <|
     c.lctx.mkForall (recInfos.map (·.motive)) <|
     c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
     c.lctx.mkForall recInfos[ownerIdx]!.indices <|
     c.lctx.mkForall #[recInfos[ownerIdx]!.major]
       (.app (mkAppN recInfos[ownerIdx]!.motive
         recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
      1000 false

/-- Reviewable output invariant for the complete production recursor loop. -/
structure GeneratedRecursors
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) where
  length : entries.length = recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos i entries[i]

/-- Append-oriented form matching the `for dIdx in [:indTypes.size]` loop. -/
structure GeneratedRecursorsPrefix
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) where
  covered : entries.length ≤ recInfos.size
  entry : ∀ i (hi : i < entries.length),
    GeneratedRecursorEntry safety env lparams elimLevel c stats indTypes
      recInfos i entries[i]

def GeneratedRecursorsPrefix.empty
    (safety : DefinitionSafety) (env : VEnv) (lparams : List Name)
    (elimLevel : Level) (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (recInfos : Array AddInductive.RecInfo) :
    GeneratedRecursorsPrefix safety env lparams elimLevel c stats indTypes
      recInfos [] where
  covered := Nat.zero_le _
  entry _ hi := by simp at hi

def GeneratedRecursorsPrefix.push
    (H : GeneratedRecursorsPrefix safety env lparams elimLevel c stats
      indTypes recInfos entries)
    (hnext : entries.length < recInfos.size)
    (E : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos entries.length newEntry) :
    GeneratedRecursorsPrefix safety env lparams elimLevel c stats indTypes
      recInfos (entries ++ [newEntry]) where
  covered := by simp; omega
  entry i hi := by
    by_cases hold : i < entries.length
    · simpa [List.getElem_append, hold] using H.entry i hold
    · have hieq : i = entries.length := by simp at hi; omega
      subst i
      simpa using E

def GeneratedRecursorsPrefix.complete
    (H : GeneratedRecursorsPrefix safety env lparams elimLevel c stats
      indTypes recInfos entries)
    (hcomplete : entries.length = recInfos.size) :
    GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries where
  length := hcomplete
  entry := H.entry

/-- A validated mutual-family owner index names an actually generated
recursor. This is the global half of the pointwise `RecursorsPresent`
obligation retained by generated recursive calls. -/
theorem GeneratedRecursors.recursorName_mem
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (hrecords : recInfos.size = indTypes.size)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    Lean.mkRecName indTypes[ownerIdx]!.name ∈
      (entries.map Prod.snd).map (·.name) := by
  have hentry : ownerIdx < entries.length := by
    rw [H.length, hrecords]
    exact howner
  let E := H.entry ownerIdx hentry
  have htranslatedName : E.info.name = entries[ownerIdx].2.name := by
    exact E.translated.2
  have hname : entries[ownerIdx].2.name =
      Lean.mkRecName indTypes[ownerIdx]!.name := by
    rw [← htranslatedName, E.name]
  rw [← hname]
  exact List.mem_map.mpr ⟨entries[ownerIdx].2,
    List.mem_map.mpr ⟨entries[ownerIdx], List.getElem_mem hentry, rfl⟩,
    rfl⟩

theorem GeneratedRecursors.recursorName_mem_block
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (block : VInductBlock)
    (hrecords : recInfos.size = indTypes.size)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    Lean.mkRecName indTypes[ownerIdx]!.name ∈
      block.recursors.map (·.name) := by
  rw [hrecursors]
  exact H.recursorName_mem hrecords ownerIdx howner

/-- The retained owner of a typed recursive field selects a generated
recursor in the installed block. -/
theorem GeneratedRecursors.recursiveDomainRecursor_mem_block
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (block : VInductBlock)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (cert : RecursorRecursiveDomain domainEnv decl) :
    Lean.mkRecName indTypes[cert.ownerIdx]!.name ∈
      block.recursors.map (·.name) := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
  have hrecords : recInfos.size = indTypes.size := by
    rw [Hcard.records, htypes]
  have howner : cert.ownerIdx < indTypes.size := by
    rw [htypes]
    exact cert.owner_lt
  exact H.recursorName_mem_block block hrecords hrecursors cert.ownerIdx howner

/-- Owner alignment discharges the exact generated-call recursor coverage
used by guarded iota RHS construction. -/
theorem GeneratedRecursors.recursorsPresent_ofOwnerAlignment
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (block : VInductBlock)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hcalls : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Howners : Hcalls.OwnerAlignment decl certs) :
    Hcalls.RecursorsPresent (block.recursors.map (·.name)) := by
  intro i hi Hentry
  have hiCert : i < certs.length := by rw [Howners.length]; exact hi
  let cert := certs[i]
  have hmem := H.recursiveDomainRecursor_mem_block block Hcard Hdecl
    hrecursors cert
  rw [Howners.recursorName i hi Hentry]
  simpa [cert] using hmem

/-- Global recursor generation discharges the final coverage premise of the
pointwise generated-rule theorem. Every recursive call is routed through its
classifier-retained mutual owner and hence names an installed primary
recursor. -/
theorem GeneratedRecursors.iotaRule_ofTranslationCertificate
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hequation : Hrule.IotaEquationTranslationCertificate trEnv Us Δ decl
      block owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl Hrule.allArgs
      Hrule.recursiveArgs selections)
    (Howners : Hrule.recursive_calls.OwnerAlignment decl selections)
    {recursiveArgs : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS trEnv Us
        (abstractForallContext Hequation.shape.domains Δ))
      (Hrule.recursiveArgs.map fun arg =>
        arg.abstractList Hrule.binders).toList recursiveArgs)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hequation.shape.domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) := by
  have hpresent := Hgenerated.recursorsPresent_ofOwnerAlignment block Hcard
    Hdecl hrecursors Hrule.recursive_calls Howners
  exact Hrule.iotaRule_ofTranslationCertificate Hequation Hselection Hargs
    hfresh hctx hproj hpresent

theorem GeneratedRecursors.iotaRule_ofTranslation
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Htr : Hrule.IotaRuleTranslation trEnv Us Δ semanticEnv decl block owner
      ctor rule)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) :=
  Hgenerated.iotaRule_ofTranslationCertificate Hrule Hcard Hdecl block
    hrecursors Htr.equation Htr.selection Htr.owner_alignment Htr.args
    hfresh Htr.context_free hproj

/-- Append one generated family batch to the flattened iota accumulator.
The pointwise premise now asks only for the explicit executable-to-`VDefEq`
translation payload; `IotaRule` itself is derived uniformly using the global
generated-recursor certificate. -/
theorem GeneratedRecursors.appendIotaBatch
    (Hgenerated : GeneratedRecursors safety generatedEnv lparams elimLevel c
      stats indTypes recInfos entries)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hbuild : IotaBuildCertificate semanticEnv decl block prior)
    (Hbatch : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (Htranslations : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length)
      (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) sourceRules[i]),
      Nonempty (Hrule.IotaRuleTranslation trEnv Us Δ semanticEnv decl block
        decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i]))
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false) :
    IotaBuildCertificate semanticEnv decl block (prior ++ abstractRules) := by
  apply Hbuild.appendBoundGeneratedRules Hbatch hlength hroom
  intro i hctor hsource habstract Hrule
  rcases Htranslations i hctor hsource habstract Hrule with ⟨Htr⟩
  exact Hgenerated.iotaRule_ofTranslation Hrule Hcard Hdecl block hrecursors
    Htr hfresh hproj

theorem GeneratedRecursors.recursorCertificate
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors) :
    RecursorCertificate decl (entries.map Prod.snd) := by
  have hindTypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
  refine {
    length := by simp [H.length, Hcard.records]
    shapes := ?_ }
  intro i htype hrec
  have hentry : i < entries.length := by simpa using hrec
  have howner : i < recInfos.size := by simpa [H.length] using hentry
  have hsource : i < indTypes.size := by omega
  let Hlocal := Hbindings.toRecursorLocalSelections Hc Hparams i howner
  have hlocalNoAlias : Hlocal.NoAlias :=
    Hbindings.selectionNoAlias Hc Hparams hnoalias i howner
  let E := H.entry i hentry
  have hshape := Hlocal.recursorShape_of_recInfo howner hlocalNoAlias Hcard
    Hdecl hsource elimLevel E.info entries[i].2 E.translated E.levels
    (by simpa [Array.getElem!_eq_getD, Array.getD, hsource] using E.name)
    E.type
  simpa [E, Hlocal] using hshape

theorem GeneratedRecursors.recursorsWF
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) :
    ∀ recursor ∈ entries.map Prod.snd, recursor.toVConstant.WF env := by
  intro recursor hrec
  rcases List.mem_iff_getElem.mp hrec with ⟨i, hi, heq⟩
  have hentry : i < entries.length := by simpa using hi
  have heqTarget : entries[i].2 = recursor := by simpa using heq
  subst recursor
  have howner : i < recInfos.size := by simpa [H.length] using hentry
  let Hlocal := Hbindings.toRecursorLocalSelections Hc Hparams i howner
  let E := H.entry i hentry
  have hwf := Hlocal.recursorWF_of_recInfo howner E.info entries[i].2
    E.translated E.type
  simpa using hwf

/-- Once the rule traversal and global name check are supplied, the generated
recursor-loop certificate fills the recursor component of the independent
ordinary-compilation interface. -/
theorem GeneratedRecursors.ordinaryCompilationCertificate
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (hrules : IotaCertificate sourceEnv decl block)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    OrdinaryCompilationCertificate sourceEnv decl block := by
  refine {
    types := htypes
    ctors := hctors
    recursors := ?_
    rules := hrules
    names := hnames }
  rw [hrecursors]
  exact H.recursorCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl

/-- Rule-batch endpoint for ordinary compilation. Generated family batches
accumulate `IotaRule` evidence with `IotaBuildCertificate`; exact flattened
coverage turns that executable traversal invariant into the final rule
certificate consumed by `OrdinaryCompilationCertificate`. -/
theorem GeneratedRecursors.ordinaryCompilationCertificate_ofRuleBuild
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors = entries.map Prod.snd)
    (Hrules : IotaBuildCertificate sourceEnv decl block block.rules)
    (hrulesLength : block.rules.length = decl.ownedConstructors.length)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    OrdinaryCompilationCertificate sourceEnv decl block :=
  H.ordinaryCompilationCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl
    block htypes hctors hrecursors (Hrules.completeBlock hrulesLength) hnames

/-- Nested restoration reuses the verified primary recursor traversal and
adds only the separately audited auxiliary-name/guardedness suffix. -/
def GeneratedRecursors.nestedCompilationCertificate
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv lparams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (block : VInductBlock) (main : VInductiveType)
    (rest : List VInductiveType)
    (htypesSource : decl.types = main :: rest)
    (auxRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (Haux : AuxiliaryRestorationPrefix decl block main
      auxRecursors auxiliaryRules)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants)
    (hrecursors : block.recursors =
      entries.map Prod.snd ++ auxRecursors)
    (hrules : block.rules = primaryRules ++ auxiliaryRules)
    (hprimaryRules : IotaListCertificate sourceEnv decl block primaryRules)
    (hnames : List.Nodup
      ((block.types ++ block.ctors ++ block.recursors).map (·.name))) :
    NestedCompilationCertificate sourceEnv decl block where
  main := main
  rest := rest
  types_source := htypesSource
  types := htypes
  ctors := hctors
  primaryRecursors := entries.map Prod.snd
  auxiliaryRecursors := auxRecursors
  recursors_eq := hrecursors
  primary_recursors :=
    H.recursorCertificate Hc Hbindings Hparams hnoalias Hcard Hdecl
  auxiliary_names := Haux.names
  primaryRules := primaryRules
  auxiliaryRules := auxiliaryRules
  rules_eq := hrules
  primary_rules := hprimaryRules
  auxiliary_guarded := Haux.guarded
  names := hnames

/-- Abstract domains introduced by `MLCtx.mkForall'`, in outermost-to-
innermost order. Local lets are discharged by `mkForall'` and contribute no
domain. -/
def MLCtxForallDomains (c : TypeChecker.MLCtx) :
    (n : Nat) → n ≤ c.length → List VExpr
  | 0, _ => []
  | n + 1, h =>
    match c with
    | .vlam _ _ _ type' _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h) ++ [type']
    | .vlet _ _ _ _ _ _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h)

theorem TypeChecker.MLCtx.mkForall'_eq_wrapForalls
    (c : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ c.length) (body : VExpr) :
    c.mkForall' n hn body = VExpr.wrapForalls (MLCtxForallDomains c n hn) body := by
  induction n generalizing c body with
  | zero => simp [TypeChecker.MLCtx.mkForall', MLCtxForallDomains,
      VExpr.wrapForalls]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      rw [ih, VExpr.wrapForalls_append]
      rfl
    | vlet fv name type value type' value' c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      exact ih c (Nat.le_of_succ_le_succ hn) body

/-- Exact certificate for a suffix of local declarations introduced by
`withLocalDecl`; its domains are recorded in the same outermost-to-innermost
order used by generated recursor telescopes. -/
inductive MLCtxLamPrefix : TypeChecker.MLCtx → Nat → List VExpr → Prop
  | nil (c : TypeChecker.MLCtx) : MLCtxLamPrefix c 0 []
  | cons : MLCtxLamPrefix c n domains →
      MLCtxLamPrefix (.vlam fv name type type' bi c) (n + 1)
        (domains ++ [type'])

theorem MLCtxLamPrefix.le
    (H : MLCtxLamPrefix c n domains) : n ≤ c.length := by
  induction H with
  | nil => simp
  | cons _ ih => simpa using Nat.succ_le_succ ih

theorem MLCtxLamPrefix.forallDomains
    (H : MLCtxLamPrefix c n domains) :
    MLCtxForallDomains c n H.le = domains := by
  induction H with
  | nil => simp [MLCtxForallDomains]
  | cons H ih =>
    simp only [MLCtxForallDomains]
    change MLCtxForallDomains _ _ H.le ++ [_] = _
    rw [ih]

theorem MLCtxLamPrefix.mkForall'
    (H : MLCtxLamPrefix c n domains) (body : VExpr) :
    c.mkForall' n H.le body = VExpr.wrapForalls domains body := by
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, H.forallDomains]

/-- Production-side installation of a list of kernel constants. This small
reference function is used only to state the staging invariant; the executable
inductive checker continues to build the same environments directly. -/
def addConstants : Environment → List ConstantInfo → Environment
  | env, [] => env
  | env, ci :: cis => addConstants (env.add ci) cis

/-- A certificate that a list of production constants and abstract constants
are installed in lockstep. Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

/-- A successful executable installation fold yields the lockstep production
/ abstract staging certificate. Translation and typing may be proved in an
earlier environment and are transported through the already installed
prefix. -/
theorem AddConstants.ofDeclareInductiveTypeInfos
    (Hvalid : CheckingEnv.Valid safety env venv)
    (Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal safety sourceEnv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF sourceEnv)
      infos values)
    (hle : sourceEnv ≤ venv)
    (hadd : venv.addConsts values = some outVEnv)
    (hnprim : ∀ info ∈ infos,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypeInfos allowPrimitive infos env).WF
      fun outEnv =>
        AddConstants safety env venv
          (List.zip (infos.map (fun info => .inductInfo info)) values)
          outEnv outVEnv := by
  induction Hentries generalizing env venv with
  | nil =>
    simp [AddInductive.declareInductiveTypeInfos, VEnv.addConsts] at hadd ⊢
    subst outVEnv
    exact Except.WF.pure .nil
  | @cons info ci' infos values Hentry _ ih =>
    have hname : info.name = ci'.name := Hentry.1.2
    cases hnext : venv.addConst ci'.name ci'.toVConstant with
    | none => simp [VEnv.addConsts, hnext] at hadd
    | some nextVEnv =>
      have hrest : nextVEnv.addConsts values = some outVEnv := by
        simpa [VEnv.addConsts, hnext] using hadd
      have hnprimHead := hnprim info (by simp)
      have hnprimTail : ∀ info ∈ infos,
          ¬ Kernel.Environment.primitives.contains info.name := by
        intro info hinfo
        exact hnprim info (by simp [hinfo])
      rw [AddInductive.declareInductiveTypeInfos]
      exact (checkName.WF Hvalid.tr.map_wf info.name allowPrimitive).bind
        fun _ hchecked => by
          have hn : env.find? info.name = none := hchecked.1
          have htr : TrConstVal safety venv (.inductInfo info) ci' :=
            Hentry.1.mono hle
          have hwf : ci'.toVConstant.WF venv := Hentry.2.mono hle
          have haddHead :
              venv.addConst info.name ci'.toVConstant = some nextVEnv := by
            simpa [hname] using hnext
          have HnextValid : CheckingEnv.Valid safety
              (env.add (.inductInfo info)) nextVEnv :=
            Hvalid.add hn hnprimHead htr.1 hwf haddHead rfl
          have hnextLe : sourceEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddHead)
          exact (ih HnextValid hnextLe hrest hnprimTail).mono fun outEnv Hrest => by
            simpa using AddConstants.cons (ci := .inductInfo info)
              (ci' := ci') hn hnprimHead htr hwf haddHead rfl Hrest

theorem AddConstants.valid
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.production
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    addConstants env (entries.map Prod.fst) = outEnv := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simpa [addConstants] using ih

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConsts (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConsts]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConsts, ← htr.2, hadd]
    exact ih

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConsts_le H.abstract

/-- Verified boundary after installing all mutual type constants and before
checking any constructor. The executable and abstract environments are
aligned, while the original source-to-constructor translation already points
at this exact abstract header environment. -/
structure DeclaredTypesResult (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  entries : List (ConstantInfo × VConstVal)
  context : ContextWF { c with env := outEnv }
  headers : HeaderCertificate sourceEnv decl
  typesInstalled : sourceEnv.addConsts decl.typeConstants = some context.venv
  sourceTypes : List.Forall₂
    (TrInductiveType sourceEnv context.venv c.lparams)
    indTypes.toList decl.types
  installed : AddConstants c.safety c.env sourceEnv entries outEnv context.venv
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    context.venv c.lparams context.mlctx.vlctx stats decl depth
  headerParams : materialized.headers.params = headers.params

/-- End-to-end refinement of `declareInductiveTypes`: a successful executable
fold installs precisely the independently specified mutual headers and
transports the materialized header certificate into that environment. -/
theorem AddInductive.declareInductiveTypes.WF
    {envTypes envCtors : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclCore Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ _ : DeclaredTypesResult c stats decl depth Hc.venv
          indTypes outEnv, True := by
  rcases Hdecl with
    ⟨huvars, hnparams, hunsafe, htypesAdded, hctorsAdded, Htypes⟩
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Htranslated := AddInductive.inductiveTypeInfos.translated
    (numParams := numParams) (numNested := numNested)
    Htypes Hmaterialized.indices hvisible
  have Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal c.safety Hc.venv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF Hc.venv)
      infos.toList decl.typeConstants := by
    simpa [infos, VInductDecl.typeConstants] using Htranslated
  have Hinstall := AddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive)
    Hc.checking Hentries VEnv.LE.rfl htypesAdded (by
      simpa [infos] using hnprim)
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    refine ⟨{
      entries := List.zip
        (infos.toList.map (fun info => .inductInfo info)) decl.typeConstants
      context := Hc.withEnv (Hinstalled.valid Hc.checking) Hinstalled.le
      headers := Hmaterialized.headers
      typesInstalled := htypesAdded
      sourceTypes := Htypes
      installed := Hinstalled
      materialized := Hmaterialized.mono Hinstalled.le
      headerParams := rfl }, trivial⟩

def DeclaredTypesResult.formation
    (H : DeclaredTypesResult c stats decl depth sourceEnv indTypes outEnv)
    (Hconstructors : ConstructorCertificate sourceEnv decl H.context.venv
      H.headers.params) :
    FormationCertificate sourceEnv decl where
  headers := H.headers
  envTypes := H.context.venv
  typesInstalled := H.typesInstalled
  constructors := Hconstructors

theorem AddInductive.checkConstructors.WF
    (H : DeclaredTypesResult c stats decl depth sourceEnv indTypes outEnv)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        ConstructorCertificate sourceEnv decl H.context.venv H.headers.params := by
  have Hloops := checkConstructors.loopTypes.refinesMaterialized
    H.context H.sourceTypes H.materialized H.headerParams Hfresh hconsume
    hlit hproj hunsafe hbound
  rw [AddInductive.checkConstructors]
  change (((liftM TypeChecker.getEnv : AddInductive.M _) >>= fun _ =>
    AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0)
      { c with env := outEnv }).WF _
  change (((liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } >>= fun _ =>
      AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
        { c with env := outEnv }).WF _)
  rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } = .ok outEnv from rfl]
  exact Hloops

/-- The exact executable prefix used by `AddInductive.run`, through mutual
header installation and constructor checking, refines `FormationWF`. -/
theorem AddInductive.formationPrefix.WF
    {envTypes envCtors : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclCore Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun outEnv =>
        AddInductive.withEnv outEnv
          (AddInductive.checkConstructors indTypes stats isUnsafe)) c).WF
      fun _ => Nonempty (FormationCertificate Hc.venv decl) := by
  have Htypes := AddInductive.declareInductiveTypes.WF Hc Hdecl Hmaterialized
    hvisible hnprim
  exact Htypes.bind fun outEnv hresult => by
    rcases hresult with ⟨Hstaged, _⟩
    have Hconstructors := AddInductive.checkConstructors.WF Hstaged Hfresh
      hconsume hlit hproj hunsafe hbound
    exact Hconstructors.mono fun _ Hctors => ⟨Hstaged.formation Hctors⟩

/-- Three-stage installation certificate matching the executable order:
mutual headers, constructors, then recursors. Reduction equations are not
included here because their validity depends on the independent iota schema. -/
structure StagedBlock (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  typesAdded : AddConstants safety env venv types envTypes venvTypes
  ctorsAdded : AddConstants safety envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors venvCtors recursors outEnv outVEnv

theorem StagedBlock.valid
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid (H.ctorsAdded.valid (H.typesAdded.valid hvalid))

theorem StagedBlock.abstract_types
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    venv.addConsts (types.map Prod.snd) = some H.venvTypes :=
  H.typesAdded.abstract

theorem StagedBlock.abstract_ctors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvTypes.addConsts (ctors.map Prod.snd) = some H.venvCtors :=
  H.ctorsAdded.abstract

theorem StagedBlock.abstract_recursors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvCtors.addConsts (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

/-- The complete semantic certificate for the block assembled by the three
executable installation stages. `AddConstants` records the per-step checking
environment; the three `*WF` fields deliberately record the stronger
stage-wide facts required by the independent `VInductBlock.WF` specification.
This distinction matters for mutual declarations: typing a later header only
after installing an earlier sibling would not establish formation of the
mutual block. -/
structure BlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  staged : StagedBlock safety env venv types ctors recursors outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF staged.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF staged.venvCtors
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

/-- Generated recursor traversal discharges the recursor-typing field of the
semantic block certificate in the exact pre-recursor environment recorded by
the staging invariant. -/
def GeneratedRecursors.toBlockCertificate
    (staged : StagedBlock safety env venv types ctors recursors
      outEnv outVEnv)
    (H : GeneratedRecursors safety staged.venvCtors lparams elimLevel c stats
      indTypes recInfos recursors)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (htypes : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv)
    (hctors : ∀ ci ∈ ctors.map Prod.snd,
      ci.toVConstant.WF staged.venvTypes)
    (hrules : ∀ df ∈ rules, df.WF outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  staged := staged
  typesWF := htypes
  ctorsWF := hctors
  recursorsWF := H.recursorsWF Hc Hbindings Hparams
  rulesWF := hrules

def BlockCertificate.block
    (_H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules

/-- A completed executable staging certificate directly discharges the
independent semantic well-formedness judgment. -/
theorem BlockCertificate.wf
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.staged.venvTypes, H.staged.venvCtors, outVEnv,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors, H.typesWF, H.ctorsWF, H.recursorsWF,
    H.rulesWF⟩

/-- The abstract installation result is fixed by the executable staging
certificate; reduction rules are installed only after every recursor. -/
theorem BlockCertificate.install
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some (outVEnv.addDefEqs rules) := by
  simp [BlockCertificate.block, VInductBlock.install,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors]

/-- Semantic endpoint of the executable block certificates. Once source
typing/formation and the independent compilation relation are supplied, the
staged executable installation constructs the abstract inductive extension. -/
theorem BlockCertificate.addInductAbstract
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hdecl : decl.WF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqs rules) :=
  .intro Hdecl Hcompile H.wf H.install

theorem BlockCertificate.addInductOfFormation
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hformation : FormationCertificate venv decl)
    (Hsource : decl.SourceWF venv)
    (Hcompile : decl.CompilesTo venv H.block) :
    VEnv.AddInduct venv decl (outVEnv.addDefEqs rules) :=
  H.addInductAbstract (Hformation.declWF Hsource) Hcompile

/-- Final assembly point for the implementation-refinement boundary. Once
the executable traversals have supplied source formation, compilation shape,
staged typing, and production-map conservation, no further semantic facts are
hidden in `AddInduct`. -/
theorem BlockCertificate.addInduct
    (H : BlockCertificate checkSafety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (haligned : ∀ safety, Aligned safety C venv →
      Aligned safety C' (outVEnv.addDefEqs rules))
    (hdelta : ∀ {name ci}, C'.find? name = some ci →
      ci.deltaValue?.isSome → C.find? name = some ci)
    (heq : ∀ info, C'.find? ``Eq = some (.inductInfo info) →
      (outVEnv.addDefEqs rules).constants ``Eq = some eqConst) :
    AddInduct C venv decl C' (outVEnv.addDefEqs rules) :=
  .intro H.block hdecl hcompile H.wf H.install haligned hdelta heq

/-- The first executable check on every source inductive header is an ordinary
type-checker run. At an empty local context its successful result already
provides both the source translation and the abstract typing derivation; later
stages must transport the same statement through the common-parameter local
context. -/
theorem checkType_closed.WF
    (hvalid : CheckingEnv.Valid safety env venv)
    (hclosed : e.FVarsIn fun _ => False) :
    (TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType e)).WF
      fun ty => ∃ e' ty', TrTyping venv lparams [] e ty e' ty' := by
  have hfvars : e.FVarsIn fun fv => fv ∈ VLCtx.fvars ([] : VLCtx) :=
    hclosed.mono fun _ h => False.elim h
  exact TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := lparams) (fuel := fuel)
    (TypeChecker.checkType.WF hfvars)

/-- Exact parameter-telescope path followed by nested lowering. The relation
retains both the growing local context and the array of corresponding free
variables, making the later restoration substitution auditable. -/
inductive NestedParamOpening : LocalContext → Array Expr → Expr → Nat →
    LocalContext → Expr → Array Expr → Prop
  | done : NestedParamOpening lctx params type 0 lctx type params
  | step {id : FVarId} {name : Name} {dom body : Expr} {bi : BinderInfo} :
      NestedParamOpening
        (lctx.mkLocalDecl id name dom bi) (params.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx tail outParams →
      NestedParamOpening lctx params (.forallE name dom body bi) (n + 1)
        outLctx tail outParams

theorem NestedParamOpening.params_size
    (H : NestedParamOpening lctx params type n outLctx tail outParams) :
    outParams.size = params.size + n := by
  induction H with
  | done => simp
  | step _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem NestedParamOpening.params_extension
    (H : NestedParamOpening lctx params type n outLctx tail outParams) :
    ∃ suffix, outParams.toList = params.toList ++ suffix ∧
      suffix.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | @step lctx params name dom body bi id n outLctx tail outParams H ih =>
    rcases ih with ⟨suffix, heq, hlength⟩
    refine ⟨(.fvar id) :: suffix, ?_, by simp [hlength]⟩
    simpa [heq, List.append_assoc]

theorem NestedParamOpening.initial_size
    (H : NestedParamOpening {} #[] type n outLctx tail outParams) :
    outParams.size = n := by simpa using H.params_size

private theorem nestedWithParamsLoop_refines {α : Type}
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ outLctx tail outParams outState,
      NestedParamOpening lctx params type n outLctx tail outParams →
      (k outLctx tail outParams env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams.loop
      k lctx type params n env state).WF Q := by
  induction n generalizing lctx type params state with
  | zero =>
    simpa [Lean4Lean.ElimNestedInductive.withParams.loop] using
      Hk lctx type params state .done
  | succ n ih =>
    cases type with
    | forallE name dom body bi =>
      simp only [Lean4Lean.ElimNestedInductive.withParams.loop]
      simp only [mkFreshId, getNGen, setNGen,
        Lean4Lean.ElimNestedInductive.instMonadNameGeneratorM,
        StateT.get, StateT.set, StateT.modifyGet,
        bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      apply ih
      intro outLctx tail outParams outState Hresult
      exact Hk outLctx tail outParams outState (.step Hresult)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj =>
      exact Except.WF.throw

theorem ElimNestedInductive.withParams.refines {α : Type}
    (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ lctx tail params outState,
      NestedParamOpening {} #[] type nparams lctx tail params →
      (k lctx tail params env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams
      type nparams k env state).WF Q := by
  exact nestedWithParamsLoop_refines k env state Q Hk

/-- Successful parameter instantiation has consumed exactly the requested
number of leading forall binders; the returned term is precisely the exposed
residual instantiated with the supplied parameter array. -/
private theorem stripForallList_refines
    (indices : List Nat) (e : Expr) :
    ((forIn indices e fun _ current =>
      match current with
      | .forallE _ _ body _ => pure (ForInStep.yield body)
      | _ => do
        throw Lean4Lean.ElimNestedInductive.illFormed
        pure (ForInStep.yield current)) :
        Except Exception Expr).WF
      fun tail => Expr.ForallTelescope e indices.length tail := by
  induction indices generalizing e with
  | nil => exact Except.WF.pure (Expr.ForallTelescope.nil e)
  | cons i indices ih =>
    cases e with
    | forallE name dom body bi =>
      have Hrest := (ih body).mono fun tail H =>
        Expr.ForallTelescope.cons (name := name) (dom := dom) (bi := bi) H
      rw [List.forIn_cons]
      exact Except.WF.pureBind Hrest
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => exact Except.WF.throw

theorem instantiateForallParams_refines
    (e : Expr) (n : Nat) (params : Array Expr) :
    (Lean4Lean.ElimNestedInductive.instantiateForallParams e n params).WF
      fun out => ∃ tail, Expr.ForallTelescope e n tail ∧
        out = tail.instantiateRevRange 0 n params := by
  unfold Lean4Lean.ElimNestedInductive.instantiateForallParams
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change (((fun tail =>
      tail.instantiateRevRange 0 n params) <$>
    (forIn (List.range' 0 n) e fun _ current =>
      match current with
      | .forallE _ _ body _ => pure (ForInStep.yield body)
      | _ => do
        throw Lean4Lean.ElimNestedInductive.illFormed
        pure (ForInStep.yield current))) : Except Exception Expr).WF _
  exact Except.WF.map
    (f := fun tail => tail.instantiateRevRange 0 n params)
    (R := fun out => ∃ residual, Expr.ForallTelescope e n residual ∧
      out = residual.instantiateRevRange 0 n params)
    (stripForallList_refines (List.range' 0 n) e)
    (fun tail Htail =>
      (⟨tail, by simpa using Htail, rfl⟩ :
        ∃ residual, Expr.ForallTelescope e n residual ∧
          tail.instantiateRevRange 0 n params =
            residual.instantiateRevRange 0 n params))

/-- Parameter replacement cannot truncate either side of the substitution:
success records exact arity equality and the concrete simultaneous
abstraction/instantiation result. -/
theorem replaceNestedParams_refines
    (params : Array Expr) (e : Expr) (args : Array Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : args.size = params.size) :
    (Lean4Lean.ElimNestedInductive.replaceParams params e args env state).WF
      fun out => out.1 = (e.abstract args).instantiateRev params := by
  unfold Lean4Lean.ElimNestedInductive.replaceParams
  simp [hsize]
  intro out hout
  cases hout
  rfl

/-- Source constructors may not mention the private namespace used for
lowering-generated auxiliary families or projections. -/
def NoNestedAux (e : Expr) : Prop :=
  (e.find? fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false).isNone

theorem checkNoNestedAux_refines (name : Name) (e : Expr) :
    (Lean4Lean.checkNoNestedAux name e).WF fun _ => NoNestedAux e := by
  unfold Lean4Lean.checkNoNestedAux NoNestedAux
  cases hfind : e.find? fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false
  · exact Except.WF.pure (by simp [hfind])
  · exact Except.WF.throw

/-- Independent lookup contract used when restoring a generated auxiliary
constructor to its source constructor family. -/
structure AuxiliaryConstructorLookup
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor : Name) (nested : Expr) (auxFamily : Name) : Prop where
  exists_info : ∃ info : ConstructorVal,
    env.find? ctor = some (.ctorInfo info) ∧
    auxFamily = info.induct ∧
    result.aux2nested.find? info.induct = some nested

theorem getNestedIfAuxCtor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor : Name) :
    ∀ nested auxFamily,
      result.getNestedIfAuxCtor env ctor = some (nested, auxFamily) →
      AuxiliaryConstructorLookup result env ctor nested auxFamily := by
  intro nested auxFamily hout
  unfold Lean4Lean.ElimNestedInductive.Result.getNestedIfAuxCtor at hout
  cases hfound : env.find? ctor with
  | none => simp [hfound] at hout
  | some info =>
    cases info with
    | ctorInfo ctorInfo =>
      simp only [hfound] at hout
      cases hnested : result.aux2nested.find? ctorInfo.induct with
      | none => simp [hnested] at hout
      | some restored =>
        have hp : (restored, ctorInfo.induct) = (nested, auxFamily) := by
          simpa [hnested] using hout
        cases hp
        exact ⟨⟨ctorInfo, hfound, rfl, hnested⟩⟩
    | _ => simp_all

theorem restoreCtorName_eq
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor auxFamily sourceFamily : Name)
    (nested : Expr) (levels : List Level)
    (hlookup : result.getNestedIfAuxCtor env ctor =
      some (nested, auxFamily))
    (hhead : nested.getAppFn = .const sourceFamily levels) :
    result.restoreCtorName env ctor =
      ctor.replacePrefix auxFamily sourceFamily := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreCtorName
  simp [hlookup, hhead]
  rfl

theorem restoreNestedNode_recursor
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (name restored : Name) (levels : List Level)
    (hrec : auxRec.find? name = some restored) :
    result.restoreNestedNode env As auxRec (.const name levels) =
      some (.const restored levels) := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode, hrec]

theorem restoreNestedNode_family
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (family : Name) (levels : List Level)
    (happ : t.isApp = true)
    (hhead : t.getAppFn = .const family levels)
    (hfamily : result.aux2nested.find? family = some nested)
    (harity : result.nparams ≤ t.getAppArgs.size) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange ((nested.abstract result.params).instantiateRev As)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | app fn arg =>
    simp only [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode]
    simp [hhead, hfamily, harity]
  | bvar | fvar | mvar | sort | const | lam | forallE | letE | lit | mdata
      | proj => cases happ

theorem restoreNestedNode_constructor
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (ctorName auxFamily sourceFamily : Name)
    (headLevels sourceLevels : List Level)
    (happ : t.isApp = true)
    (hhead : t.getAppFn = .const ctorName headLevels)
    (hnotFamily : result.aux2nested.find? ctorName = none)
    (hlookup : result.getNestedIfAuxCtor env ctorName =
      some (nested, auxFamily))
    (harity : result.nparams ≤ t.getAppArgs.size)
    (hrestoredHead :
      ((nested.abstract result.params).instantiateRev As).getAppFn =
        .const sourceFamily sourceLevels) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange
        (mkAppN (.const (ctorName.replacePrefix auxFamily sourceFamily)
          sourceLevels)
          ((nested.abstract result.params).instantiateRev As).getAppArgs)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | app fn arg =>
    simp only [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode]
    simp [hhead, hnotFamily, hlookup, harity, Expr.withApp_eq]
    simp only [Expr.instantiateRev_eq, Expr.instantiate_eq,
      Array.toList_reverse] at hrestoredHead
    rw [hrestoredHead]
  | bvar | fvar | mvar | sort | const | lam | forallE | letE | lit | mdata
      | proj => cases happ

/-- Exact, cache-independent specification of `Expr.replace`. A successful
node callback stops traversal at that node; otherwise the relation records
the recursively restored children and the same update combinators used by
Lean's implementation. -/
inductive ExprReplacement (replaceNode : Expr → Option Expr) : Expr → Expr → Prop
  | hit (h : replaceNode input = some output) :
      ExprReplacement replaceNode input output
  | bvar (h : replaceNode (.bvar i) = none) :
      ExprReplacement replaceNode (.bvar i) (.bvar i)
  | fvar {fvarId : FVarId} (h : replaceNode (.fvar fvarId) = none) :
      ExprReplacement replaceNode (.fvar fvarId) (.fvar fvarId)
  | mvar {mvarId : MVarId} (h : replaceNode (.mvar mvarId) = none) :
      ExprReplacement replaceNode (.mvar mvarId) (.mvar mvarId)
  | sort (h : replaceNode (.sort level) = none) :
      ExprReplacement replaceNode (.sort level) (.sort level)
  | const (h : replaceNode (.const name levels) = none) :
      ExprReplacement replaceNode (.const name levels) (.const name levels)
  | lit (h : replaceNode (.lit literal) = none) :
      ExprReplacement replaceNode (.lit literal) (.lit literal)
  | app (h : replaceNode (.app fn arg) = none)
      (hfn : ExprReplacement replaceNode fn fn')
      (harg : ExprReplacement replaceNode arg arg') :
      ExprReplacement replaceNode (.app fn arg)
        (Expr.updateApp! (.app fn arg) fn' arg')
  | lam (h : replaceNode (.lam name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.lam name dom body bi)
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body')
  | forallE (h : replaceNode (.forallE name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.forallE name dom body bi)
        (Expr.updateForallE! (.forallE name dom body bi) dom' body')
  | letE (h : replaceNode (.letE name type value body nondep) = none)
      (htype : ExprReplacement replaceNode type type')
      (hvalue : ExprReplacement replaceNode value value')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.letE name type value body nondep)
        (Expr.updateLetE! (.letE name type value body nondep)
          type' value' body')
  | mdata (h : replaceNode (.mdata data body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.mdata data body)
        (Expr.updateMData! (.mdata data body) body')
  | proj (h : replaceNode (.proj typeName index body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.proj typeName index body)
        (Expr.updateProj! (.proj typeName index body) body')

theorem ExprReplacement.ofReplace
    (replaceNode : Expr → Option Expr) :
    ∀ input, ExprReplacement replaceNode input (input.replace replaceNode) := by
  intro input
  induction input with
  | bvar i =>
    cases h : replaceNode (.bvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.bvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | fvar i =>
    cases h : replaceNode (.fvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.fvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | mvar i =>
    cases h : replaceNode (.mvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.mvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | sort level =>
    cases h : replaceNode (.sort level) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.sort h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | const name levels =>
    cases h : replaceNode (.const name levels) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.const h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | lit literal =>
    cases h : replaceNode (.lit literal) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.lit h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | app fn arg hfn harg =>
    cases h : replaceNode (.app fn arg) with
    | none =>
      rw [Expr.replace_eq] at hfn harg
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .app h hfn harg
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)

  | lam name dom body bi hdom hbody =>
    cases h : replaceNode (.lam name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .lam h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | forallE name dom body bi hdom hbody =>
    cases h : replaceNode (.forallE name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .forallE h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | letE name type value body nondep htype hvalue hbody =>
    cases h : replaceNode (.letE name type value body nondep) with
    | none =>
      rw [Expr.replace_eq] at htype hvalue hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .letE h htype hvalue hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | mdata data body hbody =>
    cases h : replaceNode (.mdata data body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .mdata h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | proj typeName index body hbody =>
    cases h : replaceNode (.proj typeName index body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .proj h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)

/-- The body traversal used by `restoreNested` is now related exactly to its
three independently specified node-restoration cases. -/
theorem restoreNested_body
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (body : Expr) :
    ExprReplacement (result.restoreNestedNode env As auxRec) body
      (body.replace (result.restoreNestedNode env As auxRec)) :=
  ExprReplacement.ofReplace _ body

/-- Mixed forall/lambda telescope accepted by nested restoration. The
production function preserves the outer kind chosen by the original root,
while both binder forms are accepted during opening. -/
inductive RestoreTelescope : Expr → Nat → Prop
  | done : RestoreTelescope e 0
  | forallE : RestoreTelescope body n →
      RestoreTelescope (.forallE name dom body bi) (n + 1)
  | lam : RestoreTelescope body n →
      RestoreTelescope (.lam name dom body bi) (n + 1)

/-- Any prefix of a generated lambda telescope is accepted by nested
restoration. -/
theorem Expr.LambdaTelescope.restorePrefix
    (H : Expr.LambdaTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | @cons body arity residual name dom bi Hbody =>
      apply RestoreTelescope.lam
      exact ih Hbody (by omega)

/-- Production iota RHSs always expose at least the common-parameter lambda
prefix consumed by `restoreNested`. -/
theorem BoundGeneratedRecursorRule.rhsRestoreTelescope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope rule.rhs nparams := by
  apply H.rhsLambdaTelescope.restorePrefix
  rw [hparams]
  have hp : stats.params.size = H.params_bound.fvars.length := by
    simpa using congrArg Array.size H.params_bound.expressions
  unfold BoundGeneratedRecursorRule.binders
  simp only [List.length_append]
  omega

theorem RestoreTelescope.instantiate1'
    (H : RestoreTelescope e n) (arg : Expr) (depth : Nat) :
    RestoreTelescope (e.instantiate1' arg depth) n := by
  induction H generalizing depth with
  | done => exact .done
  | forallE H ih =>
    simp only [Expr.instantiate1']
    exact .forallE (ih (depth + 1))
  | lam H ih =>
    simp only [Expr.instantiate1']
    exact .lam (ih (depth + 1))

theorem RestoreTelescope.instantiate1
    (H : RestoreTelescope e n) (arg : Expr) :
    RestoreTelescope (e.instantiate1 arg) n := by
  rw [Expr.instantiate1_eq]
  exact H.instantiate1' arg 0

/-- Exact context/free-variable opening relation for `openRestoreParams`. -/
inductive RestoreParamOpening : LocalContext → Array Expr → Expr → Nat →
    LocalContext → Array Expr → Expr → Prop
  | done : RestoreParamOpening lctx As e 0 lctx As e
  | forallE {id : FVarId} :
      RestoreParamOpening
        (lctx.mkLocalDecl id name dom bi) (As.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx outAs tail →
      RestoreParamOpening lctx As (.forallE name dom body bi) (n + 1)
        outLctx outAs tail
  | lam {id : FVarId} :
      RestoreParamOpening
        (lctx.mkLocalDecl id name dom bi) (As.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx outAs tail →
      RestoreParamOpening lctx As (.lam name dom body bi) (n + 1)
        outLctx outAs tail

theorem RestoreParamOpening.params_size
    (H : RestoreParamOpening lctx As e n outLctx outAs tail) :
    outAs.size = As.size + n := by
  induction H with
  | done => simp
  | forallE _ ih | lam _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem RestoreParamOpening.params_extension
    (H : RestoreParamOpening lctx As e n outLctx outAs tail) :
    ∃ suffix, outAs.toList = As.toList ++ suffix ∧ suffix.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | forallE H ih | lam H ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    rcases ih with ⟨suffix, heq, hlength⟩
    refine ⟨(.fvar id) :: suffix, ?_, by simp [hlength]⟩
    simpa [heq, List.append_assoc]

theorem RestoreParamOpening.initial_size
    (H : RestoreParamOpening {} #[] e n outLctx outAs tail) :
    outAs.size = n := by
  simpa using H.params_size

theorem openRestoreParams_refines
    (H : RestoreTelescope e n) (lctx : LocalContext) (As : Array Expr)
    (ngen : NameGenerator) :
    ∀ (out : LocalContext × Array Expr × Expr) outNgen,
      Lean4Lean.ElimNestedInductive.Result.openRestoreParams n lctx As e ngen =
        (out, outNgen) →
      RestoreParamOpening lctx As e n out.1 out.2.1 out.2.2 := by
  induction n generalizing e lctx As ngen with
  | zero =>
    intro out outNgen hout
    simp [Lean4Lean.ElimNestedInductive.Result.openRestoreParams] at hout
    cases hout
    exact .done
  | succ n ih =>
    cases H with
    | @forallE body _ name dom bi Hbody =>
      intro out outNgen hout
      simp only [Lean4Lean.ElimNestedInductive.Result.openRestoreParams,
        mkFreshId, getNGen, setNGen, StateT.get, StateT.set,
        StateT.modifyGet, bind, StateT.bind, pure, StateT.pure] at hout
      exact .forallE (ih (Hbody.instantiate1 (.fvar ⟨ngen.curr⟩))
        _ _ _ out outNgen hout)
    | @lam body _ name dom bi Hbody =>
      intro out outNgen hout
      simp only [Lean4Lean.ElimNestedInductive.Result.openRestoreParams,
        mkFreshId, getNGen, setNGen, StateT.get, StateT.set,
        StateT.modifyGet, bind, StateT.bind, pure, StateT.pure] at hout
      exact .lam (ih (Hbody.instantiate1 (.fvar ⟨ngen.curr⟩))
        _ _ _ out outNgen hout)

/-- End-to-end abstract relation for nested restoration: open exactly the
recorded parameter telescope, restore every body node, then rebuild the same
outer forall/lambda kind selected by the source root. -/
def NestedRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (input output : Expr) : Prop :=
  ∃ lctx As body restoredBody,
    RestoreParamOpening {} #[] input result.nparams lctx As body ∧
    ExprReplacement (result.restoreNestedNode env As auxRec)
      body restoredBody ∧
    output = if input.isForall then lctx.mkForall As restoredBody
      else lctx.mkLambda As restoredBody

theorem restoreNested_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name) (input : Expr)
    (Htelescope : RestoreTelescope input result.nparams) :
    NestedRestoration result env auxRec input
      (result.restoreNested env input auxRec) := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreNested
  generalize hopen :
    Lean4Lean.ElimNestedInductive.Result.openRestoreParams result.nparams
      {} #[] input ({ namePrefix := `_nested_fresh } : NameGenerator) = opened
  rcases opened with ⟨⟨lctx, As, body⟩, outNGen⟩
  have Hopening := openRestoreParams_refines Htelescope {} #[]
    ({ namePrefix := `_nested_fresh } : NameGenerator)
    (lctx, As, body) outNGen hopen
  simp [hopen]
  exact ⟨lctx, As, body,
    body.replace (result.restoreNestedNode env As auxRec),
    Hopening, restoreNested_body result env As auxRec body,
    by simp only [Expr.replace_eq]⟩

/-- Exact rule-level restoration contract used by `processRec`. -/
structure RuleRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name)
    (oldRule newRule : RecursorRule) : Prop where
  ctor : newRule.ctor = if newRecName == oldRecName then oldRule.ctor
    else result.restoreCtorName env oldRule.ctor
  nfields : newRule.nfields = oldRule.nfields
  rhs : NestedRestoration result env auxRec oldRule.rhs newRule.rhs

theorem restoreRule_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (rule : RecursorRule)
    (Htelescope : RestoreTelescope rule.rhs result.nparams) :
    RuleRestoration result env auxRec oldRecName newRecName rule
      (result.restoreRule env auxRec oldRecName newRecName rule) where
  ctor := rfl
  nfields := rfl
  rhs := restoreNested_refines result env auxRec rule.rhs Htelescope

inductive RulesRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    List RecursorRule → List RecursorRule → Prop
  | nil : RulesRestoration result env auxRec oldRecName newRecName [] []
  | cons : RuleRestoration result env auxRec oldRecName newRecName old new →
      RulesRestoration result env auxRec oldRecName newRecName olds news →
      RulesRestoration result env auxRec oldRecName newRecName
        (old :: olds) (new :: news)

theorem RulesRestoration.length
    (H : RulesRestoration result env auxRec oldRecName newRecName olds news) :
    news.length = olds.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RulesRestoration.entry
    (H : RulesRestoration result env auxRec oldRecName newRecName olds news) :
    ∀ i (hold : i < olds.length) (hnew : i < news.length),
      RuleRestoration result env auxRec oldRecName newRecName
        olds[i] news[i] := by
  induction H with
  | nil =>
    intro i hold
    simp at hold
  | @cons old new olds news Hhead Htail ih =>
    intro i hold hnew
    cases i with
    | zero => simpa using Hhead
    | succ i => exact ih i (by simpa using hold) (by simpa using hnew)

theorem restoreRules_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    ∀ rules,
      (∀ rule ∈ rules, RestoreTelescope rule.rhs result.nparams) →
      RulesRestoration result env auxRec oldRecName newRecName rules
        (rules.map (result.restoreRule env auxRec oldRecName newRecName)) := by
  intro rules Htelescope
  induction rules with
  | nil => exact .nil
  | cons rule rules ih =>
    exact .cons
      (restoreRule_refines result env auxRec oldRecName newRecName rule
        (Htelescope rule (by simp)))
      (ih fun tail htail => Htelescope tail (by simp [htail]))

/-- A complete generated constructor batch satisfies the operational
restoration precondition without an additional telescope assumption. -/
theorem BoundGeneratedRecursorRules.restoreRules_refines
    (H : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules)
    (hparams : result.nparams = stats.params.size)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    RulesRestoration result prodEnv auxRec oldRecName newRecName rules
      (rules.map
        (result.restoreRule prodEnv auxRec oldRecName newRecName)) := by
  apply Lean4Lean.VerifyInductive.restoreRules_refines
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hctor : i < ctors.length := by
    rw [← H.length]
    exact hi
  rcases H.entry i hctor hi with ⟨Hrule⟩
  exact Hrule.rhsRestoreTelescope hparams

/-- Recursor-level restoration records every overwritten metadata field and
the pointwise rule restoration relation. -/
structure RecursorRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName newRecName : Name)
    (oldInfo newInfo : RecursorVal) : Prop where
  name : newInfo.name = newRecName
  levelParams : newInfo.levelParams = oldInfo.levelParams
  type : NestedRestoration result env auxRec oldInfo.type newInfo.type
  all : newInfo.all = allIndNames
  numParams : newInfo.numParams = oldInfo.numParams
  numIndices : newInfo.numIndices = oldInfo.numIndices
  numMotives : newInfo.numMotives = oldInfo.numMotives
  numMinors : newInfo.numMinors = oldInfo.numMinors
  rules : RulesRestoration result env auxRec oldRecName newRecName
    oldInfo.rules newInfo.rules
  k : newInfo.k = oldInfo.k
  isUnsafe : newInfo.isUnsafe = oldInfo.isUnsafe

theorem restoreRecursor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName newRecName : Name)
    (info : RecursorVal)
    (Htype : RestoreTelescope info.type result.nparams)
    (Hrules : ∀ rule ∈ info.rules,
      RestoreTelescope rule.rhs result.nparams) :
    RecursorRestoration result env auxRec allIndNames oldRecName newRecName
      info (result.restoreRecursor env auxRec allIndNames
        oldRecName newRecName info) where
  name := rfl
  levelParams := rfl
  type := restoreNested_refines result env auxRec info.type Htype
  all := rfl
  numParams := rfl
  numIndices := rfl
  numMotives := rfl
  numMinors := rfl
  rules := restoreRules_refines result env auxRec oldRecName newRecName
    info.rules Hrules
  k := rfl
  isUnsafe := rfl

/-- Installing an operationally restored auxiliary recursor advances the
independent auxiliary-name certificate. Translation identifies the production
`RecursorVal` name with the abstract constant name; no semantic claim about
its restored rules is hidden in this naming step. -/
theorem AuxiliaryRestorationPrefix.pushRestoredRecursor
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName oldInfo newInfo)
    (Htr : TrConstVal safety trEnv (.recInfo newInfo) recursor)
    (hnewName : newRecName =
      (decl.recursorName main).appendIndexAfter (recursors.length + 1)) :
    AuxiliaryRestorationPrefix decl block main
      (recursors ++ [recursor]) rules := by
  apply H.pushRecursor
  calc
    recursor.name = newInfo.name := Htr.2.symm
    _ = newRecName := Hrestore.name
    _ = (decl.recursorName main).appendIndexAfter
        (recursors.length + 1) := hnewName

/-- Restored-rule guardedness is deliberately supplied independently of
`RuleRestoration`: the latter is a syntactic executable refinement, whereas
this premise is the semantic fact required by `NestedCompilation`. -/
theorem AuxiliaryRestorationPrefix.appendRestoredRules
    (H : AuxiliaryRestorationPrefix decl block main recursors rules)
    (Hrestore : RulesRestoration result prodEnv auxRec oldRecName newRecName
      sourceRules restoredRules)
    (htranslated : abstractRules.length = restoredRules.length)
    (hguarded : ∀ i (hsource : i < sourceRules.length)
      (hrestored : i < restoredRules.length)
      (habstract : i < abstractRules.length),
      RuleRestoration result prodEnv auxRec oldRecName newRecName
        sourceRules[i] restoredRules[i] →
      ∃ fieldVars, abstractRules[i].rhs.GuardedIota
        (block.recursors.map (·.name)) fieldVars 0) :
    AuxiliaryRestorationPrefix decl block main recursors
      (rules ++ abstractRules) := by
  apply H.appendRules
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hrestored : i < restoredRules.length := by
    rw [← htranslated]
    simpa using hi
  have hsource : i < sourceRules.length := by
    rw [← Hrestore.length]
    exact hrestored
  have Hentry := Hrestore.entry i hsource hrestored
  exact hguarded i hsource hrestored hi Hentry

/-- Syntactic facts that must hold before an expression can be treated as a
nested occurrence. The environment lookup and parameter scan are certified
separately, at the point where their reader/state effects are exposed. -/
structure NestedAppShape (e : Expr) : Prop where
  isApp : e.isApp = true
  constHead : ∃ fn levels, e.getAppFn = .const fn levels

theorem isNestedInductiveApp_shape
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.1.isSome → NestedAppShape e := by
  intro out hout hsome
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp only [happ, Bool.not_false, if_true] at hout
    change Except.ok (none, state) = .ok out at hout
    cases hout
    simp at hsome
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      exact ⟨happTrue, ⟨fn, levels, hhead⟩⟩
    | _ =>
      simp [happTrue, hhead, ReaderT.pure, StateT.pure] at hout
      cases hout
      simp at hsome

/-- Independent specification of the occurrence test used while scanning
parameters of a previously declared inductive application. -/
def MentionsNestedNewType
    (newTypes : Array InductiveType) (e : Expr) : Prop :=
  (e.find? fun
    | .const name _ => newTypes.any fun type => name == type.name
    | _ => false).isSome

theorem mentionsNestedNewType_iff
    (newTypes : Array InductiveType) (e : Expr) :
    Lean4Lean.ElimNestedInductive.mentionsNestedNewType newTypes e = true ↔
      MentionsNestedNewType newTypes e := by
  rfl

theorem nestedParamFlags_fst
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) :
    (Lean4Lean.ElimNestedInductive.nestedParamFlags newTypes args n).1 = true ↔
      ∃ i, i < n ∧ MentionsNestedNewType newTypes args[i]! := by
  induction n with
  | zero => simp [Lean4Lean.ElimNestedInductive.nestedParamFlags]
  | succ n ih =>
    rw [Lean4Lean.ElimNestedInductive.nestedParamFlags]
    simp only [Bool.or_eq_true, ih, mentionsNestedNewType_iff]
    constructor
    · rintro (⟨i, hi, hmentions⟩ | hmentions)
      · exact ⟨i, by omega, hmentions⟩
      · exact ⟨n, by omega, hmentions⟩
    · rintro ⟨i, hi, hmentions⟩
      by_cases h : i = n
      · subst i; exact Or.inr hmentions
      · exact Or.inl ⟨i, by omega, hmentions⟩

theorem nestedParamFlags_snd_false
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) :
    (Lean4Lean.ElimNestedInductive.nestedParamFlags newTypes args n).2 = false ↔
      ∀ i, i < n → args[i]!.hasLooseBVars = false := by
  induction n with
  | zero => simp [Lean4Lean.ElimNestedInductive.nestedParamFlags]
  | succ n ih =>
    rw [Lean4Lean.ElimNestedInductive.nestedParamFlags]
    simp only [Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨hprev, hn⟩ i hi
      by_cases h : i = n
      · simpa [h] using hn
      · exact hprev i (by omega)
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall n (by omega)⟩

/-- Abstract contract for the parameter scan in
`isNestedInductiveApp?`: the application has enough arguments, at least one
parameter mentions a family currently being lowered, and every scanned
parameter is closed with respect to bound variables. -/
structure NestedParameterScan
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) : Prop where
  arity : n ≤ args.size
  nested : ∃ i, i < n ∧ MentionsNestedNewType newTypes args[i]!
  closed : ∀ i, i < n → args[i]!.hasLooseBVars = false

theorem NestedParameterScan.noLoose
    (H : NestedParameterScan newTypes args n) (hi : i < n) :
    args[i]!.hasLooseBVars = false :=
  H.closed i hi

theorem NestedParameterScan.hasOccurrence
    (H : NestedParameterScan newTypes args n) :
    ∃ i, i < args.size ∧ MentionsNestedNewType newTypes args[i]! := by
  rcases H.nested with ⟨i, hi, hmentions⟩
  exact ⟨i, Nat.lt_of_lt_of_le hi H.arity, hmentions⟩

/-- Full abstract acceptance contract for nested-application recognition.
This is deliberately stated without reference to the executable loop, so its
eventual refinement theorem cannot silently inherit an implementation bug. -/
structure NestedAppCandidate (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (e : Expr) (info : InductiveVal) : Prop where
  shape : NestedAppShape e
  headFound : ∃ fn levels, e.getAppFn = .const fn levels ∧
    env.find? fn = some (.inductInfo info)
  parameters : NestedParameterScan state.newTypes e.getAppArgs info.numParams

theorem isNestedInductiveApp_candidate
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => ∀ info, out.1 = some info →
        NestedAppCandidate env state e info := by
  intro out hout info hinfo
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp [happ] at hout
    cases hout
    simp at hinfo
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      simp [happTrue, hhead,
        Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
      cases hfound : env.find? fn with
      | none =>
        simp [hfound] at hout
        change Except.ok (none, state) = .ok out at hout
        cases hout
        simp at hinfo
      | some found =>
        cases found with
        | inductInfo ci =>
          simp only [hfound] at hout
          by_cases harity : e.getAppArgs.size < ci.numParams
          · simp [harity] at hout
            cases hout
            simp at hinfo
          · simp only [harity, ↓reduceIte] at hout
            let flags := Lean4Lean.ElimNestedInductive.nestedParamFlags
              state.newTypes e.getAppArgs ci.numParams
            by_cases hnested : flags.1 = false
            · simp [flags, hnested] at hout
              cases hout
              simp at hinfo
            · have hnestedTrue : flags.1 = true := by
                cases h : flags.1 <;> simp_all
              by_cases hloose : flags.2 = true
              · simp [flags, hnestedTrue, hloose] at hout
                cases hout
              · have hlooseFalse : flags.2 = false := by
                  cases h : flags.2 <;> simp_all
                simp [flags, hnestedTrue, hlooseFalse] at hout
                cases hout
                simp only [Option.some.injEq] at hinfo
                subst info
                refine {
                  shape := ⟨happTrue, ⟨fn, levels, hhead⟩⟩
                  headFound := ⟨fn, levels, hhead, hfound⟩
                  parameters := ?_ }
                refine {
                  arity := by omega
                  nested := (nestedParamFlags_fst
                    state.newTypes e.getAppArgs ci.numParams).mp hnestedTrue
                  closed := (nestedParamFlags_snd_false
                    state.newTypes e.getAppArgs ci.numParams).mp hlooseFalse }
        | _ =>
          simp [hfound] at hout
          change Except.ok (none, state) = .ok out at hout
          cases hout
          simp at hinfo
    | _ =>
      simp [happTrue, hhead] at hout
      cases hout
      simp at hinfo

theorem isNestedInductiveApp_preservesState
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.2 = state := by
  intro out hout
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp [happ] at hout
    cases hout
    rfl
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      simp [happTrue, hhead,
        Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
      cases hfound : env.find? fn with
      | none =>
        simp [hfound] at hout
        cases hout
        rfl
      | some found =>
        cases found with
        | inductInfo ci =>
          simp only [hfound] at hout
          by_cases harity : e.getAppArgs.size < ci.numParams
          · simp [harity] at hout
            cases hout
            rfl
          · simp only [harity, ↓reduceIte] at hout
            let flags := Lean4Lean.ElimNestedInductive.nestedParamFlags
              state.newTypes e.getAppArgs ci.numParams
            by_cases hnested : flags.1 = false
            · simp [flags, hnested] at hout
              cases hout
              rfl
            · have hnestedTrue : flags.1 = true := by
                cases h : flags.1 <;> simp_all
              by_cases hloose : flags.2 = true
              · simp [flags, hnestedTrue, hloose] at hout
                cases hout
              · have hlooseFalse : flags.2 = false := by
                  cases h : flags.2 <;> simp_all
                simp [flags, hnestedTrue, hlooseFalse] at hout
                cases hout
                rfl
        | _ =>
          simp [hfound] at hout
          cases hout
          rfl
    | _ =>
      simp [happTrue, hhead] at hout
      cases hout
      rfl

/-- Reader/state bind specialized to nested lowering. -/
theorem nestedBind.WF
    {α β : Type} {P : α × Lean4Lean.ElimNestedInductive.State → Prop}
    {Q : β × Lean4Lean.ElimNestedInductive.State → Prop}
    {x : Lean4Lean.ElimNestedInductive.M α}
    {f : α → Lean4Lean.ElimNestedInductive.M β}
    (Hx : (x env state).WF P)
    (Hf : ∀ a nextState, P (a, nextState) →
      (f a env nextState).WF Q) :
    ((x >>= f) env state).WF Q := by
  exact Hx.bind fun result hresult => Hf result.1 result.2 hresult

/-- Any successful replacement is rooted in an occurrence satisfying the
independent recognition contract. This prefix theorem intentionally leaves
cache reuse and fresh auxiliary generation to separate certificates. -/
theorem replaceIfNested_recognized
    (lctx : LocalContext) (params As : Array Expr) (e : Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.replaceIfNested
      lctx params As e env state).WF fun out =>
        out.1.isSome → ∃ info, NestedAppCandidate env state e info := by
  rw [Lean4Lean.ElimNestedInductive.replaceIfNested]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e)
    (P := fun recognized =>
      recognized.2 = state ∧ ∀ info, recognized.1 = some info →
        NestedAppCandidate env state e info) ?_ ?_
  · intro recognized hrecognized
    exact ⟨isNestedInductiveApp_preservesState e env state
        recognized hrecognized,
      isNestedInductiveApp_candidate e env state recognized hrecognized⟩
  · intro recognized nextState hrecognized
    rcases hrecognized with ⟨hstate, hcandidate⟩
    cases hstate
    cases recognized with
    | none =>
      exact Except.WF.pure (by simp)
    | some info =>
      intro out _ hout
      exact ⟨info, hcandidate info rfl⟩

/-- Reference formulation of the executable header-checking prefix. Keeping
the closure check in the statement is important: it is what turns the
type-checker's context-relative result into a source declaration judgment. -/
def checkHeader (env : Environment) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) (name : Name) (type : Expr) :
    Except Exception Expr := do
  env.checkNoMVarNoFVar name type
  TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType type)

theorem checkHeader.WF
    (hvalid : CheckingEnv.Valid safety env venv) :
    (checkHeader env safety lparams fuel name type).WF (fun checkedType =>
      ∃ type' checkedType',
        TrTyping venv lparams [] type checkedType type' checkedType') := by
  unfold checkHeader
  have hno : (env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkType_closed.WF (lparams := lparams) (fuel := fuel) hvalid hclosed

end VerifyInductive
end Lean4Lean
