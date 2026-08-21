import Lean4Lean.Verify.Inductive.Basic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

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

/-- Expose the next family-local parameter from `TypeShape` as a certified
presentation of the whole source header. -/
theorem VInductDecl.TypeShape.nextParameter
    {decl : VInductDecl} {env : VEnv} {params : List VExpr}
    {target : VInductiveType} {i : Nat}
    (H : decl.TypeShape env params target)
    (hi : i < decl.nparams) :
    ∃ (ownParams : List VExpr)
        (expectedDomain expectedBody targetType : VExpr),
      ownParams.length = decl.nparams ∧
      ownParams[i]? = some expectedDomain ∧
      decl.ParamsDefEq env params ownParams ∧
      env.IsDefEq decl.uvars [] target.type
        (VExpr.wrapForalls (ownParams.take i)
          (.forallE expectedDomain expectedBody)) targetType := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, _hindicesTake, hparams, _hresult⟩
  rcases VExpr.takeForalls_rebuild hparamsTake with
    ⟨hnormalizedEq, hownLength⟩
  have hiOwn : i < ownParams.length := by omega
  let expectedBody :=
    VExpr.wrapForalls (ownParams.drop (i + 1)) afterParams
  have hdecomp : ownParams =
      ownParams.take i ++ ownParams[i] :: ownParams.drop (i + 1) := by
    calc
      ownParams = ownParams.take (i + 1) ++ ownParams.drop (i + 1) :=
        (List.take_append_drop (i + 1) ownParams).symm
      _ = (ownParams.take i ++ [ownParams[i]]) ++
          ownParams.drop (i + 1) := by
        rw [List.take_succ_eq_append_getElem hiOwn]
      _ = ownParams.take i ++ ownParams[i] :: ownParams.drop (i + 1) := by
        simp
  refine ⟨ownParams, ownParams[i], expectedBody, exprType, hownLength,
    List.getElem?_eq_getElem hiOwn, hparams, ?_⟩
  have hwrap : VExpr.wrapForalls ownParams afterParams =
      VExpr.wrapForalls (ownParams.take i)
        (.forallE ownParams[i] expectedBody) := by
    calc
      VExpr.wrapForalls ownParams afterParams =
          VExpr.wrapForalls
            (ownParams.take i ++ ownParams[i] :: ownParams.drop (i + 1))
            afterParams := congrArg (fun xs =>
              VExpr.wrapForalls xs afterParams) hdecomp
      _ = VExpr.wrapForalls (ownParams.take i)
          (VExpr.wrapForalls
            (ownParams[i] :: ownParams.drop (i + 1)) afterParams) :=
        VExpr.wrapForalls_append _ _ _
      _ = VExpr.wrapForalls (ownParams.take i)
          (.forallE ownParams[i] expectedBody) := rfl
  rw [hnormalizedEq, hwrap] at hnormalized
  exact hnormalized

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

/-- Constructor-tail formation together with the typing fact recovered by
fully applying the checked inductive header. -/
structure ConstructorTailCertificate (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) (ctx : List VExpr) (depth : Nat)
    (tail : VExpr) : Prop where
  shape : decl.CtorTailWF env target ctx depth tail
  isType : env.IsType decl.uvars ctx tail

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
  types : ∀ i, i < done → (hi : i < target.ctors.length) →
    envTypes.IsType decl.uvars [] target.ctors[i].type

theorem ConstructorTypePrefix.empty (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) :
    ConstructorTypePrefix envTypes decl params target 0 where
  covered := Nat.zero_le _
  shapes _ h := by omega
  types _ h := by omega

theorem ConstructorTypePrefix.push
    (H : ConstructorTypePrefix envTypes decl params target done)
    (hi : done < target.ctors.length)
    (hshape : decl.CtorShape envTypes params target target.ctors[done])
    (htype : envTypes.IsType decl.uvars [] target.ctors[done].type) :
    ConstructorTypePrefix envTypes decl params target (done + 1) where
  covered := by omega
  shapes i hidone hi' := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.shapes i (by omega) hi'
  types i hidone hi' := by
    by_cases h : i = done
    · subst i; exact htype
    · exact H.types i (by omega) hi'

/-- Shapes accumulated by the outer family loop. -/
structure ConstructorTypesPrefix (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (done : Nat) : Prop where
  covered : done ≤ decl.types.length
  shapes : ∀ i, i < done → (hi : i < decl.types.length) →
    ∀ j (hj : j < decl.types[i].ctors.length),
      decl.CtorShape envTypes params decl.types[i] decl.types[i].ctors[j]
  types : ∀ i, i < done → (hi : i < decl.types.length) →
    ∀ j (hj : j < decl.types[i].ctors.length),
      envTypes.IsType decl.uvars [] decl.types[i].ctors[j].type

theorem ConstructorTypesPrefix.empty (envTypes : VEnv)
    (decl : VInductDecl) (params : List VExpr) :
    ConstructorTypesPrefix envTypes decl params 0 where
  covered := Nat.zero_le _
  shapes _ h := by omega
  types _ h := by omega

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
  types i hidone hi' j hj := by
    by_cases h : i = done
    · subst i; exact Htype.types j hj hj
    · exact H.types i (by omega) hi' j hj

structure CheckedConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  formation : ConstructorCertificate env decl envTypes params
  types : ∀ ctor ∈ decl.constructorConstants,
    envTypes.IsType decl.uvars [] ctor.type

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

theorem ConstructorTypesPrefix.checkedComplete
    (H : ConstructorTypesPrefix envTypes decl params decl.types.length) :
    CheckedConstructorCertificate env decl envTypes params where
  formation := H.complete
  types ctor hctor := by
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, rfl⟩
    exact H.types i hi hi j hj

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
  typesInstalled : env.addConstVals decl.typeConstants = some envTypes
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
    (htypes : env.addConstVals decl.typeConstants = some envTypes)
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

/-- An application spine headed by a local variable cannot be one of Lean's
distinguished parameter-annotation applications. -/
theorem Expr.isAppOfArity_eq_false_of_getAppFn_fvar
    {e : Expr} (h : e.getAppFn = .fvar fv) (name : Name) (arity : Nat) :
    e.isAppOfArity name arity = false := by
  induction e generalizing arity with
  | app fn arg ihFn _ =>
    cases arity with
    | zero => rfl
    | succ arity =>
      apply ihFn
      simpa only [Expr.getAppFn] using h
  | _ => cases arity <;> simp_all [Expr.getAppFn, Expr.isAppOfArity]

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

@[simp] theorem Expr.foldl_mkApp_eq (args : List Expr) (fn : Expr) :
    args.foldl Lean.mkApp fn = args.foldl Expr.app fn := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons, Lean.mkApp]
    exact ih (.app fn arg)

theorem Expr.mkAppN_eq_mkAppList (fn : Expr) (args : Array Expr) :
    mkAppN fn args = Expr.mkAppList fn args.toList := by
  unfold mkAppN
  rw [← Array.foldl_toList, Expr.mkAppList_eq_foldl]
  exact Expr.foldl_mkApp_eq args.toList fn

theorem TrExprS.IsUnique.mkAppList
    (hfn : TrExprS.IsUnique fn)
    (hargs : ∀ arg ∈ args, TrExprS.IsUnique arg) :
    TrExprS.IsUnique (Expr.mkAppList fn args) := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons arg args ih =>
    exact ih ⟨hfn, hargs arg (by simp)⟩ (by
      intro later hlater
      exact hargs later (by simp [hlater]))

theorem TrExprS.IsUnique.mkAppN
    (hfn : TrExprS.IsUnique fn)
    (hargs : ∀ arg ∈ args, TrExprS.IsUnique arg) :
    TrExprS.IsUnique (mkAppN fn args) := by
  rw [Expr.mkAppN_eq_mkAppList]
  exact Lean4Lean.VerifyInductive.TrExprS.IsUnique.mkAppList hfn
    fun arg harg => hargs arg
    (Array.mem_toList_iff.mp harg)

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

/-- Remove the same number of newest declarations from both sides of a
complete context conversion. -/
theorem VEnv.IsDefEqCtx.dropHeads
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂) (n : Nat) :
    VEnv.IsDefEqCtx env U [] (Γ₁.drop n) (Γ₂.drop n) := by
  induction n generalizing Γ₁ Γ₂ with
  | zero => simpa using H
  | succ n ih =>
    cases H with
    | zero => exact .zero
    | succ H _ =>
      simpa only [List.drop_succ_cons] using ih H

/-- Close the same number of newest declarations on both sides of a context
conversion.  Corresponding domains may differ definitionally, so the two
resulting forall telescopes need not be syntactically equal; `forallEDF`
turns the context conversion into exactly the required type equality. -/
theorem VEnv.IsDefEqCtx.closeHeads
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (n : Nat) (hn : n ≤ Γ₁.length)
    (Hbody : env.IsDefEq U Γ₁ body₁ body₂ (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U (Γ₁.drop n)
      (VExpr.wrapForalls (Γ₁.take n).reverse body₁)
      (VExpr.wrapForalls (Γ₂.take n).reverse body₂)
      (.sort resultLevel) := by
  induction n generalizing Γ₁ Γ₂ body₁ body₂ bodyLevel with
  | zero =>
    exact ⟨bodyLevel, by simpa [VExpr.wrapForalls] using Hbody⟩
  | succ n ih =>
    cases H with
    | zero => simp at hn
    | @succ Γ₁ Γ₂ domain₁ domain₂ domainLevel Hctx Hdomain =>
      have hn' : n ≤ Γ₁.length := by simpa using hn
      have Hforall : env.IsDefEq U Γ₁
          (.forallE domain₁ body₁) (.forallE domain₂ body₂)
          (.sort (.imax domainLevel bodyLevel)) :=
        .forallEDF Hdomain Hbody
      rcases ih Hctx hn' Hforall with ⟨resultLevel, Hclosed⟩
      refine ⟨resultLevel, ?_⟩
      simpa [VExpr.wrapForalls, List.take_succ_cons,
        List.reverse_cons, VExpr.wrapForalls_append] using Hclosed

/-- A converted installed telescope can be consumed by independently typed
closed arguments once its context is identified with `liftClosedDomains`.
Closing the context conversion around the retained residual turns it into a
whole-type equality; the generic closed-domain spine then performs every
dependent substitution. -/
theorem VEnv.HasType.mkApps_of_defeqLiftClosedDomains
    (henv : env.WF) (Hctx : OnCtx ctx (env.IsType uvars))
    (Hfn : env.HasType uvars ctx fn
      (VExpr.wrapForalls installedDomains resultType))
    (Hdomains : VEnv.IsDefEqCtx env uvars []
      (installedDomains.reverse ++ ctx)
      ((VExpr.liftClosedDomains types 0).reverse ++ ctx))
    (Hargs : List.Forall₂
      (env.HasType uvars ctx) args types) :
    ∃ finalType, env.HasType uvars ctx
      (VExpr.mkApps fn args) finalType := by
  have hlength : installedDomains.length = types.length := by
    have hcontexts := Hdomains.length_eq
    simp only [List.length_append, List.length_reverse,
      VExpr.liftClosedDomains_length] at hcontexts
    omega
  have HtelescopeType : env.IsType uvars ctx
      (VExpr.wrapForalls installedDomains resultType) :=
    Hfn.isType henv Hctx
  have Hopened := VEnv.IsType.wrapForalls_inv henv.ordered Hctx
    HtelescopeType
  have HresultType : env.IsType uvars
      (installedDomains.reverse ++ ctx) resultType := Hopened.2
  rcases HresultType with ⟨resultLevel, HresultType⟩
  have Hclosed :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads Hdomains
      installedDomains.length (by simp) HresultType
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  have Hwhole : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls installedDomains resultType)
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
        resultType) := by
    refine ⟨.sort closedLevel, ?_⟩
    simpa [hlength] using Hclosed
  have HfnCanonical : env.HasType uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
        resultType) :=
    Hfn.defeqU_r henv Hctx Hwhole
  rcases VEnv.TypedApplicationSpine.liftClosedDomains
      henv.ordered HfnCanonical Hargs with ⟨finalType, Hspine⟩
  exact ⟨finalType, Hspine.hasType⟩

/-- Exact-result form of `mkApps_of_defeqLiftClosedDomains`.  Context
conversion changes the telescope domains but retains the installed residual;
the resulting application therefore has the explicit type obtained by
consuming that converted telescope with the supplied closed arguments. -/
theorem VEnv.HasType.mkApps_of_defeqLiftClosedDomains_exact
    (henv : env.WF) (Hctx : OnCtx ctx (env.IsType uvars))
    (Hfn : env.HasType uvars ctx fn
      (VExpr.wrapForalls installedDomains resultType))
    (Hdomains : VEnv.IsDefEqCtx env uvars []
      (installedDomains.reverse ++ ctx)
      ((VExpr.liftClosedDomains types 0).reverse ++ ctx))
    (Hargs : List.Forall₂
      (env.HasType uvars ctx) args types) :
    env.HasType uvars ctx (VExpr.mkApps fn args)
      (VExpr.applyForallType
        (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) resultType)
        args) := by
  have hlength : installedDomains.length = types.length := by
    have hcontexts := Hdomains.length_eq
    simp only [List.length_append, List.length_reverse,
      VExpr.liftClosedDomains_length] at hcontexts
    omega
  have HtelescopeType : env.IsType uvars ctx
      (VExpr.wrapForalls installedDomains resultType) :=
    Hfn.isType henv Hctx
  have Hopened := VEnv.IsType.wrapForalls_inv henv.ordered Hctx
    HtelescopeType
  have HresultType : env.IsType uvars
      (installedDomains.reverse ++ ctx) resultType := Hopened.2
  rcases HresultType with ⟨resultLevel, HresultType⟩
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads Hdomains
      installedDomains.length (by simp) HresultType with
    ⟨closedLevel, Hclosed⟩
  have Hwhole : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls installedDomains resultType)
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
        resultType) := by
    refine ⟨.sort closedLevel, ?_⟩
    simpa [hlength] using Hclosed
  have HfnCanonical : env.HasType uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
        resultType) :=
    Hfn.defeqU_r henv Hctx Hwhole
  rcases VEnv.TypedApplicationSpine.liftClosedDomains
      henv.ordered HfnCanonical Hargs with ⟨finalType, Hspine⟩
  rw [← Hspine.result_eq_applyForallType]
  exact Hspine.hasType

/-- Select one corresponding declaration from a complete context
conversion.  The selected types are compared in the older left-hand suffix,
which is the context in which that declaration was originally formed. -/
theorem VEnv.IsDefEqCtx.getElem
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (hi : i < Γ₁.length) :
    ∃ u, env.IsDefEq U (Γ₁.drop (i + 1)) Γ₁[i]
      (Γ₂[i]'(H.length_eq ▸ hi)) (.sort u) := by
  induction H generalizing i with
  | zero => simp at hi
  | @succ Γ₁ Γ₂ A₁ A₂ u H hhead ih =>
    cases i with
    | zero =>
      exact ⟨u, by simpa using hhead⟩
    | succ i =>
      have hi' : i < Γ₁.length := by simpa using hi
      simpa only [List.length_cons, List.getElem_cons_succ,
        List.drop_succ_cons, Nat.succ_eq_add_one] using ih hi'

/-- Right-context form of `IsDefEqCtx.getElem`.  This is convenient when the
consumer has already moved into the converted telescope. -/
theorem VEnv.IsDefEqCtx.getElemRight
    (henv : VEnv.Ordered env)
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (hi : i < Γ₁.length) :
    ∃ u, env.IsDefEq U (Γ₂.drop (i + 1)) Γ₁[i]
      (Γ₂[i]'(H.length_eq ▸ hi)) (.sort u) := by
  induction H generalizing i with
  | zero => simp at hi
  | @succ Γ₁ Γ₂ A₁ A₂ u H hhead ih =>
    cases i with
    | zero =>
      exact ⟨u, by simpa using hhead.defeqDFC henv H⟩
    | succ i =>
      have hi' : i < Γ₁.length := by simpa using hi
      simpa only [List.length_cons, List.getElem_cons_succ,
        List.drop_succ_cons, Nat.succ_eq_add_one] using ih hi'

/-- Select a declaration by its chronological telescope position when the
context is represented as a reversed recent prefix followed by an older
base.  The resulting equality lives over exactly the preceding declarations
and the corresponding left base.  This is the indexing form used by the
minor-hypothesis application fold. -/
theorem VEnv.IsDefEqCtx.getElemAppendReverse
    {domains₁ domains₂ base₁ base₂ : List VExpr}
    (H : VEnv.IsDefEqCtx env U []
      (domains₁.reverse ++ base₁) (domains₂.reverse ++ base₂))
    (hi : i < domains₁.length)
    (hlength : domains₁.length = domains₂.length) :
    ∃ u, env.IsDefEq U ((domains₁.take i).reverse ++ base₁)
      domains₁[i] (domains₂[i]'(hlength ▸ hi)) (.sort u) := by
  let j := domains₁.length - 1 - i
  have hj : j < (domains₁.reverse ++ base₁).length := by
    simp only [j, List.length_append, List.length_reverse]
    omega
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.getElem H hj with
    ⟨u, Hentry⟩
  have hjDomains : j < domains₁.reverse.length := by
    simp only [List.length_reverse, j]
    omega
  have hrightLength :
      (domains₁.reverse ++ base₁).length =
        (domains₂.reverse ++ base₂).length := H.length_eq
  have hjRight : j < domains₂.reverse.length := by
    simp only [List.length_reverse, j, hlength]
    omega
  have hdropLeft :
      (domains₁.reverse ++ base₁).drop (j + 1) =
        (domains₁.take i).reverse ++ base₁ := by
    rw [List.drop_append_of_le_length (by
      simp only [List.length_reverse, j]
      omega)]
    simp only [List.drop_reverse]
    have hcount : domains₁.length - (j + 1) = i := by
      dsimp only [j]
      omega
    rw [hcount]
  have hleftGet :
      (domains₁.reverse ++ base₁)[j] = domains₁[i] := by
    rw [List.getElem_append_left hjDomains, List.getElem_reverse]
    congr 1
    omega
  have hrightGet :
      (domains₂.reverse ++ base₂)[j]'(hrightLength ▸ hj) =
        domains₂[i]'(hlength ▸ hi) := by
    rw [List.getElem_append_left hjRight, List.getElem_reverse]
    congr 1
    omega
  rw [hdropLeft, hleftGet, hrightGet] at Hentry
  exact ⟨u, Hentry⟩

/-- Right-base counterpart of `getElemAppendReverse`.  It transports the
selected domain equality into the converted telescope prefix, which is the
ambient context in which the canonical recursive-result argument is typed. -/
theorem VEnv.IsDefEqCtx.getElemAppendReverseRight
    {domains₁ domains₂ base₁ base₂ : List VExpr}
    (henv : VEnv.Ordered env)
    (H : VEnv.IsDefEqCtx env U []
      (domains₁.reverse ++ base₁) (domains₂.reverse ++ base₂))
    (hi : i < domains₁.length)
    (hlength : domains₁.length = domains₂.length) :
    ∃ u, env.IsDefEq U ((domains₂.take i).reverse ++ base₂)
      domains₁[i] (domains₂[i]'(hlength ▸ hi)) (.sort u) := by
  let j := domains₁.length - 1 - i
  have hj : j < (domains₁.reverse ++ base₁).length := by
    simp only [j, List.length_append, List.length_reverse]
    omega
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.getElemRight henv H hj with
    ⟨u, Hentry⟩
  have hrightLength :
      (domains₁.reverse ++ base₁).length =
        (domains₂.reverse ++ base₂).length := H.length_eq
  have hjRight : j < domains₂.reverse.length := by
    simp only [List.length_reverse, j, hlength]
    omega
  have hdropRight :
      (domains₂.reverse ++ base₂).drop (j + 1) =
        (domains₂.take i).reverse ++ base₂ := by
    rw [List.drop_append_of_le_length (by
      simp only [List.length_reverse, j, hlength]
      omega)]
    simp only [List.drop_reverse]
    have hcount : domains₂.length - (j + 1) = i := by
      dsimp only [j]
      omega
    rw [hcount]
  have hleftGet :
      (domains₁.reverse ++ base₁)[j] = domains₁[i] := by
    have hjDomains : j < domains₁.reverse.length := by
      simp only [List.length_reverse, j]
      omega
    rw [List.getElem_append_left hjDomains, List.getElem_reverse]
    congr 1
    omega
  have hrightGet :
      (domains₂.reverse ++ base₂)[j]'(hrightLength ▸ hj) =
        domains₂[i]'(hlength ▸ hi) := by
    rw [List.getElem_append_left hjRight, List.getElem_reverse]
    congr 1
    omega
  rw [hdropRight, hleftGet, hrightGet] at Hentry
  exact ⟨u, Hentry⟩

/-- Pointwise form of `ParamsDefEq`.  Parameter `i` is compared with the
corresponding family-local parameter in precisely the context of the earlier
parameters, matching the order in which cached headers are replayed. -/
theorem VInductDecl.ParamsDefEq.getElem
    {decl : VInductDecl} {env : VEnv} {params ownParams : List VExpr}
    {i : Nat}
    (H : decl.ParamsDefEq env params ownParams)
    (hi : i < params.length) :
    ∃ u, env.IsDefEq decl.uvars (params.take i).reverse
      params[i] (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using H.length_eq
        omega)) (.sort u) := by
  have hlen : params.length = ownParams.length := by
    simpa using H.length_eq
  have hrev : params.length - 1 - i < params.reverse.length := by
    simp
    omega
  have hentry := VEnv.IsDefEqCtx.getElem H hrev
  have htake :
      params.length - (params.length - (1 + i) + 1) = i := by omega
  have hindex :
      params.length - (1 + (params.length - (1 + i))) = i := by omega
  simpa [List.getElem_reverse, List.drop_reverse, hlen.symm, Nat.sub_sub,
    htake, hindex] using hentry

/-- Family-local-context form of `ParamsDefEq.getElem`. -/
theorem VInductDecl.ParamsDefEq.getElemRight
    {decl : VInductDecl} {env : VEnv} {params ownParams : List VExpr}
    {i : Nat}
    (henv : VEnv.Ordered env)
    (H : decl.ParamsDefEq env params ownParams)
    (hi : i < params.length) :
    ∃ u, env.IsDefEq decl.uvars (ownParams.take i).reverse
      params[i] (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using H.length_eq
        omega)) (.sort u) := by
  have hlen : params.length = ownParams.length := by
    simpa using H.length_eq
  have hrev : params.length - 1 - i < params.reverse.length := by
    simp
    omega
  have hentry := VEnv.IsDefEqCtx.getElemRight henv H hrev
  have htake :
      params.length - (params.length - (1 + i) + 1) = i := by omega
  have hindex :
      params.length - (1 + (params.length - (1 + i))) = i := by omega
  simpa [List.getElem_reverse, List.drop_reverse, hlen.symm, Nat.sub_sub,
    htake, hindex] using hentry

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

theorem TrInductDeclSkeletonHeaders.types_length
    (H : TrInductDeclSkeletonHeaders env lparams nparams types isUnsafe decl
      envTypes) :
    types.length = decl.types.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.types

theorem TrInductDeclSkeletonHeaders.typeAt
    (H : TrInductDeclSkeletonHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    TrInductiveTypeSkeletonHeaders env envTypes lparams
      types[i] decl.types[i] :=
  Lean4Lean.VerifyInductive.List.Forall₂.getElem H.types i hsource htarget

theorem TrInductDeclSkeletonHeaders.typeNameAt
    (H : TrInductDeclSkeletonHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    types[i].name = decl.types[i].name :=
  (Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.typeAt
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
    ∃ envTypes, env.addConstVals decl.typeConstants = some envTypes ∧
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

/-- Materialize the original source skeleton with the metadata prefix of an
expanded nested-lowering declaration, simultaneously obtaining the ordinary
source translation and the arity-alignment certificate consumed by restored
recursor verification. -/
theorem TrInductDeclSkeletonCore.materializeExpandedPrefix
    (H : TrInductDeclSkeletonCore env lparams nparams types isUnsafe skeleton
      envTypes envCtors)
    (expanded : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length) :
    ∃ source,
      TrInductDeclCore env lparams nparams types isUnsafe source
        envTypes envCtors ∧
      MaterializedInductivePrefix source expanded := by
  rcases VInductDeclSkeleton.materializeExpandedPrefix skeleton expanded hle with
    ⟨source, Hmaterialize, Hprefix⟩
  exact ⟨source,
    Lean4Lean.VerifyInductive.TrInductDeclSkeletonCore.materialized
      H Hmaterialize,
    Hprefix⟩

theorem TrInductDeclSkeleton.materializeExpandedPrefix
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe skeleton)
    (expanded : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length) :
    ∃ source,
      TrInductDecl env lparams nparams types isUnsafe source ∧
      MaterializedInductivePrefix source expanded := by
  rcases VInductDeclSkeleton.materializeExpandedPrefix skeleton expanded hle with
    ⟨source, Hmaterialize, Hprefix⟩
  exact ⟨source,
    Lean4Lean.VerifyInductive.TrInductDeclSkeleton.materialized
      H Hmaterialize,
    Hprefix⟩

/-- Materialization preserves the header-only translation while filling the
semantic arity metadata recovered by the executable header checker. -/
theorem TrInductDeclSkeletonHeaders.materialized
    (H : TrInductDeclSkeletonHeaders env lparams nparams types isUnsafe
      skeleton envTypes)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    TrInductDeclHeaders env lparams nparams types isUnsafe decl envTypes := by
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have herase := VInductDeclSkeleton.materialize_toSkeleton Hmaterialize
  have htypeConstants : decl.typeConstants = skeleton.typeConstants := by
    rw [← VInductDecl.toSkeleton_typeConstants decl, herase]
  refine {
    uvars := hfields.1.trans H.uvars
    nparams := hfields.2.1.trans H.nparams
    isUnsafe := hfields.2.2.1.trans H.isUnsafe
    typesAdded := by simpa [htypeConstants] using H.typesAdded
    types := ?_ }
  have hlength : types.length = decl.types.length := by
    calc
      types.length = skeleton.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length H
      _ = decl.types.length := hfields.2.2.2.symm
  apply List.forall₂_of_getElem hlength
  intro i hsourceIdx htargetIdx
  have hskeletonIdx : i < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.types_length H]
    exact hsourceIdx
  have htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclSkeletonHeaders.typeAt H i
      hsourceIdx hskeletonIdx
  rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize
      hskeletonIdx with ⟨data, hdata, htarget⟩
  have htarget' : decl.types[i] =
      skeleton.types[i].toVInductiveType data.1 data.2 := by
    simpa [List.getElem?_eq_getElem htargetIdx] using htarget
  rw [htarget']
  exact ⟨htranslated.header, htranslated.ctors⟩

theorem TrInductDecl.types_length
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    types.length = decl.types.length := by
  rcases H with ⟨_, _, _, _, _, _, _, _, htypes⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes

theorem VEnv.addConstVals_append
    {env middle out : VEnv} {xs ys : List VConstVal}
    (hxs : env.addConstVals xs = some middle)
    (hys : middle.addConstVals ys = some out) :
    env.addConstVals (xs ++ ys) = some out := by
  induction xs generalizing env with
  | nil =>
    simp [VEnv.addConstVals] at hxs
    subst middle
    exact hys
  | cons x xs ih =>
    simp only [List.cons_append, VEnv.addConstVals] at hxs ⊢
    cases hnext : env.addConst x.name x.toVConstant with
    | none => simp [hnext] at hxs
    | some next =>
      rw [hnext] at hxs
      simpa [hnext] using ih (by simpa using hxs)

theorem VEnv.addConstVals_append_inv
    {env out : VEnv} {xs ys : List VConstVal}
    (H : env.addConstVals (xs ++ ys) = some out) :
    ∃ middle, env.addConstVals xs = some middle ∧
      middle.addConstVals ys = some out := by
  induction xs generalizing env with
  | nil =>
    exact ⟨env, by simp [VEnv.addConstVals], by simpa [VEnv.addConstVals] using H⟩
  | cons x xs ih =>
    simp only [List.cons_append, VEnv.addConstVals] at H
    cases hnext : env.addConst x.name x.toVConstant with
    | none => simp [hnext] at H
    | some next =>
      rw [hnext] at H
      rcases ih H with ⟨middle, hprefix, hsuffix⟩
      exact ⟨middle, by simp [VEnv.addConstVals, hnext, hprefix], hsuffix⟩

/-- Successful left-to-right abstract installation implies both freshness in
the input environment and pairwise distinctness of all installed names. -/
theorem VEnv.addConstVals_names_fresh
    {env out : VEnv} {constants : List VConstVal}
    (H : env.addConstVals constants = some out) :
    (constants.map (·.name)).Nodup ∧
      ∀ ci ∈ constants, env.constants ci.name = none := by
  induction constants generalizing env with
  | nil => simp
  | cons ci constants ih =>
    simp only [VEnv.addConstVals] at H
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [hadd] at H
    | some next =>
      rw [hadd] at H
      rcases ih H with ⟨htail, hfresh⟩
      have hinstalled : next.constants ci.name = some ci.toVConstant :=
        VEnv.addConst_self hadd
      have hhead : ci.name ∉ constants.map (·.name) := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨later, hlater, hname⟩
        have habsent := hfresh later hlater
        rw [hname, hinstalled] at habsent
        contradiction
      refine ⟨List.nodup_cons.mpr ⟨hhead, htail⟩, ?_⟩
      intro later hlater
      simp only [List.mem_cons] at hlater
      rcases hlater with rfl | hlater
      · unfold VEnv.addConst at hadd
        split at hadd <;> cases hadd
        assumption
      · have habsent := hfresh later hlater
        have hne : ci.name ≠ later.name := by
          intro heq
          apply hhead
          exact List.mem_map.mpr ⟨later, hlater, heq.symm⟩
        rw [VEnv.addConst_constants_of_ne hadd hne] at habsent
        exact habsent

theorem VEnv.addConstVals_names_nodup
    {env out : VEnv} {constants : List VConstVal}
    (H : env.addConstVals constants = some out) :
    (constants.map (·.name)).Nodup :=
  (VEnv.addConstVals_names_fresh H).1

/-- Two fresh abstract constants with distinct names may be installed in
either order, producing the same functional environment. -/
theorem VEnv.addConstVals_swap
    {env out : VEnv} {a b : VConstVal}
    (hne : a.name ≠ b.name)
    (H : env.addConstVals [a, b] = some out) :
    env.addConstVals [b, a] = some out := by
  have hfresh := VEnv.addConstVals_names_fresh H |>.2
  have haFresh := hfresh a (by simp)
  have hbFresh := hfresh b (by simp)
  simp [VEnv.addConstVals, VEnv.addConst, haFresh, hbFresh, hne, hne.symm] at H ⊢
  rw [← H]
  congr 1
  funext name
  by_cases haName : a.name = name <;>
    by_cases hbName : b.name = name <;> simp_all

/-- Installing a list of fresh abstract constants is invariant under
permutation: only the resulting finite map matters, not insertion order. -/
theorem VEnv.addConstVals_perm
    {env out : VEnv} {constants constants' : List VConstVal}
    (Hperm : constants ~ constants')
    (H : env.addConstVals constants = some out) :
    env.addConstVals constants' = some out := by
  induction Hperm generalizing env out with
  | nil => exact H
  | @cons ci constants constants' _ ih =>
    simp only [VEnv.addConstVals] at H ⊢
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [hadd] at H
    | some next =>
      rw [hadd] at H
      simpa using ih H
  | @swap a b constants =>
    change env.addConstVals ([b, a] ++ constants) = some out at H
    rcases VEnv.addConstVals_append_inv H with
      ⟨middle, hprefix, hsuffix⟩
    have hnodup := VEnv.addConstVals_names_nodup hprefix
    have hne : b.name ≠ a.name := by
      simpa using hnodup
    change env.addConstVals ([a, b] ++ constants) = some out
    exact VEnv.addConstVals_append
      (VEnv.addConstVals_swap hne hprefix) hsuffix
  | trans _ _ ih₁ ih₂ =>
    exact ih₂ (ih₁ H)

/-- Recover the canonical dependency-ordered block installation from a
successful installation of the same constants in any restoration order. -/
theorem VInductBlock.install_of_permutedConstants
    {env out : VEnv} {block : VInductBlock}
    {constants : List VConstVal}
    (Hperm : block.types ++ block.ctors ++ block.recursors ~ constants)
    (H : env.addConstVals constants = some out) :
    block.install env = some (out.addDefEqRules block.rules) := by
  have hcanonical : env.addConstVals
      (block.types ++ block.ctors ++ block.recursors) = some out :=
    VEnv.addConstVals_perm Hperm.symm H
  rcases VEnv.addConstVals_append_inv (xs := block.types)
      (ys := block.ctors ++ block.recursors) (by
        simpa only [List.append_assoc] using hcanonical) with
    ⟨envTypes, htypes, htail⟩
  rcases VEnv.addConstVals_append_inv (xs := block.ctors)
      (ys := block.recursors) htail with
    ⟨envCtors, hctors, hrecursors⟩
  simp [VInductBlock.install, htypes, hctors, hrecursors]

/-- Semantic certificate for a block whose constants were produced in
restoration order.  Typing is stated at the canonical dependency stages,
while freshness/installation may be witnessed by any permutation of those
constants. -/
structure RestoredBlockCertificate (env : VEnv)
    (block : VInductBlock) where
  constants : List VConstVal
  outVEnv : VEnv
  order : block.types ++ block.ctors ++ block.recursors ~ constants
  installed : env.addConstVals constants = some outVEnv
  typesWF : ∀ ci ∈ block.types, ci.toVConstant.WF env
  ctorsWF : ∀ envTypes,
    env.addConstVals block.types = some envTypes →
    ∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes
  recursorsWF : ∀ envTypes envCtors,
    env.addConstVals block.types = some envTypes →
    envTypes.addConstVals block.ctors = some envCtors →
    ∀ ci ∈ block.recursors, ci.toVConstant.WF envCtors
  rulesWF : ∀ df ∈ block.rules, df.WF outVEnv

theorem RestoredBlockCertificate.canonicalStages
    (H : RestoredBlockCertificate env block) :
    ∃ envTypes envCtors,
      env.addConstVals block.types = some envTypes ∧
      envTypes.addConstVals block.ctors = some envCtors ∧
      envCtors.addConstVals block.recursors = some H.outVEnv := by
  have hcanonical : env.addConstVals
      (block.types ++ block.ctors ++ block.recursors) = some H.outVEnv :=
    VEnv.addConstVals_perm H.order.symm H.installed
  rcases VEnv.addConstVals_append_inv (xs := block.types)
      (ys := block.ctors ++ block.recursors) (by
        simpa only [List.append_assoc] using hcanonical) with
    ⟨envTypes, htypes, htail⟩
  rcases VEnv.addConstVals_append_inv (xs := block.ctors)
      (ys := block.recursors) htail with
    ⟨envCtors, hctors, hrecursors⟩
  exact ⟨envTypes, envCtors, htypes, hctors, hrecursors⟩

/-- Restoration-order installation plus canonical stage typing discharges
the independent compiled-block well-formedness judgment. -/
theorem RestoredBlockCertificate.wf
    (H : RestoredBlockCertificate env block) : block.WF env := by
  rcases H.canonicalStages with
    ⟨envTypes, envCtors, htypes, hctors, hrecursors⟩
  exact ⟨envTypes, envCtors, H.outVEnv, htypes, hctors, hrecursors,
    H.typesWF, H.ctorsWF envTypes htypes,
    H.recursorsWF envTypes envCtors htypes hctors, H.rulesWF⟩

theorem RestoredBlockCertificate.install
    (H : RestoredBlockCertificate env block) :
    block.install env = some (H.outVEnv.addDefEqRules block.rules) :=
  VInductBlock.install_of_permutedConstants H.order H.installed

/-- Final abstract inductive-extension assembly specialized to a restored
block.  The declaration and compilation judgments remain independent inputs;
the restoration certificate supplies block well-formedness and installation. -/
theorem RestoredBlockCertificate.addInduct
    (H : RestoredBlockCertificate env block)
    (Hdecl : decl.WF env)
    (Hcompile : decl.CompilesTo env block) :
    VEnv.AddInduct env decl (H.outVEnv.addDefEqRules block.rules) :=
  .intro Hdecl Hcompile H.wf H.install

theorem VEnv.addConstVals_get
    {env out : VEnv} {constants : List VConstVal}
    (H : env.addConstVals constants = some out)
    (hci : ci ∈ constants) :
    out.constants ci.name = some ci.toVConstant := by
  induction constants generalizing env with
  | nil => simp at hci
  | cons head tail ih =>
    simp only [VEnv.addConstVals] at H
    cases hadd : env.addConst head.name head.toVConstant with
    | none => simp [hadd] at H
    | some next =>
      rw [hadd] at H
      rcases List.mem_cons.mp hci with rfl | htail
      · exact (VEnv.addConstVals_le H).constants (VEnv.addConst_self hadd)
      · exact ih H htail

theorem TrInductDeclCore.sourceNames_nodup
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    decl.sourceNames.Nodup := by
  have hadd : env.addConstVals
      (decl.typeConstants ++ decl.constructorConstants) = some envCtors :=
    VEnv.addConstVals_append H.typesAdded H.ctorsAdded
  simpa [VInductDecl.sourceNames, List.map_append] using
    VEnv.addConstVals_names_nodup hadd

/-- The two executable checking phases jointly recover the pointwise core
translation, without assuming aggregate source well-formedness. -/
theorem TrInductDeclCore.ofPhases
    (Hheaders : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (Hctors : TrInductDeclConstructors envTypes lparams types decl envCtors) :
    TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors := by
  have combine : ∀ {sources targets},
      List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
        sources targets →
      List.Forall₂
        (fun source target => List.Forall₂
          (fun ctor ctor' =>
            TrSourceConst envTypes lparams ctor.name ctor.type ctor')
          source.ctors target.ctors)
        sources targets →
      List.Forall₂ (TrInductiveType env envTypes lparams)
        sources targets := by
    intro sources targets hheaders hctors
    induction hheaders with
    | nil =>
      cases hctors
      exact .nil
    | cons hheader _ ih =>
      cases hctors with
      | cons hctor hctors =>
        exact .cons ⟨hheader.header, hctor⟩ (ih hctors)
  exact {
    uvars := Hheaders.uvars
    nparams := Hheaders.nparams
    isUnsafe := Hheaders.isUnsafe
    typesAdded := Hheaders.typesAdded
    ctorsAdded := Hctors.ctorsAdded
    types := combine Hheaders.types Hctors.types }

/-- Pointwise original-source translations already contain all typing and
universe facts required by `SourceWF`. Thus the aggregate source judgment
adds only nonemptiness and global name uniqueness. Nonemptiness comes from
the lowering entry point; uniqueness follows from the staged `addConstVals`
equalities retained by the core translation. -/
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

theorem TrInductDeclCore.sourceWF_ofNonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ []) :
    decl.SourceWF env :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF H hnonempty
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup H)

theorem TrInductDeclCore.toTrInductDeclOfNonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ []) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDecl H hnonempty
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup H)

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
    ∃ envTypes, env.addConstVals decl.typeConstants = some envTypes ∧
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

theorem TrInductiveType.headers
    (H : TrInductiveType env envTypes lparams type target) :
    TrInductiveTypeHeaders env envTypes lparams type target where
  header := H.header
  ctors := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => h.raw) H.ctors

theorem TrInductiveTypeHeaders.ctors_length
    (H : TrInductiveTypeHeaders env envTypes lparams type target) :
    type.ctors.length = target.ctors.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.ctors

theorem TrInductiveTypeHeaders.ctorAt
    (H : TrInductiveTypeHeaders env envTypes lparams type target)
    (i : Nat) (hsource : i < type.ctors.length)
    (htarget : i < target.ctors.length) :
    TrSourceConstRaw envTypes lparams type.ctors[i].name type.ctors[i].type
      target.ctors[i] :=
  Lean4Lean.VerifyInductive.List.Forall₂.getElem H.ctors i hsource htarget

theorem TrSourceConstRaw.checked
    (H : TrSourceConstRaw env lparams name type ci')
    (hwf : ci'.toVConstant.WF env) :
    TrSourceConst env lparams name type ci' :=
  ⟨H.uvars, H.name, H.type, hwf⟩

/-- Constructor checking supplies exactly the typing evidence omitted from
the header phase's raw constructor translations. -/
theorem CheckedConstructorCertificate.translated
    {types : List InductiveType}
    (H : CheckedConstructorCertificate sourceEnv decl envTypes params)
    (Hdecl : TrInductDeclHeaders sourceEnv lparams nparams types isUnsafe
      decl envTypes) :
    List.Forall₂
      (fun (source : InductiveType) (target : VInductiveType) => List.Forall₂
        (fun (ctor : Constructor) (ctor' : VConstVal) =>
          TrSourceConst envTypes lparams ctor.name ctor.type ctor')
        source.ctors target.ctors)
      types decl.types := by
  have hlength : types.length = decl.types.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hdecl.types
  apply List.forall₂_of_getElem hlength
  intro i hsource htarget
  have Htype := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hdecl.types i hsource htarget
  have hctorLength : types[i].ctors.length = decl.types[i].ctors.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htype.ctors
  apply List.forall₂_of_getElem hctorLength
  intro j hsourceCtor htargetCtor
  have Hctor := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Htype.ctors j hsourceCtor htargetCtor
  apply Lean4Lean.VerifyInductive.TrSourceConstRaw.checked Hctor
  have hwf := H.types decl.types[i].ctors[j] (by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[i], List.getElem_mem htarget,
      List.getElem_mem htargetCtor⟩)
  have huvars : decl.types[i].ctors[j].uvars = decl.uvars :=
    Hctor.uvars.trans Hdecl.uvars.symm
  simpa [VConstant.WF, huvars] using hwf

theorem TrInductDeclCore.headers
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    TrInductDeclHeaders env lparams nparams types isUnsafe decl envTypes where
  uvars := H.uvars
  nparams := H.nparams
  isUnsafe := H.isUnsafe
  typesAdded := H.typesAdded
  types := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => TrInductiveType.headers h) H.types

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

theorem TrSourceConst.ctorInfo
    (H : TrSourceConst env lparams name type ci')
    (hlevelParams : info.levelParams = lparams)
    (hname : info.name = name)
    (htype : info.type = type)
    (hvisible : safety ≤
      (if info.isUnsafe then DefinitionSafety.unsafe else .safe)) :
    TrConstVal safety env (.ctorInfo info) ci' := by
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
      (TrInductiveTypeHeaders env envTypes lparams)
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
      env.addConstVals decl.typeConstants = some envTypes ∧
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
    ∃ envTypes, env.addConstVals decl.typeConstants = some envTypes ∧
      TrOwnedConstructor env envTypes lparams
        (Lean4Lean.VerifyInductive.ownedConstructors types)[i]
        decl.ownedConstructors[i] := by
  rcases Lean4Lean.VerifyInductive.TrInductDecl.ownedConstructors H with
    ⟨envTypes, htypes, hctors⟩
  exact ⟨envTypes, htypes,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem hctors i hsource htarget⟩

end VerifyInductive
end Lean4Lean
