import Lean4Lean.Verify.Typing.ProjectionProduction
import Lean4Lean.Verify.Environment.Lemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A projection name is ready at a checker boundary when it resolves to one
exact visible production inductive payload with installed abstract
provenance.

This is intentionally pointwise.  A staged inductive environment may contain
the active family's header and constructors before its eliminators exist, so
a global provenance claim about the whole current constant map would be
false.  Readiness therefore retains the exact visible `.casesOn` declaration
and its abstract translation in addition to family provenance.
-/
structure ProjectionNameReadinessData
    (safety : DefinitionSafety) (constants : ConstMap) (env : VEnv)
    (name : Name) where
  familyInfo : InductiveVal
  familyLookup :
    constants.find? name = some (.inductInfo familyInfo)
  familyVisible : safety ≤ (ConstantInfo.inductInfo familyInfo).safety
  family : Nonempty
    (ProductionProjectionFamily safety constants env name familyInfo)
  eliminatorInfo : ConstantInfo
  eliminatorLookup :
    constants.find? (mkCasesOnName name) = some eliminatorInfo
  eliminatorVisible : safety ≤ eliminatorInfo.safety
  eliminator : VConstant
  eliminatorAbstractLookup :
    env.constants (mkCasesOnName name) = some eliminator
  eliminatorTranslation : TrConstant safety env eliminatorInfo eliminator

def ProjectionNameReady
    (safety : DefinitionSafety) (constants : ConstMap) (env : VEnv)
    (name : Name) : Prop :=
  Nonempty (ProjectionNameReadinessData safety constants env name)

/-- Every primitive projection node in an executable expression is ready in
the exact production/abstract environment pair used to translate it.  This
is the per-expression invariant required by staged checking: source
constructor checking establishes it before active constructor metadata is
inserted, and generated terms preserve it structurally.

It is not a caller compatibility callback.  The only non-structural leaf is
`ProjectionNameReady`, whose witness combines persistent installed-inductive
provenance with the ordinary checking-environment translation of `.casesOn`.
-/
inductive ProjectionsReady
    (safety : DefinitionSafety) (constants : ConstMap) (env : VEnv) :
    Expr → Prop
  | bvar : ProjectionsReady safety constants env (.bvar index)
  | fvar (fvarId : FVarId) :
      ProjectionsReady safety constants env (.fvar fvarId)
  | sort : ProjectionsReady safety constants env (.sort level)
  | const : ProjectionsReady safety constants env (.const name levels)
  | mvar (mvarId : MVarId) :
      ProjectionsReady safety constants env (.mvar mvarId)
  | app :
      ProjectionsReady safety constants env fn →
      ProjectionsReady safety constants env arg →
      ProjectionsReady safety constants env (.app fn arg)
  | lam :
      ProjectionsReady safety constants env domain →
      ProjectionsReady safety constants env body →
      ProjectionsReady safety constants env (.lam binderName domain body bi)
  | forallE :
      ProjectionsReady safety constants env domain →
      ProjectionsReady safety constants env body →
      ProjectionsReady safety constants env
        (.forallE binderName domain body bi)
  | letE :
      ProjectionsReady safety constants env type →
      ProjectionsReady safety constants env value →
      ProjectionsReady safety constants env body →
      ProjectionsReady safety constants env
        (.letE binderName type value body nondep)
  | lit : ProjectionsReady safety constants env (.lit literal)
  | mdata :
      ProjectionsReady safety constants env body →
      ProjectionsReady safety constants env (.mdata data body)
  | proj :
      ProjectionNameReady safety constants env structName →
      ProjectionsReady safety constants env major →
      ProjectionsReady safety constants env (.proj structName index major)

namespace ProjectionNameReady

/-- Exact metadata retained after the successful family, singleton
constructor, field-bound, and eliminator checks performed by `inferProj`.
Every data field is selected by a production lookup or by installed
provenance; there is no asserted expansion result in this certificate. -/
structure InferenceMetadata
    (safety : DefinitionSafety) (constants : ConstMap) (env : VEnv)
    (name : Name) (index : Nat) where
  familyInfo : InductiveVal
  familyLookup : constants.find? name = some (.inductInfo familyInfo)
  familyVisible : safety ≤ (ConstantInfo.inductInfo familyInfo).safety
  family : ProductionProjectionFamily safety constants env name familyInfo
  sourceOwner : VInductiveType
  sourceOwner_eq : sourceOwner =
    family.decl.types[family.familyIdx]'family.alignment.familyIdx_lt
  sourceOwner_mem : sourceOwner ∈ family.decl.types
  sourceOwner_name : sourceOwner.name = name
  sourceOwnerLookup :
    env.constants name = some sourceOwner.toVConstant
  sourceOwnerTranslation : TrConstant safety env
    (.inductInfo familyInfo) sourceOwner.toVConstant
  constructor : ProductionProjectionConstructor family
  index_lt : index < constructor.alignment.info.numFields
  sourceConstructor : VConstVal
  sourceConstructor_eq : sourceConstructor =
    (family.decl.types[family.familyIdx]'
      family.alignment.familyIdx_lt).ctors[0]'
        constructor.alignment.ctorIdx_lt
  sourceConstructor_mem : sourceConstructor ∈
    (family.decl.types[family.familyIdx]'family.alignment.familyIdx_lt).ctors
  sourceConstructor_name : sourceConstructor.name = constructor.constructorName
  sourceConstructorLookup :
    env.constants constructor.constructorName =
      some sourceConstructor.toVConstant
  sourceConstructorTranslation : TrConstant safety env
    (.ctorInfo constructor.alignment.info) sourceConstructor.toVConstant
  eliminatorInfo : ConstantInfo
  eliminatorLookup :
    constants.find? (mkCasesOnName name) = some eliminatorInfo
  eliminatorVisible : safety ≤ eliminatorInfo.safety
  eliminator : VConstant
  eliminatorAbstractLookup :
    env.constants (mkCasesOnName name) = some eliminator
  eliminatorTranslation : TrConstant safety env eliminatorInfo eliminator

/-- The resolved abstract owner has exactly the resolved constructor.
This is derived from the production singleton branch and the exact indexed
identities retained above; it does not appeal to uniqueness of names. -/
theorem InferenceMetadata.sourceOwnerSingle
    (H : InferenceMetadata safety constants env name index) :
    H.sourceOwner.ctors = [H.sourceConstructor] := by
  have hlength : H.sourceOwner.ctors.length = 1 := by
    rw [H.sourceOwner_eq]
    exact H.constructor.sourceSingle
  have hconstructor : H.sourceConstructor =
      H.sourceOwner.ctors[0]'(by omega) := by
    simpa [H.sourceOwner_eq] using H.sourceConstructor_eq
  cases hctors : H.sourceOwner.ctors with
  | nil => simp [hctors] at hlength
  | cons head tail =>
      cases tail with
      | nil =>
          have : H.sourceConstructor = head := by
            simpa [hctors] using hconstructor
          simp [this]
      | cons next tail => simp [hctors] at hlength

/-- The executable singleton-constructor and field-bound branches refine
pointwise readiness to exact projection-inference metadata. -/
theorem inferenceMetadata
    (H : ProjectionNameReady safety production.constants env name)
    (Hchecking : CheckingEnv safety production env)
    (hfamily : production.find? name = some (.inductInfo familyInfo))
    (hsingle : familyInfo.ctors = [constructorName])
    (hconstructor : production.find? constructorName =
      some (.ctorInfo constructorInfo))
    (hindex : index < constructorInfo.numFields) :
    Nonempty (InferenceMetadata safety production.constants env name index) := by
  have hfamilyMap : production.constants.find? name =
      some (.inductInfo familyInfo) :=
    Hchecking.map_wf.find?'_eq_find? _ ▸ hfamily
  have hconstructorMap : production.constants.find? constructorName =
      some (.ctorInfo constructorInfo) :=
    Hchecking.map_wf.find?'_eq_find? _ ▸ hconstructor
  rcases H with ⟨H⟩
  rw [H.familyLookup] at hfamilyMap
  cases Option.some.inj hfamilyMap
  rcases H.family with ⟨P⟩
  rcases P.constructorOfSingle hsingle with ⟨C⟩
  have hconstructor' : production.constants.find? constructorName =
      some (.ctorInfo C.alignment.info) := by
    simpa [hsingle] using C.alignment.lookup
  rw [hconstructorMap] at hconstructor'
  cases Option.some.inj hconstructor'
  let sourceOwner := P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt
  have hsourceOwnerMem : sourceOwner ∈ P.decl.types :=
    List.getElem_mem P.alignment.familyIdx_lt
  have hsourceOwnerName : sourceOwner.name = name := by
    exact P.alignment.name.symm.trans P.familyNameExact
  have hsourceOwnerLookup : env.constants name =
      some sourceOwner.toVConstant := by
    simpa [hsourceOwnerName] using
      ProjectionMetadata.installedInductCertificate_ownerLookup
        P.installed hsourceOwnerMem
  have hsourceOwnerTranslation : TrConstant safety env
      (.inductInfo H.familyInfo) sourceOwner.toVConstant :=
    (Hchecking.find?_uniq hfamily hsourceOwnerLookup).2
  let sourceConstructor :=
    sourceOwner.ctors[0]'C.alignment.ctorIdx_lt
  have hsourceConstructorMem : sourceConstructor ∈ sourceOwner.ctors :=
    List.getElem_mem C.alignment.ctorIdx_lt
  have hconstructorName : C.constructorName = constructorName := by
    have hsingle' := C.productionSingle
    rw [hsingle] at hsingle'
    have heq : constructorName = C.constructorName := by
      simpa using hsingle'
    exact heq.symm
  have hsourceConstructorName :
      sourceConstructor.name = C.constructorName := by
    have hsourceRuntime : sourceConstructor.name = constructorName := by
      simpa [sourceOwner, sourceConstructor, hsingle] using
        C.alignment.name.symm
    exact hsourceRuntime.trans hconstructorName.symm
  have hsourceLookup : env.constants C.constructorName =
      some sourceConstructor.toVConstant := by
    simpa [hsourceConstructorName] using
      ProjectionMetadata.installedInductCertificate_constructorLookup
        P.installed (List.getElem_mem P.alignment.familyIdx_lt)
          hsourceConstructorMem
  have hsourceRuntimeLookup : env.constants constructorName =
      some sourceConstructor.toVConstant := by
    simpa [hconstructorName] using hsourceLookup
  have hsourceTranslation : TrConstant safety env
      (.ctorInfo C.alignment.info) sourceConstructor.toVConstant :=
    (Hchecking.find?_uniq hconstructor hsourceRuntimeLookup).2
  exact ⟨{
    familyInfo := H.familyInfo
    familyLookup := H.familyLookup
    familyVisible := H.familyVisible
    family := P
    sourceOwner := sourceOwner
    sourceOwner_eq := rfl
    sourceOwner_mem := hsourceOwnerMem
    sourceOwner_name := hsourceOwnerName
    sourceOwnerLookup := hsourceOwnerLookup
    sourceOwnerTranslation := hsourceOwnerTranslation
    constructor := C
    index_lt := hindex
    sourceConstructor := sourceConstructor
    sourceConstructor_eq := rfl
    sourceConstructor_mem := hsourceConstructorMem
    sourceConstructor_name := hsourceConstructorName
    sourceConstructorLookup := hsourceLookup
    sourceConstructorTranslation := hsourceTranslation
    eliminatorInfo := H.eliminatorInfo
    eliminatorLookup := H.eliminatorLookup
    eliminatorVisible := H.eliminatorVisible
    eliminator := H.eliminator
    eliminatorAbstractLookup := H.eliminatorAbstractLookup
    eliminatorTranslation := H.eliminatorTranslation }⟩

/-- Exact resolved projection readiness survives a lockstep environment
extension.  Unlike the false vacuous formulation, the old family lookup is
part of `H`, so a fresh active family can never be mistaken for it. -/
theorem mono
    (H : ProjectionNameReady safety source env name)
    (hproduction : ∀ {currentName info},
      source.find? currentName = some info →
        target.find? currentName = some info)
    (henv : env ≤ env') :
    ProjectionNameReady safety target env' name := by
  rcases H with ⟨H⟩
  rcases H.family with ⟨P⟩
  have hfamily' := hproduction H.familyLookup
  have heliminator' := hproduction H.eliminatorLookup
  refine ⟨{
    familyInfo := H.familyInfo
    familyLookup := hfamily'
    familyVisible := H.familyVisible
    family := ⟨?_⟩
    eliminatorInfo := H.eliminatorInfo
    eliminatorLookup := heliminator'
    eliminatorVisible := H.eliminatorVisible
    eliminator := H.eliminator
    eliminatorAbstractLookup := henv.constants H.eliminatorAbstractLookup
    eliminatorTranslation := H.eliminatorTranslation.mono henv }⟩
  exact {
    decl := P.decl
    familyIdx := P.familyIdx
    alignment := P.alignment.rebase
      (hproduction P.alignment.lookup) hproduction
    familyNameExact := P.familyNameExact
    installed := P.installed.mono henv
    recursor := P.recursor
    recursorName := P.recursorName
    recursorLookup := henv.constants P.recursorLookup
    recursorShape := P.recursorShape }

end ProjectionNameReady

namespace ProjectionsReady

theorem projectionName
    (H : ProjectionsReady safety constants env
      (.proj structName index major)) :
    ProjectionNameReady safety constants env structName := by
  cases H with
  | proj hname _ => exact hname

theorem projectionMajor
    (H : ProjectionsReady safety constants env
      (.proj structName index major)) :
    ProjectionsReady safety constants env major := by
  cases H with
  | proj _ hmajor => exact hmajor

/-- Structural transport once readiness of every name occurring in the
expression has been transported.  Staged callers prove the name case from
their exact source-map preservation trace; there is deliberately no false
global monotonicity theorem for arbitrary newly inserted names. -/
theorem mapNames
    (H : ProjectionsReady safety source env expression)
    (hnames : ∀ {name}, ProjectionNameReady safety source env name →
      ProjectionNameReady safety target env' name) :
    ProjectionsReady safety target env' expression := by
  induction H with
  | bvar => exact .bvar
  | fvar fvarId => exact .fvar fvarId
  | sort => exact .sort
  | const => exact .const
  | mvar mvarId => exact .mvar mvarId
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody
  | letE _ _ _ ihType ihValue ihBody => exact .letE ihType ihValue ihBody
  | lit => exact .lit
  | mdata _ ih => exact .mdata ih
  | @proj structName index major hname _ ih =>
      exact .proj (hnames hname) ih

/-- Per-expression readiness is stable under the exact lockstep extensions
used by staged declaration checking. -/
theorem mono
    (H : ProjectionsReady safety source env expression)
    (hproduction : ∀ {name info},
      source.find? name = some info → target.find? name = some info)
    (henv : env ≤ env') :
    ProjectionsReady safety target env' expression :=
  H.mapNames fun Hname => Hname.mono hproduction henv

/-- Moving de Bruijn variables cannot change a primitive projection's
structure name. -/
theorem liftLooseBVars'
    (H : ProjectionsReady safety constants env expression) (start amount) :
    ProjectionsReady safety constants env
      (expression.liftLooseBVars' start amount) := by
  induction H generalizing start with
  | bvar => simp [Expr.liftLooseBVars'] <;> exact .bvar
  | fvar fvarId => simpa [Expr.liftLooseBVars'] using
      (ProjectionsReady.fvar (safety := safety) (constants := constants)
        (env := env) fvarId)
  | sort => exact .sort
  | const => exact .const
  | mvar mvarId => simpa [Expr.liftLooseBVars'] using
      (ProjectionsReady.mvar (safety := safety) (constants := constants)
        (env := env) mvarId)
  | app _ _ ihFn ihArg =>
      simpa [Expr.liftLooseBVars'] using .app (ihFn start) (ihArg start)
  | lam _ _ ihDomain ihBody =>
      simpa [Expr.liftLooseBVars'] using .lam (ihDomain start)
        (ihBody (start + 1))
  | forallE _ _ ihDomain ihBody =>
      simpa [Expr.liftLooseBVars'] using .forallE (ihDomain start)
        (ihBody (start + 1))
  | letE _ _ _ ihType ihValue ihBody =>
      simpa [Expr.liftLooseBVars'] using .letE (ihType start)
        (ihValue start) (ihBody (start + 1))
  | lit => exact .lit
  | mdata _ ih => simpa [Expr.liftLooseBVars'] using .mdata (ih start)
  | proj hname _ ih =>
      simpa [Expr.liftLooseBVars'] using .proj hname (ih start)

/-- Substituting one expression preserves readiness when both the body and
the substituted expression are ready. -/
theorem instantiate1'
    (H : ProjectionsReady safety constants env expression)
    (Harg : ProjectionsReady safety constants env argument) (k := 0) :
    ProjectionsReady safety constants env
      (Expr.instantiate1' expression argument k) := by
  induction H generalizing k with
  | bvar =>
      simp only [Expr.instantiate1']
      split
      · exact .bvar
      · split
        · exact Harg.liftLooseBVars' 0 k
        · exact .bvar
  | fvar fvarId => simpa [Expr.instantiate1'] using
      (ProjectionsReady.fvar (safety := safety) (constants := constants)
        (env := env) fvarId)
  | sort => exact .sort
  | const => exact .const
  | mvar mvarId => simpa [Expr.instantiate1'] using
      (ProjectionsReady.mvar (safety := safety) (constants := constants)
        (env := env) mvarId)
  | app _ _ ihFn ihArg =>
      simpa [Expr.instantiate1'] using .app (ihFn k) (ihArg k)
  | lam _ _ ihDomain ihBody =>
      simpa [Expr.instantiate1'] using .lam (ihDomain k) (ihBody (k + 1))
  | forallE _ _ ihDomain ihBody =>
      simpa [Expr.instantiate1'] using .forallE (ihDomain k)
        (ihBody (k + 1))
  | letE _ _ _ ihType ihValue ihBody =>
      simpa [Expr.instantiate1'] using .letE (ihType k) (ihValue k)
        (ihBody (k + 1))
  | lit => exact .lit
  | mdata _ ih => simpa [Expr.instantiate1'] using .mdata (ih k)
  | proj hname _ ih =>
      simpa [Expr.instantiate1'] using .proj hname (ih k)

/-- Simultaneous list instantiation is repeated readiness-preserving single
instantiation. -/
theorem instantiateList
    (H : ProjectionsReady safety constants env expression)
    (Hargs : ∀ argument ∈ arguments,
      ProjectionsReady safety constants env argument) (k := 0) :
    ProjectionsReady safety constants env
      (Expr.instantiateList expression arguments k) := by
  induction arguments generalizing expression with
  | nil => simpa [Expr.instantiateList] using H
  | cons argument arguments ih =>
      simp only [Expr.instantiateList]
      apply ih (H.instantiate1' (Hargs argument (by simp)) k)
      intro current hcurrent
      exact Hargs current (by simp [hcurrent])

end ProjectionsReady

/-- Persistent provenance immediately makes every projection name in a
stable environment ready. -/
theorem InstalledInductiveProvenance.projectionNameReady
    (H : InstalledInductiveProvenance safety production.constants env)
    (Hchecking : CheckingEnv safety production env)
    (hfamily : production.constants.find? name =
      some (.inductInfo familyInfo))
    (hvisible : safety ≤ (ConstantInfo.inductInfo familyInfo).safety)
    (heliminator : production.find? (mkCasesOnName name) =
      some eliminatorInfo)
    (heliminatorVisible : safety ≤ eliminatorInfo.safety) :
    ProjectionNameReady safety production.constants env name := by
  rcases Hchecking.find? heliminator heliminatorVisible with
    ⟨eliminator, habstract, htranslation⟩
  exact ⟨{
    familyInfo := familyInfo
    familyLookup := hfamily
    familyVisible := hvisible
    family := InstalledInductiveProvenance.projectionFamily H hfamily hvisible
    eliminatorInfo := eliminatorInfo
    eliminatorLookup :=
      Hchecking.map_wf.find?'_eq_find? _ ▸ heliminator
    eliminatorVisible := heliminatorVisible
    eliminator := eliminator
    eliminatorAbstractLookup := habstract
    eliminatorTranslation := htranslation }⟩

end VerifyInductive

end Lean4Lean
