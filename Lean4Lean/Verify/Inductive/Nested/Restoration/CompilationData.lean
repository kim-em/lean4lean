import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations
import Lean4Lean.Verify.Inductive.Nested.Install.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorShape
import Lean4Lean.Verify.Inductive.Recursor.Signature.Generator
import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Std.List

/-! `CompilationData` for the lowered declaration of a validated nested run.

The expanded declaration is the lowered declaration `E.production.loweredDecl`,
the signature and instance are the consumed generation of its completed
recursor construction, and the block is the canonical restored block of the
final assembly shape.  Every field is proved here except the restoration
correspondence of the constructor types (and of the auxiliary family headers)
and the restored recursor and equation lists, collected in
`NestedCompilationPending`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive


/-! ### List helpers -/

theorem forall₂_append_left_split {R : α → β → Prop}
    {l₁ l₂ : List α} {r : List β} (H : List.Forall₂ R (l₁ ++ l₂) r) :
    List.Forall₂ R l₁ (r.take l₁.length) ∧
      List.Forall₂ R l₂ (r.drop l₁.length) := by
  have h₁ := List.forall₂_take H l₁.length
  have h₂ := Lean4Lean.List.forall₂_drop H l₁.length
  simp only [List.take_left', List.drop_left'] at h₁ h₂
  exact ⟨h₁, h₂⟩

theorem forall₂_of_map_eq {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {r : List β}, l.map f = r.map g →
      List.Forall₂ (fun a b => f a = g b) l r
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq h.2)

theorem forall₂_swap {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r →
      List.Forall₂ (fun b a => R a b) r l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_swap t)

theorem forall₂_join {R : α → β → Prop} {S : γ → β → Prop} :
    ∀ {l : List α} {m : List β} {n : List γ}, List.Forall₂ R l m →
      List.Forall₂ S n m → List.Forall₂ (fun a c => ∃ b, R a b ∧ S c b) l n
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons ⟨_, h, h'⟩ (forall₂_join t t')

/-- Every constructor of the normalized declaration carries the signature's
universe arity. -/
theorem _root_.Lean4Lean.InductiveSignature.declaration_ctor_uvars (s : InductiveSignature) :
    ∀ family ∈ s.declaration.types, ∀ ctor ∈ family.ctors, ctor.uvars = s.uvars := by
  intro family hfamily ctor hctor
  simp only [InductiveSignature.declaration, List.mem_map] at hfamily
  obtain ⟨⟨f, i⟩, _, rfl⟩ := hfamily
  simp only [List.mem_filterMap] at hctor
  obtain ⟨c, _, h⟩ := hctor
  split at h
  · cases h; rfl
  · cases h

/-- Every family of the normalized declaration carries the signature's
universe arity. -/
theorem _root_.Lean4Lean.InductiveSignature.declaration_type_uvars
    (s : InductiveSignature) :
    ∀ family ∈ s.declaration.types, family.uvars = s.uvars := by
  intro family hfamily
  simp only [InductiveSignature.declaration, List.mem_map] at hfamily
  obtain ⟨⟨f, i⟩, _, rfl⟩ := hfamily
  rfl

/-- The completed recursor construction of the lowered declaration. -/
noncomputable def NestedInstalledProduction.loweredConstruction
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv) :
    RecursorConstruction P.constructors.toConstructorCheck :=
  P.production.toRecursorConstruction

/-- The normalized signature of the lowered declaration. -/
noncomputable def NestedInstalledProduction.compilationSignature
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv) :
    InductiveSignature :=
  P.loweredConstruction.generator.signature

/-- The generation instance of the lowered declaration. -/
noncomputable def NestedInstalledProduction.compilationInstance
    {loweredEnv : Environment} (P : NestedInstalledProduction loweredEnv) :
    Instance P.compilationSignature :=
  P.loweredConstruction.generator.generation

/-- The fields of `CompilationData` not yet derived from a validated nested
run.  The source families' names, universes, index counts, result levels and
header telescopes, the auxiliary families' names and universes, and every
source constructor's name and universes are derived; what remains is the restoration
of every normalized constructor type, the remaining header data of the
auxiliary families, and the restored recursor and equation lists. -/
structure NestedCompilationPending (env : VEnv) (decl : VInductDecl)
    (s : InductiveSignature) (g : Instance s)
    (auxiliaries : List ContainerSpecialization) (block : VInductBlock) : Prop where
  /-- Restoration of the constructor types of the source families. -/
  sourceConstructors : ∀ envTypes,
    env.addConstVals decl.typeConstants = some envTypes →
    List.Forall₂ (fun normalized family : VInductiveType =>
        List.Forall₂ (fun normalized ctor : VConstVal =>
          RestoresType (compilationRestoration decl auxiliaries) envTypes decl.uvars
            normalized.type ctor.type)
          normalized.ctors family.ctors)
      (s.declaration.types.take decl.types.length) decl.types
  /-- Header data and constructor restoration of the auxiliary families,
  against the direct specializations of their containers. -/
  auxiliaryFamilies : ∀ envTypes direct,
    env.addConstVals decl.typeConstants = some envTypes →
    auxiliaries.mapM (fun a => a.specializedFamily decl.uvars s.params) = some direct →
    List.Forall₂ (fun normalized family : VInductiveType =>
        normalized.numIndices = family.numIndices ∧
        normalized.resultLevel ≈ family.resultLevel ∧
        (∃ domains body level exprType, level ≈ normalized.resultLevel ∧
          envTypes.IsDefEq decl.uvars [] family.type
            (VExpr.wrapForalls domains body) exprType ∧
          envTypes.IsDefEq decl.uvars domains.reverse body (.sort level)
            (.sort (.succ level))) ∧
        List.Forall₂ (fun normalized ctor : VConstVal =>
          normalized.name = ctor.name ∧ normalized.uvars = ctor.uvars ∧
          RestoresType (compilationRestoration decl auxiliaries) envTypes decl.uvars
            normalized.type ctor.type)
          normalized.ctors family.ctors)
      (s.declaration.types.drop decl.types.length) direct
  recursors : g.restoredRecursors (compilationRestoration decl auxiliaries) =
    some block.recursors
  equations : g.restoredEquations (compilationRestoration decl auxiliaries) =
    some block.rules

/-- `CompilationData` for the lowered declaration of a validated nested run,
for any specialization list with the facts of `containerSpecializationFacts`,
modulo `NestedCompilationPending`. -/
theorem NestedValidatedRunResult.compilationData_of_specializations
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    {envTypes : VEnv} {auxiliaries : List ContainerSpecialization}
    (htypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (hnames : auxiliaries.map (·.auxiliary) =
      (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    (hwellFormed : ∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl
      E.production.constructors.toConstructorCheck.parameterScope.toCtx.reverse)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (hdirect : ∀ (U : Nat) (params : List VExpr), ∃ direct,
      auxiliaries.mapM (fun a => a.specializedFamily U params) = some direct ∧
      List.Forall₂ (DirectFamilyShape U) auxiliaries direct)
    (Hpending : NestedCompilationPending
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.production.compilationSignature E.production.compilationInstance
      auxiliaries
      (canonicalRestoredBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors
        C.primaryRules C.auxiliaryRules)) :
    CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.production.loweredDecl E.production.compilationSignature
      E.production.compilationInstance auxiliaries
      (canonicalRestoredBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors
        C.primaryRules C.auxiliaryRules) := by
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have hexpanded : C.formationAssembly.expanded = E.production.loweredDecl := by
    rw [C.formationExpanded, hC]
  have HexpandedSource : E.production.loweredDecl.SourceWF
      (ves.venv (if isUnsafe then .unsafe else .safe)) :=
    hexpanded ▸ C.formationAssembly.expandedSource
  have Hmodels : E.production.compilationSignature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.loweredDecl := by
    have h := E.production.loweredConstruction.generator.models
    change E.production.compilationSignature.Models E.production.initialEnv
      E.production.loweredDecl at h
    rwa [hinit] at h
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have hsourceNonempty : sourceDecl.types ≠ [] := by
    rw [C.typesSource]; simp
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.production.loweredDecl.typeConstants =
        some E.production.constructors.toConstructorCheck.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.production.loweredDecl.typeConstants =
          some E.production.constructors.toConstructorCheck.headerVEnv) hinit)
      E.production.constructors.toConstructorCheck.core.typesAdded
  have hloweredCtors := E.production.constructors.toConstructorCheck.core.ctorsAdded
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hlowered := VEnv.addConstVals_append hloweredTypes hloweredCtors
  have hrecursorsAdded := E.production.production.installed.abstract
  have hrecursorValues : E.production.production.entries.map Prod.snd =
      E.production.compilationInstance.recursors :=
    E.production.production.canonicalRecursors
  rw [hrecursorValues, E.production.constructors.toConstructorCheck.contextVEnv]
    at hrecursorsAdded
  have hrecursorsFresh := VEnv.addConstVals_names_fresh hrecursorsAdded
  simp only [VEnv.addEliminators_constants, VEnv.addProjections_constants] at hrecursorsFresh
  have hctorFresh : ∀ recursor ∈ E.production.compilationInstance.recursors,
      E.production.constructors.toConstructorCheck.ctorVEnv.constants recursor.name = none :=
    hrecursorsFresh.2
  have HsourceWF := TrInductDeclCore.sourceWF_ofNonempty Hsource hsourceNonempty
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars :=
    hexpanded ▸ C.formationAssembly.uvars
  refine {
    sourceWF := HsourceWF
    sourceParameters := C.formationAssembly.sourceParameters
    expandedWF := HexpandedSource
    headerPrefix := by
      have h := E.nativeSource.sourceTypeValues
      rw [E.nativeSourceDecl_eq] at h
      rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
    expandedFormation := hexpanded ▸ C.formationAssembly.expandedFormation
    model := Hmodels
    uvars := hexpanded ▸ C.formationAssembly.uvars
    nparams := hexpanded ▸ C.formationAssembly.nparams
    safety := hexpanded ▸ C.formationAssembly.isUnsafe
    restorationScoped := hscoped
    correspondence := by
      have hparams : E.production.compilationSignature.params =
          E.production.constructors.toConstructorCheck.parameterScope.toCtx.reverse :=
        E.production.loweredConstruction.generator.params
      obtain ⟨direct, hmapM, hshapes⟩ :=
        hdirect sourceDecl.uvars E.production.compilationSignature.params
      refine ⟨envTypes, direct, htypes, hmapM, hparams ▸ hwellFormed, ?_⟩
      have HT := C.formationAssembly.types
      rw [hexpanded] at HT
      obtain ⟨HTsource, HTgenerated⟩ := forall₂_append_left_split HT
      have HM := Hmodels.families
      have hle := VEnv.addConstVals_le htypes
      have hsplit := List.take_append_drop sourceDecl.types.length
        E.production.compilationSignature.declaration.types
      rw [← hsplit]
      have hprefixLength :
          (E.production.compilationSignature.declaration.types.take
            sourceDecl.types.length).length = sourceDecl.types.length := by
        rw [Lean4Lean.List.Forall₂.length_eq (List.forall₂_take HM sourceDecl.types.length)]
        exact (Lean4Lean.List.Forall₂.length_eq HTsource).symm
      refine (Lean4Lean.List.Forall₂.append_of_left hprefixLength).mpr ⟨?_, ?_⟩
      · have HMp := List.forall₂_take HM sourceDecl.types.length
        have HP := Hpending.sourceConstructors envTypes htypes
        obtain ⟨_, _, _, hheaders, _, _⟩ := C.formationAssembly.sourceParameters
        have H1 := forall₂_join HMp HTsource
        refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and H1 HP))
        rintro a src ⟨⟨⟨x, hM, hT⟩, hP⟩, ha, hsrc⟩
        have hres : a.resultLevel ≈ src.resultLevel := by
          rw [← hT.resultLevel]; exact hM.2.2.2.1
        obtain ⟨domains, body, exprType, _, htype, hbody⟩ := (hheaders src hsrc).header
        refine ⟨hM.1.trans hT.name, hM.2.1.trans hT.uvars,
          hM.2.2.1.trans hT.numIndices, hres,
          ⟨domains, body, src.resultLevel, exprType, hres.symm, htype.mono hle,
            hbody.mono hle⟩, ?_⟩
        have Hnames := Lean4Lean.List.Forall₂.trans
          (fun _ _ _ h1 h2 => h1.trans h2.name)
          (forall₂_of_map_eq (f := VConstVal.name) (g := VConstVal.name) hM.2.2.2.2) (forall₂_swap hT.constructors)
        refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and Hnames hP))
        rintro n c ⟨⟨hname, hRT⟩, hn, hc⟩
        refine ⟨hname, ?_, hRT⟩
        rw [E.production.compilationSignature.declaration_ctor_uvars a
          (List.mem_of_mem_take ha) n hn, Hmodels.uvars, hloweredUvars,
          HsourceWF.2.2.2.1 c (List.mem_flatMap.mpr ⟨src, hsrc, hc⟩)]
      · have HMd := Lean4Lean.List.forall₂_drop HM sourceDecl.types.length
        have HP := Hpending.auxiliaryFamilies envTypes direct htypes hmapM
        have Hnames := forall₂_of_map_eq (f := ContainerSpecialization.auxiliary)
          (g := fun t : VInductiveType => t.name) hnames
        have Hdirect := forall₂_join (forall₂_swap Hnames) (forall₂_swap hshapes)
        have H1 := forall₂_join HMd (forall₂_swap Hdirect)
        refine Lean4Lean.List.Forall₂.imp ?_
          (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and H1 HP))
        rintro a d ⟨⟨⟨x, hM, aux, hname, hshape⟩, hP⟩, ha, _⟩
        refine ⟨hM.1.trans (hname.symm.trans hshape.name.symm), ?_, hP.1, hP.2.1,
          hP.2.2.1, hP.2.2.2⟩
        rw [E.production.compilationSignature.declaration_type_uvars a
          (List.mem_of_mem_drop ha), Hmodels.uvars, hloweredUvars, hshape.uvars]
    admissible := ⟨_, hloweredTypes,
      E.production.loweredConstruction.generator.admissible⟩
    recursiveTypesWF := by
      refine ⟨_, _, E.production.constructors.toConstructorCheck.eliminators, hloweredTypes,
        hloweredCtors, ?_, ?_, ?_⟩
      · have hown := E.production.constructors.toConstructorCheck.eliminatorsOwn
        generalize E.production.constructors.toConstructorCheck.eliminators = es at hown ⊢
        rw [hinit] at hown
        exact hown
      · rw [← E.production.constructors.toConstructorCheck.contextVEnv]
        exact E.production.loweredConstruction.generator.recursiveTypesWF
      · rw [← E.production.constructors.toConstructorCheck.contextVEnv]
        exact E.production.loweredConstruction.generator.familyTypesWF
    familyTypesWF := by
      refine ⟨_, _, E.production.constructors.toConstructorCheck.eliminators, hloweredTypes,
        hloweredCtors, ?_, ?_⟩
      · have hown := E.production.constructors.toConstructorCheck.eliminatorsOwn
        generalize E.production.constructors.toConstructorCheck.eliminators = es at hown ⊢
        rw [hinit] at hown
        exact hown
      · rw [← E.production.constructors.toConstructorCheck.contextVEnv]
        exact E.production.loweredConstruction.generator.familyTypesWF
    recursorNames := E.production.loweredConstruction.generator.names
    generatedNames := by
      rw [List.map_append]
      refine List.nodup_append.mpr ⟨VEnv.addConstVals_names_nodup hlowered,
        hrecursorsFresh.1, ?_⟩
      intro x hx y hy hxy
      subst hxy
      rcases List.mem_map.mp hx with ⟨ci, hci, rfl⟩
      rcases List.mem_map.mp hy with ⟨recursor, hrecursor, hname⟩
      have hsome := VEnv.addConstVals_get hlowered hci
      rw [← hname, hctorFresh recursor hrecursor] at hsome
      cases hsome
    recursorsFresh := by
      intro recursor hrecursor
      cases hbase : (ves.venv (if isUnsafe then .unsafe else .safe)).constants
          recursor.name with
      | none => rfl
      | some c =>
        have := (VEnv.addConstVals_le hlowered).constants hbase
        rw [hctorFresh recursor hrecursor] at this
        cases this
    types := rfl
    ctors := rfl
    projections := rfl
    recursors := Hpending.recursors
    equations := Hpending.equations
    names := by
      have hvalues :
          (C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map
              Prod.snd =
            (canonicalRestoredBlock sourceDecl C.primaryRecursors
                C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).types ++
              (canonicalRestoredBlock sourceDecl C.primaryRecursors
                C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).ctors ++
              (canonicalRestoredBlock sourceDecl C.primaryRecursors
                C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).recursors := by
        simp only [List.map_append, canonicalRestoredBlock]
        rw [C.typeValues, C.constructorValues, C.recursorValues]
      rw [← hvalues]
      exact VEnv.addConstVals_names_nodup C.canonical.atomic.abstract }

end VerifyInductive
end Lean4Lean
