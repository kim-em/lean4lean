import Lean4Lean.Verify.Inductive.Nested.Restoration.Base
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Environment.Blocks
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorTranslations
import Lean4Lean.Verify.Inductive.Nested.Restoration.Recursors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorShape
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationDataConstructors

/-! # The telescopes of the restored recursors

`RecursorShapesAt` of every restored kernel recursor in the recursor stage of a restored block
base, read by `NestedRun.assemblyRecursors` (`AssemblyRecursors.lean`) for
`RestoredBlock.recShapes`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The restored recursors of a run are the restoration steps at the recursor names (the
`rvals_steps` of `AssemblyRecursors.lean`, restated here below it). -/
private theorem rvals_steps_aux {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) :
    List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
        (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
        Hs.restored.newInfo = rv)
      (types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames) H.rvals := by
  have h1 : ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        (types.map (fun t => Lean.mkRecName t.name)) H.inductiveRecs := by
    intro types sourceEnv targetEnv H
    induction H with
    | nil => exact .nil
    | cons h t ih => exact .cons ⟨_, _, h.restored.recursor, rfl⟩ ih
  have h2 : ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        names H.recursorInfos := by
    intro names sourceEnv targetEnv H
    induction H with
    | nil => exact .nil
    | cons h t ih => exact .cons ⟨_, _, h, rfl⟩ ih
  exact Lean4Lean.List.Forall₂.append (h1 H.inductives) (h2 H.auxiliaries)

/-- Every restored recursor of a run is the restoration step at the recursor name of a
generated owner. -/
theorem NestedRun.rval_step
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnonempty : sourceTypes ≠ []) {rv : RecursorVal} (hrv : rv ∈ E.restoration.rvals) :
    ∃ (owner : Fin E.lowered.recursors.generationSignature.families.size) (s t : Environment)
      (Hs : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 (sourceTypes.map (·.name))
        (E.lowered.recursors.canonicalGeneration.recursorName owner) s t),
      Hs.restored.newInfo = rv := by
  have hsteps := rvals_steps_aux E.restoration
  rw [← E.recursorNames_order hnonempty, Lean4Lean.List.forall₂_map_left_iff] at hsteps
  obtain ⟨owner, -, s, t, Hs, h⟩ := Lean4Lean.List.Forall₂.forall_exists_r hsteps rv hrv
  exact ⟨owner, s, t, Hs, h⟩

/-- **The recursor shape of every restored recursor**, without its rules, in the recursor
stage of the base (`RestoredRecursorShape`, whose `k` clause is the premise `hk`). -/
theorem NestedRun.restoredRecursorShapeOf
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered)
    (hk : ∀ rv ∈ E.restoration.rvals, rv.k = false) :
    ∃ auxiliaries : List ContainerSpecialization, ∀ rv ∈ E.restoration.rvals,
      ∃ owner, RestoredRecursorShape E.lowered.generatedInstance
        (compilationRestoration sourceDecl auxiliaries) C.recursorVEnv owner rv := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hrecs := E.restoredRecursorList_of_paramUniform C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.generatedInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.lowered.generatedInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have hequations : E.lowered.generatedInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some (rules ++ []) := by
    rw [List.append_nil]; exact hrulesEq
  obtain ⟨-, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC rules []
    hadded henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have htypesEq : C.install.venvTypes = envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.install.venvCtors := by
    have h := C.install.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  refine ⟨auxiliaries, fun rv hrv => ?_⟩
  obtain ⟨owner, s, t, Hs, rfl⟩ := E.rval_step C.sourceNonempty hrv
  obtain ⟨htype, hnp, hni, hnm, hnmin⟩ := E.restoredRecursorShapeFields C hC wf Hsources hadded
    Haux Hexpansion hnodup hparamsSize D hscoped owner Hs
  obtain ⟨head, -, hheadName, -, hargs, happ, -⟩ :=
    Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
  refine ⟨owner, {
    type := htype
    numParams := hnp
    numIndices := hni
    numMotives := hnm
    numMinors := hnmin
    k := hk _ hrv
    specialization := ⟨head, ?_, hargs, happ⟩ }⟩
  rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
    owner Hs, hheadName]

/-- **The rule-free telescope shapes of the restored recursors** in the recursor stage of the
base, as `NestedRun.strippedValid` reads them. -/
theorem NestedRun.restoredRecursorTelescopes
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered)
    (hk : ∀ rv ∈ E.restoration.rvals, rv.k = false) :
    ∀ r ∈ E.restoration.rvals, ∃ cnparams indLevels ctorParams,
      Nonempty (VRecursorShape C.recursorVEnv r.name r.levelParams.length r.numParams
        cnparams r.numMotives r.numMinors r.numIndices r.getMajorInduct indLevels ctorParams) := by
  obtain ⟨auxiliaries, H⟩ := E.restoredRecursorShapeOf wf Hsources C hC hk
  intro r hr
  obtain ⟨owner, S⟩ := H r hr
  obtain ⟨head, -, hshape⟩ := S.shape
  exact ⟨_, _, _, hshape⟩

/-- **Stub (restB).** The recursor and constructor telescopes of every restored kernel recursor
in the recursor stage of the base (`RecursorShapesAt`, with its rules). The rule-free part is
`RestoredRecursorShape.alignmentCore`; the rule part is the `VConstructorShape` of each rule's
restored constructor (`restoredRuleConstructors`) at the recursor's major inductive. -/
theorem NestedRun.restoredRecursorShapes
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered) :
    ∀ rv ∈ E.restoration.rvals, RecursorShapesAt outEnv.constants C.recursorVEnv rv := by
  -- WAVE 3 STUB (restB): see the docstring.
  have := wf; have := Hsources; have := hC; sorry


end VerifyInductive
end Lean4Lean
