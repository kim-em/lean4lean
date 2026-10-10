import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyKernel

/-! # The constructor shape of a container constructor

`NestedRun.containerConstructorShape`: a constructor `c` of the container family of a
specialization has, in the source constructor stage, the constructor shape at the number of
specialization arguments plus the field count of the generated constructor it specializes.
With `NestedRun.loweredConstructorShape` (moved here from `RuleConstructors.lean`, which
imports this file). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The lowered constructor of a generated constructor has the constructor shape at the lowered
parameter count plus the generated field count. -/
theorem NestedRun.loweredConstructorShape
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {venv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes venv sourceDecl lparams nparams isUnsafe
      safety outEnv)
    (index : Fin E.lowered.signature.constructors.size) :
    ∃ ci, E.lowered.constructors.ctorVEnv.constants
        E.lowered.signature.constructors[index].name = some ci ∧
      ci.type.CtorShape (E.lowered.loweredDecl.nparams +
        E.lowered.signature.constructors[index].fields.length) := by
  let H := E.lowered.recursors
  let owner : Fin H.generationSignature.families.size :=
    E.lowered.signature.constructors[index].owner
  have hmem : index ∈ H.generationSignature.ownedConstructors owner := by
    unfold InductiveSignature.ownedConstructors
    exact List.mem_filter.mpr ⟨List.mem_finRange _, beq_self_eq_true _⟩
  obtain ⟨l, hl, hidx⟩ := List.mem_iff_getElem.mp hmem
  have hcov := H.rulesCoverage owner
  obtain ⟨hl', Htr⟩ := List.forall₂_getElem_exists hcov l hl
  replace Htr := hidx ▸ Htr
  have hru : H.modelRule index ((H.rvalAt owner).rules[l]) ∈ (H.modelRecursor owner).rules := by
    simp only [RecursorInstallation.modelRecursor]
    have hlz : l < (List.zipWith H.modelRule (H.generationSignature.ownedConstructors owner)
        (H.rvalAt owner).rules).length := by
      simp only [List.length_zipWith]; exact Nat.lt_min.mpr ⟨hl, hl'⟩
    have := List.getElem_mem hlz
    rw [List.getElem_zipWith] at this
    exact hidx ▸ this
  obtain ⟨ci, hci, hshape⟩ := H.rulesCtor owner _ hru
  refine ⟨ci, ?_, ?_⟩
  · have h : (H.modelRule index ((H.rvalAt owner).rules[l])).ctor =
        E.lowered.signature.constructors[index].name := Htr.ctor
    rw [← h]; exact hci
  · have h : (H.modelRule index ((H.rvalAt owner).rules[l])).nfields =
        E.lowered.signature.constructors[index].fields.length := Htr.nfields
    rw [← h]; exact hshape

/-- **Stub (restB).** The constructor shape of a container constructor at the specialization
arguments plus the field count of the generated constructor it specializes.

What it needs: the generated constructor is the container constructor instantiated at the
specialization arguments under the common parameters
(`SpecializationGenerates.constructorShapes`), the lowered constructor is its nested expansion
(`NestedTypeExpansion.constructors`, which keeps the forall arity), and the lowered constructor
has the lowered parameter count plus the generated field count
(`NestedRun.loweredConstructorShape`). -/
theorem NestedRun.containerConstructorShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    {envTypes : VEnv} {ctx : List VExpr} {generated : List VInductiveType}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes ctx sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (index : Fin E.lowered.signature.constructors.size)
    (hge : sourceDecl.types.length ≤ E.lowered.signature.constructors[index].owner.val)
    (hidx : E.lowered.signature.constructors[index].owner.val - sourceDecl.types.length <
      auxiliaries.length)
    {c : VConstVal}
    (hc : c ∈ (auxiliaries[E.lowered.signature.constructors[index].owner.val -
      sourceDecl.types.length]'hidx).source.ctors)
    (hname : E.lowered.signature.constructors[index].name =
      (auxiliaries[E.lowered.signature.constructors[index].owner.val -
        sourceDecl.types.length]'hidx).constructorName c) :
    ∃ ci, E.sourceCore.envCtors.constants c.name = some ci ∧
      ci.type.CtorShape ((auxiliaries[E.lowered.signature.constructors[index].owner.val -
        sourceDecl.types.length]'hidx).arguments.length +
        E.lowered.signature.constructors[index].fields.length) := by
  -- WAVE 3 STUB (restB): see the docstring.
  have := Haux; have := Hexpansion; have := Hdata; have := hge; have := hc; have := hname
  sorry


end VerifyInductive
end Lean4Lean
