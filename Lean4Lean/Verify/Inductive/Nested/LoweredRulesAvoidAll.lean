import Lean4Lean.Verify.Inductive.Nested.LoweredRulesAvoid

/-! # Avoidance of all restorable names by the lowered rules

The restorable names of the compilation restoration of a nested run are the
auxiliary family names `_nested.i`, the auxiliary constructor names (the
container constructor names with the container prefix replaced by
`_nested.i`), and the lowered auxiliary recursor names `_nested.i.rec`.

* `NestedValidatedRunResult.restorableNames_reserved`: every restorable name
  lies in the reserved `_nested` namespace.
* `NestedValidatedRunResult.restorableNames_lit`: hence no literal mentions a
  restorable name.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

section Reserved

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- **Every restorable name lies in the reserved `_nested` namespace.** Each
auxiliary family name is `_nested.i` (`resultFamilyNamesReservedOfEmpty`),
each auxiliary constructor name is obtained by replacing the container prefix
of a container constructor name by the auxiliary family name (the replacement
is effective, `RestorationTableData.ctorRenamed`), and each auxiliary recursor
name is `A.rec` for an auxiliary family name `A`. -/
theorem NestedValidatedRunResult.restorableNames_reserved
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      (`_nested).isPrefixOf n = true := by
  rcases E.lowering with ⟨finalState, Hrun, -, -⟩
  have hres := Hrun.resultFamilyNamesReservedOfEmpty rfl
  have hauxRes : ∀ a ∈ auxiliaries, NamePrefix `_nested a.auxiliary := by
    intro a ha
    obtain ⟨nested, hfind⟩ := D.familyLookup a ha
    exact namePrefix_of_isPrefixOf (hres _ _ hfind)
  intro n hn
  simp only [Restoration.restorableNames, compilationRestoration_heads_auxiliary,
    compilationRestoration_recursors_fst, List.mem_append, List.mem_flatMap,
    List.mem_map] at hn
  rcases hn with ⟨a, ha, hn⟩ | ⟨a, ha, rfl⟩
  · simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨ctor, hctor, rfl⟩
    · exact (hauxRes a ha).isPrefixOf
    · have hP := namePrefix_of_replacePrefix_ne (D.ctorRenamed a ha ctor hctor)
      exact ((hauxRes a ha).trans' (hP.replacePrefix_prefix a.auxiliary)).isPrefixOf
  · exact (NamePrefix.str "rec" (hauxRes a ha)).isPrefixOf

/-- **No literal mentions a restorable name**: the constants of the
constructor form of a literal (`Nat.zero`, `Nat.succ`, `Char.ofNat`,
`String.ofList`, `List.nil`, `List.cons`, `Char`) lie outside the reserved
`_nested` namespace. -/
theorem NestedValidatedRunResult.restorableNames_lit
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ l : Literal, l.toConstructor.AvoidsConsts
      (compilationRestoration sourceDecl auxiliaries).restorableNames := by
  intro l
  have h := avoidsConsts_lit_of_reserved (E.restorableNames_reserved D) l
  cases h with
  | lit _ h => exact h

end Reserved

end VerifyInductive
end Lean4Lean
