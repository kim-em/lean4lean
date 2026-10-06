import Lean4Lean.Verify.Inductive.CompletedRecursorPhases
import Lean4Lean.Verify.Inductive.CompletedSourceSignature
import Lean4Lean.Verify.Inductive.Header.SingletonElimination
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterRawShape
import Lean4Lean.Theory.Inductive.SignatureLemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The universe and naming policy is fixed by the successful executable
run, independently of the supplied source signature. -/
noncomputable def CompletedRecursorPhasesResult.generationInstance
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (s : InductiveSignature) :
    InductiveSignature.Instance s where
  uvars := (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
  levels := recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  targetLevel := Classical.choose H.elimLevelAdmissible.ofLevel
  recursorName owner := s.families[owner].name.str "rec"

/-- The completed run fixes both the source signature and its universe
instance. Generation and concrete metadata must use this same choice. -/
noncomputable def CompletedRecursorPhasesResult.canonicalGeneration
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    InductiveSignature.Instance H.toCompletedRecursorConstruction.generationSignature :=
  H.toCompletedRecursorConstruction.generationInstance

/-- The final phase result installs precisely its one canonical generator's
recursor table. -/
theorem CompletedRecursorPhasesResult.canonicalGeneration_recursors
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    H.entries.map Prod.snd = H.canonicalGeneration.recursors :=
  H.canonicalRecursors

theorem CompletedRecursorPhasesResult.generationInstance_target
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (s : InductiveSignature) :
    VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some (H.generationInstance s).targetLevel :=
  Classical.choose_spec H.elimLevelAdmissible.ofLevel

/-- The completed producer retains the reason for its elimination universe.
The nonzero branch is already interpreted in the independent source model;
the singleton branch retains every actual field check for interpretation
against the normalized constructor telescope. -/
theorem CompletedRecursorPhasesResult.eliminationDecision
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    (∀ family ∈ decl.types, family.resultLevel.IsNeverZero) ∨
    H.elimLevel = .zero ∨
    ∃ ind, indTypes = #[ind] ∧
      (ind.ctors = [] ∨ ∃ ctor, ind.ctors = [ctor] ∧
        LargeEliminationTrace stats
          { c with env := ctorEnv, checkLCtx := {} } ctor.type 0 #[]) := by
  by_cases hzero : H.elimLevel = .zero
  · exact .inr (.inl hzero)
  rcases AddInductive.isLargeEliminator.shape_of_checked
      (AddInductive.getElimLevel.large_of_checked H.elimLevelChecked hzero) with
    hnotzero | ⟨ind, hind, hctors⟩
  · exact .inl fun _ hfamily =>
      R.sourceMaterialized.familyNeverZero hnotzero hfamily
  · refine .inr (.inr ⟨ind, hind, ?_⟩)
    rcases hctors with hnil | ⟨ctor, hctor, hchecked⟩
    · exact .inl hnil
    · exact .inr ⟨ctor, hctor,
        AddInductive.isLargeEliminator.loop.trace hchecked⟩

/-- Source modeling transports the nonzero decision to every specialized
family in the selected signature. -/
theorem CompletedRecursorPhasesResult.generationInstance_nonzero
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (Hmodel : s.Models sourceEnv decl)
    (Hnonzero : ∀ family ∈ decl.types, family.resultLevel.IsNeverZero) :
    ∀ family ∈ s.families.toList,
      (family.resultLevel.inst (H.generationInstance s).levels).IsNeverZero := by
  intro family hfamily
  rcases List.mem_iff_getElem.mp hfamily with ⟨i, hi, rfl⟩
  let owner : Fin s.families.size := ⟨i, by simpa using hi⟩
  rcases Hmodel.family owner with ⟨source, hsource, _, _, _, hlevel, _⟩
  exact ((Hnonzero source hsource).of_equiv hlevel.symm).inst

/-- Once the remaining singleton-field alternative is interpreted, the
universe policy satisfies the independent generator's full admissibility
judgment. Neither universe arity nor naming is a caller choice. -/
theorem CompletedRecursorPhasesResult.generationInstance_admissible
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (Hmodel : s.Models sourceEnv decl)
    (Helim :
      (∀ family ∈ decl.types, family.resultLevel.IsNeverZero) ∨
      H.elimLevel = .zero ∨
      s.SingletonElimination R.headerVEnv (H.generationInstance s).uvars
        (H.generationInstance s).levels) :
    (H.generationInstance s).Admissible R.headerVEnv := by
  refine {
    levels_length := ?_
    levels_wf := recursorDeclarationAbstractLevels_wf H.elimLevelAdmissible
    target_wf := .of_ofLevel (H.generationInstance_target s)
    elimination := ?_ }
  · change (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible).length = s.uvars
    rw [recursorDeclarationAbstractLevels_length, Hmodel.uvars, R.core.uvars]
  · rcases Helim with hnonzero | hsmall | hsingleton
    · exact .inl (H.generationInstance_nonzero Hmodel hnonzero)
    · apply Or.inr; apply Or.inl
      have ht := H.generationInstance_target s
      rw [hsmall] at ht
      have : (H.generationInstance s).targetLevel = .zero := Option.some.inj ht.symm
      rw [this]
      rfl
    · exact .inr (.inr hsingleton)

open _root_.Lean4Lean.InductiveSignature in


/-- Admissibility belongs to the same consumed signature selected before
installation, including the actual singleton decision and universe policy. -/
theorem CompletedRecursorPhasesResult.canonicalGeneration_admissible
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    H.canonicalGeneration.Admissible R.headerVEnv :=
  H.toCompletedRecursorConstruction.consumedGeneration.admissible

end VerifyInductive
end Lean4Lean
