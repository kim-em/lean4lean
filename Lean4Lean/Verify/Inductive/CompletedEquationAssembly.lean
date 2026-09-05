import Lean4Lean.Verify.Inductive.CompletedEquationFinal

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem CompletedRecursorPhasesResult.addInductOfOrdinaryCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.blockCertificate rules hrules).finalVEnv :=
  (H.blockCertificate rules hrules).addInductOfOrdinaryCompilation
    R.formation R.core hnonempty Hcompile

theorem CompletedRecursorPhasesResult.addInductOfNestedCompilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : NestedCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.blockCertificate rules hrules).finalVEnv :=
  (H.blockCertificate rules hrules).addInductOfNestedCompilation
    R.formation R.core hnonempty Hcompile

/-- Owner-prefix accumulation of reconstructed equations and their typing
proofs.  Keeping the equation traversal independent of the final block lets
this invariant grow in exactly the order used by `declareRecursors`. -/
structure CompletedRecursorPhasesResult.GeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (Us : List Name)
    (owner : Nat) (rules : List VDefEq) : Prop where
  equations : H.GeneratedIotaEquationTranslations Us [] owner rules
  rulesWF : ∀ rule ∈ rules, rule.WF H.outVEnv

def CompletedRecursorPhasesResult.GeneratedEquationBuild.empty
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (Us : List Name) :
    H.GeneratedEquationBuild Us 0 [] where
  equations := .nil
  rulesWF _ h := by simp at h

theorem CompletedRecursorPhasesResult.GeneratedEquationBuild.appendOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {prior : List VDefEq}
    (T : H.GeneratedEquationBuild Us owner prior)
    (howner : owner < H.entries.length)
    (batch : List VDefEq)
    (hlength : batch.length =
      (H.generated.entry owner howner).info.rules.length)
    (Hwitness : ∀ i
      (hctor : i < indTypes[owner]!.ctors.length)
      (hsource : i < (H.generated.entry owner howner).info.rules.length)
      (habstract : i < batch.length),
      Nonempty (H.GeneratedEquationWitness Us owner howner i hctor
        batch[i])) :
    H.GeneratedEquationBuild Us (owner + 1) (prior ++ batch) := by
  let E := H.generated.entry owner howner
  have hsourceOwner : owner < indTypes.size := by
    have hrec : owner < H.recInfos.size := by
      simpa [H.generated.length] using howner
    have htypes : H.recInfos.size = indTypes.size := by
      rw [H.cardinality.records]
      simpa using
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
    omega
  have hpriorLength : prior.length = recursorMinorOffset indTypes owner :=
    T.equations.ruleLength
  have hbatchLength : batch.length = indTypes[owner]!.ctors.length := by
    rw [hlength, E.rules.length]
  have hconcreteRoom := recursorMinorOffset_room indTypes owner hsourceOwner
  have hownedLength :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        decl.ownedConstructors.length := by
    simpa [ownedConstructors, List.length_flatMap] using
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
        R.core
  have hroom : batch.length + prior.length ≤
      decl.ownedConstructors.length := by
    rw [hbatchLength, hpriorLength, ← hownedLength]
    omega
  refine { equations := ?_, rulesWF := ?_ }
  · exact .cons T.equations howner batch hlength hroom (by
    intro i hctor hsource habstract _hindex
    rcases Hwitness i hctor hsource habstract with ⟨W⟩
    exact ⟨W.alignment, ⟨W.translation⟩, W.uvars⟩)
  · intro rule hrule
    rcases List.mem_append.mp hrule with hprior | hbatch
    · exact T.rulesWF rule hprior
    · rcases List.mem_iff_getElem.mp hbatch with ⟨i, hi, heq⟩
      have hsource : i <
          (H.generated.entry owner howner).info.rules.length := by
        rw [← hlength]
        exact hi
      have hctor : i < indTypes[owner]!.ctors.length := by
        rw [← E.rules.length]
        exact hsource
      rcases Hwitness i hctor hsource hi with ⟨W⟩
      rw [← heq]
      exact W.wf

/-- Pointwise reconstruction suffices to build the complete flattened rule
list.  The list itself is chosen in the production owner/constructor order;
length, coverage, and well-formedness are accumulated by
`GeneratedEquationBuild`. -/
theorem CompletedRecursorPhasesResult.existsGeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (Us : List Name)
    (Hpoint : ∀ owner (howner : owner < H.entries.length)
      i (hctor : i < indTypes[owner]!.ctors.length),
      ∃ rule : VDefEq,
        Nonempty (H.GeneratedEquationWitness Us owner howner i hctor rule)) :
    ∃ rules : List VDefEq,
      Nonempty (H.GeneratedEquationBuild Us H.entries.length rules) := by
  classical
  have go : ∀ owner, owner ≤ H.entries.length →
      ∃ rules : List VDefEq,
        Nonempty (H.GeneratedEquationBuild Us owner rules) := by
    intro owner hcovered
    induction owner with
    | zero => exact ⟨[], ⟨.empty H Us⟩⟩
    | succ owner ih =>
      have howner : owner < H.entries.length := by omega
      rcases ih (by omega) with ⟨prior, ⟨T⟩⟩
      let E := H.generated.entry owner howner
      let sourceCtorBound : ∀ j : Fin E.info.rules.length,
          j.1 < indTypes[owner]!.ctors.length := fun j => by
        rw [← E.rules.length]
        exact j.2
      let selected : Fin E.info.rules.length → VDefEq := fun j =>
        Classical.choose (Hpoint owner howner j.1 (sourceCtorBound j))
      let batch : List VDefEq := List.ofFn selected
      have hlength : batch.length = E.info.rules.length := by
        simp [batch]
      have Hwitness : ∀ i
          (hctor : i < indTypes[owner]!.ctors.length)
          (hsource : i < E.info.rules.length)
          (habstract : i < batch.length),
          Nonempty (H.GeneratedEquationWitness Us owner howner i hctor
            batch[i]) := by
        intro i hctor hsource habstract
        let j : Fin E.info.rules.length := ⟨i, hsource⟩
        have Hselected :=
          Classical.choose_spec (Hpoint owner howner j.1
            (sourceCtorBound j))
        simpa [batch, selected, j] using Hselected
      exact ⟨prior ++ batch, ⟨T.appendOwner howner batch hlength
        Hwitness⟩⟩
  exact go H.entries.length (Nat.le_refl _)

/-- Reconstruct the complete flattened equation batch directly from the
completed recursor phase.  Unlike `existsGeneratedEquationBuild`, this
endpoint has no pointwise premise: each equation is obtained from the
independently aligned constructor rule. -/
theorem CompletedRecursorPhasesResult.existsCanonicalGeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ rules : List VDefEq,
      Nonempty (H.GeneratedEquationBuild Us H.entries.length rules) := by
  dsimp only
  apply H.existsGeneratedEquationBuild
  intro owner howner i hctor
  rcases H.generatedRuleAlignment owner howner i hctor with ⟨A⟩
  exact A.finalCanonicalEquationWitness

/-- Declaration-facing package for the remaining concrete equation
translations of an ordinary recursor run.  Field selection, recursive-call
semantics, recursor presence, and pre-installation freshness are all derived
from `CompletedRecursorPhasesResult`; callers retain only post-installation equation
translation plus the opaque projection-preservation boundary. -/
structure CompletedRuleTranslationResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) where
  Us : List Name
  Δ : VLCtx
  rules : List VDefEq
  rulesWF : ∀ df ∈ rules, df.WF H.outVEnv
  owner : Nat
  equations : H.GeneratedIotaEquationTranslations Us Δ owner rules
  contextFree : VLCtx.NoIndConsts
    ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) Δ
  complete : owner = H.entries.length

def CompletedRecursorPhasesResult.GeneratedEquationBuild.completedResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {rules : List VDefEq}
    (T : H.GeneratedEquationBuild Us owner rules)
    (hcomplete : owner = H.entries.length) :
    CompletedRuleTranslationResult H where
  Us := Us
  Δ := []
  rules := rules
  rulesWF := T.rulesWF
  owner := owner
  equations := T.equations
  contextFree := by
    intro v mapped type hfind
    simp [VLCtx.find?] at hfind
  complete := hcomplete

/-- The completed recursor phase determines the full ordinary compilation
payload.  The only shared-typing premise is the generic structural property
of the opaque `TrProj` relation; no rule, telescope, or equation witness is
chosen by the caller. -/
theorem CompletedRecursorPhasesResult.canonicalCompletedRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    Nonempty (CompletedRuleTranslationResult H) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases H.existsCanonicalGeneratedEquationBuild with ⟨rules, ⟨T⟩⟩
  exact ⟨T.completedResult rfl⟩

theorem CompletedRuleTranslationResult.compilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    (T : CompletedRuleTranslationResult H) :
    OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate T.rules T.rulesWF).block :=
  H.ordinaryCompilationOfRuleBuild T.rules T.rulesWF
    (T.equations.build T.rules T.rulesWF T.contextFree)
    (T.equations.completeLength T.complete)


end VerifyInductive
end Lean4Lean
