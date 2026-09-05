import Lean4Lean.Verify.Inductive.Equation.Setup

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Recursor installation makes every generated recursor name fresh in the
completed constructor environment, independently of the formation route. -/
theorem CompletedRecursorPhasesResult.recursorNamesFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (rules : List VDefEq) (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    ∀ name ∈ (H.blockCertificate rules hrules).block.recursors.map (·.name),
      R.context.venv.constants name = none := by
  have hfresh := VEnv.addConstVals_names_fresh H.installed.abstract |>.2
  intro name hname
  change name ∈ (H.entries.map Prod.snd).map (·.name) at hname
  rcases List.mem_map.mp hname with ⟨recursor, hrecursor, rfl⟩
  simpa using hfresh recursor hrecursor

/-- Common equation-alignment layer for recursor runs entered from either
ordinary or atomic primitive formation. -/
def CompletedRecursorPhasesResult.generatedCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    GeneratedRecursors c.safety
      (R.context.venv.addProjections decl.projectionEntries) c.lparams
      H.elimLevel H.localContext stats indTypes H.recInfos H.entries := by
  simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using H.generated

/-- The semantic batch retained by the installer is the batch stored in the
corresponding generated recursor entry.  Source-info equality, rather than a
second indexing convention, identifies the two rule lists. -/
theorem CompletedRecursorPhasesResult.generatedRuleSemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    ∃ Hsemantic : SemanticBoundGeneratedRecursorRules indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        H.recursorWF decl owner indTypes[owner]!.ctors
        (recursorMinorOffset indTypes owner)
        (H.generated.entry owner howner).info.rules,
      Nonempty (Hsemantic.ProducerMotiveEvidence H.recInfos
        H.elimLevel) := by
  rcases H.ruleSemantics.entry owner howner with
    ⟨info, hsource, Hsemantic, Hmotive, _Horigins⟩
  let E := H.generated.entry owner howner
  have hinfo : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hsource.symm.trans E.source_eq
    injection heq
  subst info
  dsimp [E] at Hsemantic Hmotive ⊢
  let Hpair : ∃ Hs : SemanticBoundGeneratedRecursorRules indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        H.recursorWF decl (0 + owner) indTypes[0 + owner]!.ctors
        (recursorMinorOffset indTypes (0 + owner)) E.info.rules,
      Nonempty (Hs.ProducerMotiveEvidence H.recInfos H.elimLevel) :=
    ⟨Hsemantic, Hmotive⟩
  simpa only [Nat.zero_add] using Hpair

/-- Pointwise projection used by abstract iota reconstruction.  It exposes
the exact generated source rule together with the semantic trace from the
same executable constructor iteration. -/
theorem CompletedRecursorPhasesResult.generatedRuleSemantic
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrule : i < (H.generated.entry owner howner).info.rules.length) :
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (H.generated.entry owner howner).info.rules[i],
      ∃ S : Hrule.Semantics H.recursorWF decl owner,
        Nonempty (Hrule.ProducerOriginEvidence S H.recInfos H.elimLevel
          H.origins owner i) ∧
        S.parameterDecls = H.parameterSuffix.parameterDecls := by
  rcases H.ruleSemantics.entry owner howner with
    ⟨info, hsource, _Hsemantic, _Hmotive, Horigins⟩
  let E := H.generated.entry owner howner
  have hinfo : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hsource.symm.trans E.source_eq
    injection heq
  subst info
  dsimp [E] at Horigins ⊢
  have hzero : 0 + owner = owner := Nat.zero_add owner
  rw [hzero] at Horigins
  exact Horigins i hctor hrule

/-- The family selected from the generated residual is exactly the outer
owner whose constructor batch is being traversed. -/
theorem CompletedRecursorPhasesResult.generatedRuleSemanticOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrule : i < (H.generated.entry owner howner).info.rules.length) :
    ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (H.generated.entry owner howner).info.rules[i],
      ∃ Hsemantic : Hrule.Semantics
          H.recursorWF decl owner,
        Nonempty (Hrule.ProducerOriginEvidence Hsemantic H.recInfos
          H.elimLevel H.origins owner i) ∧
        Hsemantic.parameterDecls = H.parameterSuffix.parameterDecls ∧
        Hsemantic.ownerIdx = owner := by
  rcases H.generatedRuleSemantic owner howner i hctor hrule with
    ⟨Hrule, Hsemantic, Horigin, hparameterDecls⟩
  have htypeNames : (decl.types.map (·.name)).Nodup := by
    have hprefix := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup
        R.core)).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  exact ⟨Hrule, Hsemantic, Horigin, hparameterDecls,
    Hsemantic.owner_eq Hrule htypeNames⟩

/-- Complete source alignment for one rule emitted by the mutual recursor
loop.  The entry index selects the same concrete family in `indTypes`, the
same abstract family in `decl.types`, and the same abstract constructor in
that family's constructor list.  The semantic target selected while building
the rule is additionally identified with this owner.  Keeping these facts in
one dependent record prevents later iota reconstruction from silently mixing
the three independent indexing conventions. -/
structure CompletedRecursorPhasesResult.GeneratedRuleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length) where
  sourceOwner_lt : owner < indTypes.size
  sourceCtor_lt : i < indTypes[owner].ctors.length
  abstractOwner_lt : owner < decl.types.length
  abstractCtor_lt : i < decl.types[owner].ctors.length
  ownerTranslation : TrInductiveType sourceEnv R.headerVEnv
    c.lparams indTypes[owner] decl.types[owner]
  ctorTranslation : TrSourceConst R.headerVEnv c.lparams
    indTypes[owner].ctors[i].name indTypes[owner].ctors[i].type
    decl.types[owner].ctors[i]
  sourceRule_lt : i < (H.generated.entry owner howner).info.rules.length
  rule : BoundGeneratedRecursorRule indTypes stats
    (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels H.elimLevel stats.levels)
    indTypes[owner]!.ctors[i]
    (recursorMinorOffset indTypes owner + i)
    (H.generated.entry owner howner).info.rules[i]
  semantics : rule.Semantics
    H.recursorWF decl owner
  parameterDecls_eq : semantics.parameterSuffix.parameterDecls =
    H.parameterSuffix.parameterDecls
  motiveEvidence : Nonempty (rule.ProducerMotiveEvidence semantics
    H.recInfos H.elimLevel)
  originEvidence : Nonempty (rule.ProducerOriginEvidence semantics
    H.recInfos H.elimLevel H.origins owner i)
  semantic_owner : semantics.ownerIdx = owner

noncomputable def CompletedRecursorPhasesResult.GeneratedRuleAlignment.producerOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    A.rule.ProducerOriginEvidence A.semantics H.recInfos H.elimLevel
      H.origins owner i :=
  Classical.choice A.originEvidence

noncomputable def CompletedRecursorPhasesResult.GeneratedRuleAlignment.producerMinorShape
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    RecInfoMinorTypeShape :=
  A.producerOrigin.producer.minorShape

noncomputable def CompletedRecursorPhasesResult.GeneratedRuleAlignment.producerReplayAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    A.rule.ProducerCallReplayAt (recInfos := H.recInfos) A.semantics
      A.producerMinorShape j hj :=
  Classical.choice (A.producerOrigin.producer.replay j hj)

/-- Select the fully aligned pointwise rule package directly from the
completed recursor phase.  All bounds not supplied by the caller follow from
the generated-recursors cardinality and the source-declaration translation. -/
theorem CompletedRecursorPhasesResult.generatedRuleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length) :
    Nonempty (H.GeneratedRuleAlignment owner howner i hctor) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have habstractOwner : owner < decl.types.length := by
    simpa [H.cardinality.records] using hrecInfo
  have hsourceOwner : owner < indTypes.size := by
    have htypes : indTypes.size = decl.types.length := by
      simpa using
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
    omega
  have hsourceCtor : i < indTypes[owner].ctors.length := by
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using hctor
  have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    owner (by simpa using hsourceOwner) habstractOwner
  rw [Array.getElem_toList] at Howner
  have habstractCtor : i < decl.types[owner].ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Howner]
    exact hsourceCtor
  let Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Howner i
    hsourceCtor
    habstractCtor
  let E := H.generated.entry owner howner
  have hsourceRule : i < E.info.rules.length := by
    rw [E.rules.length]
    exact hctor
  rcases H.generatedRuleSemanticOwner owner howner i hctor hsourceRule with
    ⟨Hrule, Hsemantic, ⟨Horigin⟩, hparameterDecls, hsemanticOwner⟩
  let Hmotive : Nonempty (Hrule.ProducerMotiveEvidence Hsemantic H.recInfos
      H.elimLevel) := ⟨Horigin.producer⟩
  exact ⟨{
    sourceOwner_lt := hsourceOwner
    sourceCtor_lt := hsourceCtor
    abstractOwner_lt := habstractOwner
    abstractCtor_lt := habstractCtor
    ownerTranslation := Howner
    ctorTranslation := Hctor
    sourceRule_lt := hsourceRule
    rule := Hrule
    semantics := Hsemantic
    parameterDecls_eq := Hsemantic.parameterDecls_eq.trans hparameterDecls
    motiveEvidence := Hmotive
    originEvidence := ⟨Horigin⟩
    semantic_owner := hsemanticOwner }⟩

/-- The recursor selected by a generated rule carries the exact five-part,
binder-typed telescope recovered from the production `.recInfo`.  This is
the canonical source of the parameter, motive, and minor domains used when
typing the corresponding equation; it does not reconstruct those domains
from the rule RHS. -/
theorem CompletedRecursorPhasesResult.recursorTelescopeTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    Nonempty (GeneratedRecursorTelescopeTranslation
      (R.context.venv.addProjections decl.projectionEntries)
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let E := H.generated.entry owner howner
  rcases H.generatedTelescopeTranslations owner howner with
    ⟨info, hinfo, ⟨T⟩⟩
  have hinfoEq : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hinfo.symm.trans E.source_eq
    injection heq
  subst info
  refine ⟨?_⟩
  simpa [E.levels, H.localExtends.lparams_eq] using T

theorem CompletedRecursorPhasesResult.finalRecursorTelescopeTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    Nonempty (GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  rcases H.recursorTelescopeTranslationAt owner howner with ⟨T⟩
  exact ⟨T.mono H.installed.le⟩

/-- The translated common prefixes of any two installed mutual recursors
are definitionally equal.  The proof is deliberately factored through the
concrete generated source binders, so it does not assume that independently
translated abstract domain lists are syntactically identical. -/
theorem CompletedRecursorPhasesResult.finalRecursorCommonPrefixContextAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (T₁ : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner₁ howner₁).info.type
      H.entries[owner₁].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner₁]!.indices.size owner₁)
    (T₂ : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner₂ howner₂).info.type
      H.entries[owner₂].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner₂]!.indices.size owner₂) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (T₁.params ++ T₁.motives ++ T₁.minors).reverse
      (T₂.params ++ T₂.motives ++ T₂.minors).reverse := by
  apply T₁.commonPrefixDefEqCtx H.outVEnvWF T₂
  intro i hi _hi₁ _hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
  exact H.generatedRecursorCommonPrefixBinderDomainAt
    owner₁ howner₁ owner₂ howner₂ i hi Hbinder₁ Hbinder₂

theorem CompletedRecursorPhasesResult.GeneratedRuleAlignment.recursorTelescopeTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    Nonempty (GeneratedRecursorTelescopeTranslation
      (R.context.venv.addProjections decl.projectionEntries)
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  exact H.recursorTelescopeTranslationAt owner howner

theorem CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursorTelescopeTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    Nonempty (GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  exact H.finalRecursorTelescopeTranslationAt owner howner

/-- The parameter domains recovered from the installed generated recursor
are definitionally equal to the independently checked cached parameter
scope.  This is the canonical equation-context bridge: it compares contexts,
not syntax, and is derived from translation of the same concrete `mkForall`
prefix on both sides. -/
theorem
    CompletedRecursorPhasesResult.finalRecursorParameterContextAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        T.params.reverse parameterDecls.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases H.finalRecursorTelescopeTranslationAt owner howner with ⟨T⟩
  let E := H.generated.entry owner howner
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  let inner : Expr :=
    H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
    H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive
        H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have Hraw : TrExprS H.outVEnv Us []
      (H.localContext.lctx.mkForall stats.params inner)
      H.entries[owner].2.type := by
    have Htranslated := T.typed.translation
    rw [E.type] at Htranslated
    simpa [E.levels, H.localExtends.lparams_eq, inner, Us] using
      TrExprS.of_inferImplicit Htranslated
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact VEnv.addProjections_le.trans H.installed.le
  have Hsort : TrExprS H.outVEnv Us []
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (VExpr.wrapForalls H.parameterSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    have HsortBase := H.parameterSuffix.closedSortTranslation
    rw [H.recursorWF.lctx_eq] at HsortBase
    exact HsortBase.mono hbase
  have Hsame : Expr.SameForallPrefix stats.params.size
      (H.localContext.lctx.mkForall stats.params inner)
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level))) := by
    exact selections.params.sameForallPrefix
      hselectionNoAlias.parts.params inner (.sort (.zero : Level))
  have hnil : VLCtx.IsDefEq H.outVEnv Us.length ([] : VLCtx) [] :=
    .refl H.outVEnvWF.ordered (by trivial)
  rcases Hsame.translatedContexts H.outVEnvWF hnil Hraw Hsort with
    ⟨leftDomains, leftResidual, rightDomains, rightResidual,
      hleftLength, hrightLength, hleftTarget, hrightTarget, hcontexts⟩
  have hleftEq : leftDomains = T.params := by
    apply VExpr.wrapForalls_prefix_domains_eq hleftLength T.params_length
    calc
      VExpr.wrapForalls leftDomains leftResidual = H.entries[owner].2.type :=
        hleftTarget.symm
      _ = VExpr.wrapForalls
          (T.params ++ (T.motives ++ T.minors ++ T.indices ++ T.major))
          T.result := by
        simpa [List.append_assoc] using T.target_eq
  have hparameterCtxLength : H.parameterSuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    calc
      H.parameterSuffix.parameterDecls.toCtx.length =
          H.parameterSuffix.parameterDecls.length :=
        checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
          H.parameterSuffix.cached
      _ = stats.params.size := H.parameterSuffix.parameterDecls_length
  have hrightEq : rightDomains =
      H.parameterSuffix.parameterDecls.toCtx.reverse := by
    apply VExpr.wrapForalls_prefix_domains_eq hrightLength
      (by simpa using hparameterCtxLength)
    calc
      VExpr.wrapForalls rightDomains rightResidual =
          VExpr.wrapForalls H.parameterSuffix.parameterDecls.toCtx.reverse
            (.sort (.zero : VLevel)) := hrightTarget.symm
      _ = VExpr.wrapForalls
          (H.parameterSuffix.parameterDecls.toCtx.reverse ++ [])
          (.sort (.zero : VLevel)) := by simp
  refine ⟨T, ?_⟩
  simpa only [hleftEq, hrightEq, parameterDecls, ← H.parameterDecls,
    VLCtx.toCtx, List.append_nil, List.reverse_reverse] using hcontexts

/-- Translate the common parameter prefix of a generated recursor without
using the generated recursor translation itself.  The dummy sort telescope
comes from the pre-installation header certificate, so it can be weakened
into an independently compiled source environment even when the production
recursor suffix mentions lowered nested auxiliaries.  `SameForallDomains`
records the exact concrete-domain agreement after `inferImplicit`, while
deliberately forgetting the residual-dependent binder annotations. -/
theorem CompletedRecursorPhasesResult.sourceRecursorParameterTemplateAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    {newEnv : VEnv} (hsourceLE : sourceEnv ≤ newEnv) :
    let E := H.generated.entry owner howner
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let sourceSuffix :=
      R.sourceMaterialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible
    let template :=
      (c.lctx.mkForall stats.params
        (.sort (.zero : Level))).inferImplicit 1000 false
    Expr.ForallTelescope template stats.params.size
        (.sort (.zero : Level)) ∧
      Expr.SameForallDomains stats.params.size template E.info.type ∧
      TrExprS newEnv Us [] template
        (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) ∧
      newEnv.IsType Us.length []
        (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
          (.sort (.zero : VLevel))) := by
  let E := H.generated.entry owner howner
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceSuffix :=
    R.sourceMaterialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible
  let template :=
    (c.lctx.mkForall stats.params
      (.sort (.zero : Level))).inferImplicit 1000 false
  let sourceParams :=
    R.sourceMaterialized.parameterSuffix.paramsBound
  let sourceSelection := sourceParams.toLocalForallSelection
    R.sourceContext.toBindingContextWF
  have HtemplateRaw := sourceSelection.forallTelescope
    (.sort (.zero : Level))
  have htemplateResidual :
      (Expr.sort (.zero : Level)).abstractList sourceSelection.fvars =
        .sort (.zero : Level) := by
    induction sourceSelection.fvars with
    | nil => rfl
    | cons fv fvars ih =>
      simp only [Expr.abstractList]
      rw [show (Expr.sort (.zero : Level)).abstract1 fv =
        .sort (.zero : Level) by rfl]
      exact ih
  rw [htemplateResidual] at HtemplateRaw
  have HtemplateTelescope : Expr.ForallTelescope template stats.params.size
      (.sort (.zero : Level)) := by
    simpa [template] using
      HtemplateRaw.inferImplicit_sameResidual (by rfl) 1000 false
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  let inner : Expr :=
    H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
    H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive
        H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have HrawPrefix : Expr.SameForallPrefix stats.params.size
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (H.localContext.lctx.mkForall stats.params inner) :=
    selections.params.sameForallPrefix
      hselectionNoAlias.parts.params (.sort (.zero : Level)) inner
  have hsourceMkForall :
      H.localContext.lctx.mkForall stats.params
          (.sort (.zero : Level)) =
        c.lctx.mkForall stats.params (.sort (.zero : Level)) := by
    let sourceParamsAtCtor : BoundFVarArray { c with env := ctorEnv }
        stats.params := sourceParams.monoFVars (by
          intro fv hfv
          exact hfv)
    have HlocalExtendsBase :
        BindingContextLE { c with env := ctorEnv } H.localContext := by
      simpa using H.localExtends.rebaseTypeCheckerLParams
        c.typeCheckerLParams H.localContext.typeCheckerLParams
    exact sourceParamsAtCtor.mkForall_mono HlocalExtendsBase
      (.sort (.zero : Level))
  have Hdomains : Expr.SameForallDomains stats.params.size template
      E.info.type := by
    have Himplicit := HrawPrefix.sameForallDomains.inferImplicit 1000 false
    rw [hsourceMkForall] at Himplicit
    rw [E.type]
    simpa [template, inner] using Himplicit
  have HsourceTranslation : TrExprS sourceEnv Us []
      (c.lctx.mkForall stats.params (.sort (.zero : Level)))
      (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    have Hbase := sourceSuffix.closedSortTranslation
    let sourceRecContext :=
      R.sourceContext.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible
    have hlctx : sourceRecContext.mlctx.lctx = c.lctx :=
      sourceRecContext.lctx_eq
    have hvenv : sourceRecContext.venv = sourceEnv :=
      (ContextWF.toAdmissibleRecursorContextWF_venv
        R.sourceContext H.elimLevelAdmissible).trans
          R.sourceContextVEnv
    rw [hlctx, hvenv] at Hbase
    simpa [Us, sourceSuffix] using Hbase
  have HsourceType : sourceEnv.IsType Us.length []
      (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    have Hbase := sourceSuffix.closedSortTyped.2
    let sourceRecContext :=
      R.sourceContext.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible
    have hvenv : sourceRecContext.venv = sourceEnv :=
      (ContextWF.toAdmissibleRecursorContextWF_venv
        R.sourceContext H.elimLevelAdmissible).trans
          R.sourceContextVEnv
    rw [hvenv] at Hbase
    simpa [Us, sourceSuffix] using Hbase
  have HtemplateTranslation : TrExprS newEnv Us [] template
      (VExpr.wrapForalls sourceSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    exact TrExprS.inferImplicit (HsourceTranslation.mono hsourceLE) 1000 false
  exact ⟨HtemplateTelescope, Hdomains, HtemplateTranslation,
    HsourceType.mono hsourceLE⟩

/-- Rule-local specialization of `finalRecursorParameterContextAt`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursorParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        T.params.reverse parameterDecls.toCtx := by
  exact H.finalRecursorParameterContextAt owner howner

/-- Every retained translation of the installed generated recursor has the
same canonical parameter context.  The existential witness selected by
`finalRecursorParameterContextAt` is immaterial because the five retained
telescope groups are uniquely determined by the common source and target. -/
theorem
    CompletedRecursorPhasesResult.finalRecursorParameterContextFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {owner : Nat} (howner : owner < H.entries.length)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      T.params.reverse
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx := by
  rcases H.finalRecursorParameterContextAt owner howner with
    ⟨T₀, Hparams⟩
  have hparams : T.params = T₀.params :=
    (T.groupsResult_eq T₀).1
  simpa only [hparams] using Hparams

/-- The original production constructor type has exactly the common
parameter prefix replayed by `mkRecInfos`, followed by the genuine field
suffix opened while generating this rule.  This is a source-syntax fact: it
does not identify the rule's larger retained local context with the canonical
equation context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.sourceConstructorTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ residual,
      Expr.ForallTelescope
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        (stats.params.size + A.rule.allArgs.size) residual := by
  rcases A.semantics.parameterPrefix.toNestedParamOpening
      A.rule.params_bound with ⟨parameterLctx, Hparams⟩
  have Hsource := Hparams.reflectForallTelescope
    A.semantics.fieldOpening.telescope
  simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using Hsource

/-- Inverting the independently checked source-constant translation along
the exact combined parameter/field telescope exposes a typed abstract
constructor telescope in the final environment.  Its universe names are
still the declaration names; recursor-level reindexing is a separate step. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSourceConstructorTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ residual,
      Expr.ForallTelescope
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        (stats.params.size + A.rule.allArgs.size) residual ∧
      Expr.ForallTelescopeTypeTranslation H.outVEnv c.lparams []
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        (stats.params.size + A.rule.allArgs.size)
        ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).type := by
  rcases A.sourceConstructorTelescope with ⟨residual, Htelescope⟩
  have henv : R.headerVEnv ≤ H.outVEnv :=
    R.installation.constructorLE.trans
      (VEnv.addProjections_le.trans H.installed.le)
  have Htranslation := A.ctorTranslation.type.mono henv
  have Htype : H.outVEnv.IsType c.lparams.length []
      ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).type := by
    simpa [VConstant.WF, A.ctorTranslation.uvars] using
      A.ctorTranslation.wf.mono henv
  exact ⟨residual, Htelescope,
    Expr.ForallTelescopeTypeTranslation.ofTrExprS Htelescope
      Htranslation Htype⟩

/-- Parameter/field decomposition of the original constructor telescope.
The field certificate is now checked under precisely the abstract parameter
prefix, with no motives, minors, mutual indices, or majors retained from the
executable reader context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSourceConstructorFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ parameterDomains fieldSource fieldTarget,
      parameterDomains.length = stats.params.size ∧
      Expr.ForallTelescope
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
        stats.params.size fieldSource ∧
      ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).type =
        VExpr.wrapForalls parameterDomains fieldTarget ∧
      Expr.ForallTelescopeTypeTranslation H.outVEnv c.lparams
        (abstractForallContext parameterDomains []) fieldSource
        A.rule.allArgs.size fieldTarget := by
  rcases A.finalSourceConstructorTelescope with
    ⟨_residual, _Htelescope, Htyped⟩
  exact Htyped.dropPrefix

/-- Re-select the constructor-checking synthesis for this exact source
position and transport it across recursor installation.  Unlike
`finalSourceConstructorFrame`, this certificate is already rebased to the
recursor universe list and uses the materialized canonical parameter scope. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorSynthesis
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ ctorVal tailTarget,
      ctorVal ∈ (decl.types[owner]'A.abstractOwner_lt).ctors ∧
      ctorVal.name =
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name ∧
      Nonempty
        (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          H.outVEnv Us
          (recursorConstructorTelescopeTarget ctorVal
            H.elimLevelAdmissible)
          parameterDecls tailTarget stats.params.size 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases R.checkedConstructorPrefixSeedAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨ctorVal, _tail, tailTarget, _introTarget, hctorMem, hctorName,
      _Hprefix, _Htail, _HtailType, _Hintro, _HintroShape,
      _HintroType, ⟨Hsynthesis⟩⟩
  refine ⟨ctorVal, tailTarget, ?_, hctorName, ⟨?_⟩⟩
  · simpa using hctorMem
  · have hbaseLE :
        (R.context.toAdmissibleRecursorContextWF
          H.elimLevelAdmissible).venv ≤ H.outVEnv := by
      simpa only [ContextWF.toAdmissibleRecursorContextWF_venv] using
        VEnv.addProjections_le.trans H.installed.le
    simpa [Us, parameterDecls] using Hsynthesis.mono hbaseLE

/-- The independently checked constructor application transports into the
actual generated recursor parameter context.  The translated term and its
residual type are retained from constructor checking; only the ambient
context changes, via `finalRecursorParameterContext`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (tailTarget introTarget : VExpr),
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) ∧
        H.outVEnv.HasType Us.length T.params.reverse
          introTarget tailTarget := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalRecursorParameterContext with ⟨T, hparams⟩
  rcases R.checkedConstructorPrefixSeedAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨_ctorVal, _tail, tailTarget, introTarget, _hctorMem, _hctorName,
      _Hprefix, _Htail, _HtailType, Hintro, HintroShape,
      HintroType, _Hsynthesis⟩
  have hbaseLE :
      (R.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    simpa only [ContextWF.toAdmissibleRecursorContextWF_venv] using
      VEnv.addProjections_le.trans H.installed.le
  have Hintro' : TrExprS H.outVEnv Us parameterDecls
      (mkAppN (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        stats.params) introTarget := by
    simpa [Us, parameterDecls] using Hintro.mono hbaseLE
  have HintroType' : H.outVEnv.HasType Us.length parameterDecls.toCtx
      introTarget tailTarget := by
    simpa [Us, parameterDecls] using HintroType.mono hbaseLE
  refine ⟨T, tailTarget, introTarget, Hintro', HintroShape, ?_⟩
  exact HintroType'.defeqDFC H.outVEnvWF.ordered
    (hparams.symm H.outVEnvWF.ordered)

/-- Decompose the independently checked constructor tail along the genuine
field telescope retained by rule generation.  This joins the constructor
checker and recursor generator only through their common source tail; the
abstract parameter contexts are related by conversion, not by syntactic
equality. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorFieldFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us parameterDecls
          A.semantics.parameterTail
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext fieldDomains parameterDecls)
          (A.rule.target.abstractList A.semantics.fieldOpening.fvars)
          fieldResult ∧
        H.outVEnv.IsType Us.length parameterDecls.toCtx
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        H.outVEnv.IsType Us.length T.params.reverse
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        OnCtx (fieldDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length T.params.reverse introTarget
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalRecursorParameterContext with ⟨T, hparams⟩
  rcases R.checkedConstructorPrefixSeedAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨_ctorVal, tail, tailTarget, introTarget, _hctorMem, _hctorName,
      Hprefix, Htail, HtailType, Hintro, HintroShape,
      HintroType, _Hsynthesis⟩
  have HsemanticPrefix : RecursorParamPrefix stats 0
      ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
      A.semantics.parameterTail := by
    simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using
      A.semantics.parameterPrefix
  have htail : tail = A.semantics.parameterTail :=
    Hprefix.tail_eq HsemanticPrefix
  subst tail
  have hbaseLE :
      (R.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    simpa only [ContextWF.toAdmissibleRecursorContextWF_venv] using
      VEnv.addProjections_le.trans H.installed.le
  have Htail' : TrExprS H.outVEnv Us parameterDecls
      A.semantics.parameterTail tailTarget := by
    simpa [Us, parameterDecls] using Htail.mono hbaseLE
  have HtailType' : H.outVEnv.IsType Us.length parameterDecls.toCtx
      tailTarget := by
    simpa [Us, parameterDecls] using HtailType.mono hbaseLE
  have Hintro' : TrExprS H.outVEnv Us parameterDecls
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        stats.params) introTarget := by
    simpa [Us, parameterDecls] using Hintro.mono hbaseLE
  have HintroType' : H.outVEnv.HasType Us.length T.params.reverse
      introTarget tailTarget := by
    have Htyped : H.outVEnv.HasType Us.length parameterDecls.toCtx
        introTarget tailTarget := by
      simpa [Us, parameterDecls] using HintroType.mono hbaseLE
    exact Htyped.defeqDFC H.outVEnvWF.ordered
      (hparams.symm H.outVEnvWF.ordered)
  have Hfields := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    A.semantics.fieldOpening.telescope Htail' HtailType'
  rcases Hfields.toWrapForalls with
    ⟨fieldDomains, sourceResidual, fieldResult, hfields,
      HsourceTelescope, htarget, Hresult, _HresultType⟩
  have hsourceResidual :
      sourceResidual = A.semantics.fieldOpening.residual :=
    HsourceTelescope.residual_eq A.semantics.fieldOpening.telescope
  have HfieldResidual : TrExprS H.outVEnv Us
      (abstractForallContext fieldDomains parameterDecls)
      (A.rule.target.abstractList A.semantics.fieldOpening.fvars)
      fieldResult := by
    rw [A.semantics.fieldOpening.closed, ← hsourceResidual]
    exact Hresult
  subst tailTarget
  have HtailTypeT : H.outVEnv.IsType Us.length T.params.reverse
      (VExpr.wrapForalls fieldDomains fieldResult) :=
    HtailType'.defeqDFC H.outVEnvWF.ordered
      (hparams.symm H.outVEnvWF.ordered)
  have HfieldContext : OnCtx
      (fieldDomains.reverse ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) :=
    (VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
      hparams.isType HtailTypeT).1
  exact ⟨T, fieldDomains, fieldResult, introTarget, hparams, hfields,
    Htail', HfieldResidual, HtailType', HtailTypeT, HfieldContext,
    HintroType', Hintro', HintroShape⟩

/-- Close the cached common parameters around a constructor result already
translated below its genuine field telescope.  Keeping this lemma
parameterized by the field-frame witnesses lets later equation proofs retain
the very same recursor telescope witness. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.cachedConstructorTargetOfFieldFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (HfieldResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext fieldDomains
        (R.materializedFinal.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls)
      (A.rule.target.abstractList A.semantics.fieldOpening.fvars)
      fieldResult) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) [])
      (A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.semantics.fieldOpening.fvars))
      fieldResult := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  dsimp only
  have hparamExprs : stats.params.toList.reverse =
      (A.rule.params_bound.fvars.reverse.map Expr.fvar) := by
    have h := congrArg Array.toList A.rule.params_bound.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have Hcached : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl
      (A.rule.params_bound.fvars.reverse.map Expr.fvar) parameterDecls := by
    have Hbase := H.parameterSuffix.cached
    rw [hparamExprs] at Hbase
    simpa [parameterDecls, H.parameterDecls] using Hbase
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      A.rule.params_bound.fvars.reverse parameterDecls := by
    rw [List.forall₂_map_left_iff] at Hcached
    exact Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have hparamsNodup : A.rule.params_bound.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr <|
      (List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have Hclosed :=
    Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
      Hdecls hparamsNodup HfieldResidual
  have hparamsFields :
      (A.rule.params_bound.fvars ++
        A.semantics.fieldOpening.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_reverse.mp hparamsNodup,
      A.semantics.fieldOpening.nodup, ?_⟩
    intro param hparam field hfield heq
    subst field
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound] at hfield
    exact A.rule.all_args_outer_fresh param hfield
      (List.mem_append_left _ (List.mem_append_left _ hparam))
  have hfieldLength : A.semantics.fieldOpening.fvars.length =
      fieldDomains.length := by
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound, hfields]
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  have hsource := Expr.abstractList_after_inner
    (e := A.rule.target) (outer := A.rule.params_bound.fvars)
    (inner := A.semantics.fieldOpening.fvars) (k := 0) hparamsFields
  have hsource' :
      ((A.rule.target.abstractList A.semantics.fieldOpening.fvars).abstractList
          A.rule.params_bound.fvars fieldDomains.length) =
        A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.semantics.fieldOpening.fvars) := by
    simpa [hfieldLength] using hsource
  simp only [List.reverse_reverse] at Hclosed
  rw [hsource'] at Hclosed
  simpa [parameterDecls, List.reverse_reverse] using Hclosed

/-- Close the cached common parameters around the already closed constructor
field target.  This preserves the exact strict target translation, including
indices containing projections, while replacing every production free
variable by its canonical de Bruijn binder. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCachedConstructorTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult : VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains) [])
          (A.rule.target.abstractList
            (A.rule.params_bound.fvars ++
              A.semantics.fieldOpening.fvars))
          fieldResult := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, fieldDomains, fieldResult, _introTarget, _hparams, hfields,
      _Htail, HfieldResidual, _HtailType, _HtailTypeT, _HfieldContext,
      _HintroType, _Hintro, _HintroShape⟩
  exact ⟨T, fieldDomains, fieldResult, hfields,
    A.cachedConstructorTargetOfFieldFrame fieldDomains fieldResult hfields
      HfieldResidual⟩

/-- The lift introduced between parameters and fields is exactly simultaneous
abstraction over the rule's complete parameter/motive/minor/field binder list.
This follows from strict-translation scoping: the constructor result can only
mention parameters and genuine fields, hence motives and minors merely shift
the already abstracted parameter variables. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.canonicalTargetBinderLift_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Htarget : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (((R.materializedFinal.parameterSuffix.toRecursorContext
            H.elimLevelAdmissible).parameterDecls.toCtx.reverse) ++
          fieldDomains) [])
      (A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.semantics.fieldOpening.fvars))
      fieldResult) :
    ((A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.semantics.fieldOpening.fvars)).liftLooseBVars'
      A.rule.allArgs.size (T.motives ++ T.minors).length) =
      A.rule.target.abstractList A.rule.binders := by
  let params := A.rule.params_bound.fvars
  let motives := A.rule.motives_bound.fvars
  let minors := A.rule.minors_bound.fvars
  let fields := A.semantics.fieldOpening.fvars
  let middle := motives ++ minors
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  have hparamsLength : params.length = stats.params.size := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    simpa [params] using h.symm
  have hfieldsLength : fields.length = A.rule.allArgs.size := by
    change A.semantics.fieldOpening.fvars.length = A.rule.allArgs.size
    rw [A.semantics.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound]
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  have hparameterDeclsLength : parameterDecls.toCtx.length =
      stats.params.size := by
    have hcached := H.parameterSuffix.cached
    have h :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        hcached
    calc
      parameterDecls.toCtx.length = parameterDecls.length := by
        simpa [parameterDecls, H.parameterDecls] using h
      _ = stats.params.size := by
        simpa [parameterDecls, H.parameterDecls] using
          H.parameterSuffix.parameterDecls_length
  have hparamsFields : (params ++ fields).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1,
      A.semantics.fieldOpening.nodup, ?_⟩
    intro param hparam field hfield heq
    subst field
    have hfield' : param ∈ A.rule.all_args_bound.fvars := by
      simpa [fields, A.semantics.fieldOpening.fvars_eq_bound
        A.rule.all_args_bound] using hfield
    exact A.rule.all_args_outer_fresh param hfield'
      (List.mem_append_left _ (List.mem_append_left _ hparam))
  have hsourceClosed : Closed
      (A.rule.target.abstractList (params ++ fields))
      (params ++ fields).length := by
    have hclosed := Htarget.closed
    simpa [params, fields, VLCtx.bvars,
      parameterDecls, hparamsLength, hfieldsLength, hfields,
      hparameterDeclsLength] using hclosed
  have htargetClosed : Closed A.rule.target 0 :=
    Expr.closed_of_abstractList (e := A.rule.target)
      (fvars := params ++ fields) (depth := 0) (by
        simpa using hsourceClosed)
  have hsourceFVars :
      (A.rule.target.abstractList (params ++ fields)).FVarsIn
        (fun _ => False) := by
    have hfvars := Htarget.fvarsIn
    simpa [abstractForallContext, VLCtx.fvars, params, fields,
      parameterDecls] using hfvars
  have htargetFVars : A.rule.target.FVarsIn
      (fun fv => fv ∈ params ++ fields) := by
    exact (FVarsIn.of_abstractList hsourceFVars).mono fun fv h => by
      simpa using h
  have houterSplit := List.nodup_append.mp A.rule.outer_binders_nodup
  have hparamsMotivesSplit :=
    List.nodup_append.mp houterSplit.1
  have htargetAvoidsMiddle : A.rule.target.FVarsIn
      (fun fv => fv ∉ middle) := by
    apply htargetFVars.mono
    intro fv hfv hmiddle
    rcases List.mem_append.mp hfv with hparam | hfield
    · rcases List.mem_append.mp hmiddle with hmotive | hminor
      · exact hparamsMotivesSplit.2.2 fv hparam fv hmotive rfl
      · exact houterSplit.2.2 fv
          (List.mem_append_left _ hparam) fv hminor rfl
    · have hfield' : fv ∈ A.rule.all_args_bound.fvars := by
        simpa [fields, A.semantics.fieldOpening.fvars_eq_bound
          A.rule.all_args_bound] using hfield
      apply A.rule.all_args_outer_fresh fv hfield'
      rcases List.mem_append.mp hmiddle with hmotive | hminor
      · exact List.mem_append_left _
          (List.mem_append_right _ hmotive)
      · exact List.mem_append_right _ hminor
  have hmiddleAbstract : A.rule.target.abstractList middle = A.rule.target :=
    htargetAvoidsMiddle.abstractList_eq_self htargetClosed
  let targetFields := A.rule.target.abstractList fields
  have hparamsFieldsShape :
      targetFields.abstractList params fields.length =
        A.rule.target.abstractList (params ++ fields) := by
    simpa [targetFields] using Expr.abstractList_after_inner
      (e := A.rule.target) (outer := params) (inner := fields) (k := 0)
      hparamsFields
  have htargetFieldsClosed : Closed targetFields fields.length := by
    apply Expr.closed_of_abstractList
    rw [hparamsFieldsShape]
    simpa [List.length_append, Nat.add_comm] using hsourceClosed
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := targetFields) (fvars := params) (depth := fields.length)
    (extra := middle.length) htargetFieldsClosed
    (List.nodup_append.mp
      (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have hfullShape := Expr.abstractList_after_inner
    (e := A.rule.target) (outer := params)
    (inner := middle ++ fields) (k := 0) (by
      simpa [params, motives, minors, fields, middle,
        A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound,
        BoundGeneratedRecursorRule.binders, List.append_assoc] using
        A.rule.binders_nodup)
  rw [Expr.abstractList_append, hmiddleAbstract] at hfullShape
  have hmiddleLength : middle.length =
      (T.motives ++ T.minors).length := by
    have hm : motives.length = (H.recInfos.map (·.motive)).size := by
      have h := congrArg Array.size A.rule.motives_bound.expressions
      simpa [motives] using h.symm
    have hmi : minors.length =
        (H.recInfos.flatMap (·.minors)).size := by
      have h := congrArg Array.size A.rule.minors_bound.expressions
      simpa [minors] using h.symm
    simp [middle, hm, hmi, T.motives_length, T.minors_length]
  have hfullShape' :
      targetFields.abstractList params (fields.length + middle.length) =
        A.rule.target.abstractList (params ++ (middle ++ fields)) := by
    simpa [targetFields, List.length_append, Nat.add_comm,
      List.append_assoc] using hfullShape
  calc
    (A.rule.target.abstractList (params ++ fields)).liftLooseBVars'
        A.rule.allArgs.size (T.motives ++ T.minors).length =
        (targetFields.abstractList params fields.length).liftLooseBVars'
          fields.length middle.length := by
            rw [hparamsFieldsShape, hfieldsLength, hmiddleLength]
    _ = targetFields.abstractList params (fields.length + middle.length) :=
      hshift.symm
    _ = A.rule.target.abstractList (params ++ (middle ++ fields)) :=
      hfullShape'
    _ = A.rule.target.abstractList A.rule.binders := by
      simp [BoundGeneratedRecursorRule.binders, params, motives, minors,
        fields, middle,
        A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound,
        List.append_assoc]

/-- Insert motives and minors beneath the closed constructor fields while
retaining a strict translation of the constructor result.  The source lift
is the precise de Bruijn effect of the otherwise unused generated binders. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCachedConstructorEquationTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult : VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCachedConstructorTarget with
    ⟨T, originalDomains, fieldResult, hfields, Htarget⟩
  let inserted := T.motives ++ T.minors
  let fieldDomains :=
    (liftContextPrefix inserted.length originalDomains.reverse).reverse
  have W := abstractForallContext.bvInsertBeforeInner
    parameterDecls.toCtx.reverse inserted originalDomains
  have Hweak := Htarget.weakBV H.outVEnvWF.ordered W
  have hsource := A.canonicalTargetBinderLift_eq
    T originalDomains fieldResult hfields Htarget
  have hsource' :
      ((A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.semantics.fieldOpening.fvars)).liftLooseBVars'
        originalDomains.length inserted.length) =
        A.rule.target.abstractList A.rule.binders := by
    simpa [inserted, hfields] using hsource
  rw [hsource'] at Hweak
  have hfieldDomains : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, hfields]
  exact ⟨T, fieldDomains, fieldResult, hfieldDomains, by
    simpa [parameterDecls, inserted, fieldDomains, hfields,
      List.append_assoc] using Hweak⟩

/-- Invert a cached constructor target belonging to a fixed recursor
telescope.  Keeping `T` explicit is essential when the resulting index spine
is consumed by the matching recursor suffix. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.cachedConstructorIndexSpineOfTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Htarget :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let parameterDecls :=
        (R.materializedFinal.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      TrExprS H.outVEnv Us
        (abstractForallContext
          ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains) [])
        (A.rule.target.abstractList A.rule.binders)
        (fieldResult.liftN
          (T.motives ++ T.minors).length A.rule.allArgs.size)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
        (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size).getAppFnArgs =
          (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
            parameterTargets ++ indexTargets) ∧
        stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          ((stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          parameterTargets ∧
        indexTargets.length = T.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  dsimp only at Htarget
  have hvalid : AddInductive.isValidIndAppIdx stats A.rule.target owner =
      true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.semantics.target_valid).2
    simpa [A.semantic_owner] using h
  have hconst := A.semantics.validStats.indConstAt A.abstractOwner_lt
  have hhead : A.rule.target.getAppFn =
      .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead hvalid hconst
  have hheadAbstract :
      (A.rule.target.abstractList A.rule.binders).getAppFn =
        .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels := by
    rw [Expr.getAppFn_abstractList, hhead]
    induction A.rule.binders <;> simp_all [Expr.abstractList, Expr.abstract1]
  rcases checkPositivityStep.TrExprS.constAppSpine Htarget hheadAbstract with
    ⟨levels, translatedArgs, hspine, hlevels, Hargs⟩
  let indices := (AddInductive.getIIndices stats A.rule.target).2
  have hsourcePrefix := A.semantics.validStats.sourceParameterPrefix hvalid
  have hsourceArgs :
      (A.rule.target.abstractList A.rule.binders).getAppArgsList =
        (stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList ++
          (indices.map fun arg =>
            arg.abstractList A.rule.binders).toList := by
    rw [Expr.getAppArgsList_abstractList]
    have hsplit : A.rule.target.getAppArgsList =
        stats.params.toList ++ indices.toList := by
      calc
        A.rule.target.getAppArgsList =
            A.rule.target.getAppArgsList.take stats.params.size ++
              A.rule.target.getAppArgsList.drop stats.params.size :=
          (List.take_append_drop _ _).symm
        _ = stats.params.toList ++ indices.toList := by
          rw [hsourcePrefix]
          congr 1
          have hsuffix :
              (A.rule.target.getAppArgs[stats.params.size:]).toList =
                A.rule.target.getAppArgs.toList.drop stats.params.size := by
            rw [List.drop_eq_drop_min]
            simp only [Subarray.toList_eq, Array.array_toSubarray,
              Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
              Array.toList_extract, List.extract_eq_take_drop,
              Array.length_toList]
            apply List.take_of_length_le
            simp
          simpa [indices, AddInductive.getIIndices,
            Expr.getAppArgs_toList] using hsuffix.symm
    rw [hsplit]
    simp
  rw [hsourceArgs] at Hargs
  rcases checkPositivityStep.List.Forall₂.split_left Hargs with
    ⟨parameterTargets, indexTargets, htranslatedArgs,
      HparameterTargets, HindexTargets⟩
  have hindicesLength : indices.size = stats.nindices[owner]! := by
    exact checkPositivityStep.getIIndices.index_arity
      A.semantics.target_valid |>.trans (by simp [A.semantic_owner])
  have hindexTargetsLength : indexTargets.length = T.indices.length := by
    have htranslated :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' HindexTargets
    have harity := H.arities owner (by
      simpa [H.generated.length] using howner)
    rw [T.indices_length, harity, ← hindicesLength]
    simpa [indices] using htranslated.symm
  refine ⟨levels, parameterTargets, indexTargets, ?_, hlevels,
    HparameterTargets, hindexTargetsLength, ?_⟩
  · simpa [htranslatedArgs] using hspine
  · simpa [indices] using HindexTargets

/-- Invert the fully abstracted constructor result at its validated family
head.  This exposes the exact translated index suffix in the equation
context, without imposing any syntactic restriction on index expressions. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCachedConstructorIndexSpine
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult : VExpr)
          (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size).getAppFnArgs =
          (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
            parameterTargets ++ indexTargets) ∧
        stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          ((stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          parameterTargets ∧
        indexTargets.length = T.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCachedConstructorEquationTarget with
    ⟨T, fieldDomains, fieldResult, hfields, Htarget⟩
  rcases A.cachedConstructorIndexSpineOfTarget
      T fieldDomains fieldResult hfields Htarget with
    ⟨levels, parameterTargets, indexTargets, hspine, hlevels,
      HparameterTargets, hindexLength, HindexTargets⟩
  exact ⟨T, fieldDomains, fieldResult, levels, parameterTargets,
    indexTargets, hfields, Htarget, hspine, hlevels, HparameterTargets,
    hindexLength, HindexTargets⟩

/-- Apply the checked constructor to the canonical variables of its genuine
field telescope.  This is done before inserting motives and minors, avoiding
any pointwise formula for lifting dependent field domains. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorFieldApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        fieldDomains.length = A.rule.allArgs.size ∧
        H.outVEnv.HasType Us.length
          (fieldDomains.reverse ++ T.params.reverse)
          (VExpr.mkApps (introTarget.liftN fieldDomains.length 0)
            (recursorCanonicalVars fieldDomains.length))
          fieldResult := by
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, fieldDomains, fieldResult, introTarget, _hparams, hfields,
      _Htail, _HfieldResidual, _HtailType, _HtailTypeT, _HfieldContext,
      HintroType, _Hintro, _HintroShape⟩
  have Happ := VEnv.HasType.mkApps_wrapForalls_canonical
    H.outVEnvWF.ordered HintroType
  exact ⟨T, fieldDomains, fieldResult, introTarget, hfields, by
    simpa [recursorCanonicalVars] using Happ⟩

/-- Insert the generated motive/minor block beneath the genuine constructor
fields.  `fieldDomains` is rebuilt from the lifted context prefix, so the
resulting canonical equation context remains valid for dependent fields. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorEquationContextWithFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (originalDomains fieldDomains : List VExpr)
          (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.semantics.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (recursorCanonicalVars A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (recursorCanonicalVars stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T, originalDomains, fieldResult, introTarget, hparams, hfields,
      Htail, HfieldResidual, _HtailType, HtailTypeT, HfieldContext,
      HintroType, _Hintro, HintroShape⟩
  have HcachedTarget := A.cachedConstructorTargetOfFieldFrame
    originalDomains fieldResult hfields HfieldResidual
  let inserted := T.motives ++ T.minors
  have Wtarget := abstractForallContext.bvInsertBeforeInner
    parameterDecls.toCtx.reverse inserted originalDomains
  have HtargetWeak := HcachedTarget.weakBV H.outVEnvWF.ordered Wtarget
  have hsource := A.canonicalTargetBinderLift_eq
    T originalDomains fieldResult hfields HcachedTarget
  have hsource' :
      ((A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.semantics.fieldOpening.fvars)).liftLooseBVars'
        originalDomains.length inserted.length) =
        A.rule.target.abstractList A.rule.binders := by
    simpa [inserted, hfields] using hsource
  rw [hsource'] at HtargetWeak
  have Happ := VEnv.HasType.mkApps_wrapForalls_canonical
    H.outVEnvWF.ordered HintroType
  let added := inserted.reverse
  let liftedPrefix := liftContextPrefix inserted.length originalDomains.reverse
  let fieldDomains := liftedPrefix.reverse
  have W : Ctx.LiftN inserted.length originalDomains.reverse.length
      (originalDomains.reverse ++ T.params.reverse)
      (liftedPrefix ++ added ++ T.params.reverse) := by
    simpa [liftedPrefix, added] using
      Ctx.LiftN.insertAfterPrefix originalDomains.reverse added T.params.reverse
  have Hweak := Happ.weakN H.outVEnvWF.ordered W
  have W0 : Ctx.LiftN inserted.length 0 T.params.reverse
      (added ++ T.params.reverse) := by
    exact .zero added (by simp [added])
  have HliftedType := HtailTypeT.weakN H.outVEnvWF.ordered W0
  rw [VExpr.liftN_wrapForalls] at HliftedType
  have hbase : OnCtx (added ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [added, inserted, List.reverse_append, List.append_assoc] using
      T.prefixContext H.outVEnvWF.ordered
  have Hcontext : OnCtx
      (liftedPrefix ++ added ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
      hbase HliftedType
    simpa [liftedPrefix, liftContextPrefix] using Hopened.1
  have hfieldDomains : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, liftedPrefix, hfields]
  refine ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
    hparams, hfields, ?_, Htail, HfieldContext, hfieldDomains, ?_, ?_, ?_,
    HintroShape⟩
  · simp [fieldDomains, liftedPrefix, inserted]
  · simpa [fieldDomains, liftedPrefix, added, inserted, List.reverse_append,
      List.append_assoc] using Hcontext
  · simpa [fieldDomains, liftedPrefix, added, inserted, hfields, List.reverse_append,
      List.append_assoc, Nat.add_comm, recursorCanonicalVars] using Hweak
  · simpa [parameterDecls, inserted, fieldDomains, liftedPrefix, added,
      hfields, List.append_assoc] using HtargetWeak

/-- Weaken the checked constructor major below the generated motive/minor
prefix.  The explicit lift is the de Bruijn shift later field and equation
terms must share; retaining it here prevents an implicit context-extension
assumption from entering iota typing. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCheckedConstructorPrefixApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (tailTarget introTarget : VExpr),
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        H.outVEnv.HasType Us.length
          (T.params ++ T.motives ++ T.minors).reverse
          (introTarget.liftN (T.motives ++ T.minors).length 0)
          (tailTarget.liftN (T.motives ++ T.minors).length 0) := by
  rcases A.finalCheckedConstructorApplication with
    ⟨T, tailTarget, introTarget, Hintro, _HintroShape, HintroType⟩
  let added := (T.motives ++ T.minors).reverse
  have W0 : Ctx.LiftN added.length 0 T.params.reverse
      (added ++ T.params.reverse) := .zero added
  have W : Ctx.LiftN added.length 0 T.params.reverse
      ((T.params ++ T.motives ++ T.minors).reverse) := by
    simpa [added, List.reverse_append, List.append_assoc] using W0
  refine ⟨T, tailTarget, introTarget, Hintro, ?_⟩
  simpa [added, Nat.add_comm] using
    HintroType.weakN H.outVEnvWF.ordered W

/-- The terminal inductive application retained by rule generation consumes
the same index telescope as the motive introduced by the first recursor
pass.  The exact root-to-constructor context extension is retained in the
semantic rule package, so this statement does not reconstruct motive
bindings or rerun positivity validation. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.semanticMotiveTelescopeEvidence
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ binding : RecursorMotiveBinding A.semantics.context
        H.recInfos[owner]! H.elimLevel,
      Nonempty (RecursorMotiveTelescopeEvidence A.semantics.context stats
        H.recInfos[owner]! binding A.rule.target
        A.semantics.targetTarget) := by
  rcases A.motiveEvidence with ⟨Hmotive⟩
  have Hpair : ∃ binding : RecursorMotiveBinding A.semantics.context
        H.recInfos[A.semantics.ownerIdx]! H.elimLevel,
      Nonempty (RecursorMotiveTelescopeEvidence A.semantics.context stats
        H.recInfos[A.semantics.ownerIdx]! binding A.rule.target
        A.semantics.targetTarget) := ⟨Hmotive.binding, Hmotive.telescope⟩
  rw [A.semantic_owner] at Hpair
  exact Hpair

/-- The permutation-free first-pass motive telescope is retained through the
complete mutual and constructor passes and transported to the final constant
environment.  Its only ambient binders are the common parameters, matching
the grouped prefix of `GeneratedRecursorTelescopeTranslation`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalPairedMotiveSeed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let parameterCtx :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.recursorWF.venv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        S.canonical.params.reverse parameterCtx := by
  dsimp only
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  exact H.motiveTelescopes.seed owner hrecInfo

/-- Final-environment form of the retained paired motive seed.  The concrete
source is exactly the production index/major telescope, while the two target
expressions remain linked by the independently proved first-pass
definitional equality. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalPairedMotiveTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterCtx :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          S.canonical.params.reverse parameterCtx ∧
      TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
        (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
          (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
            (.sort H.elimLevel)))
        S.motiveActualType ∧
      H.outVEnv.IsDefEqU Us.length H.recursorWF.mlctx.vlctx.toCtx
        S.motiveActualType S.motiveType := by
  dsimp only
  rcases A.finalPairedMotiveSeed with ⟨S, hparams⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact VEnv.addProjections_le.trans H.installed.le
  exact ⟨S, hparams.mono hbase, S.motiveTypeTr.mono hbase,
    S.motiveTypeDefEq.mono hbase⟩

theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMotiveTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let parameterCtx :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams) stats
        decl owner H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        C.params.reverse parameterCtx := by
  dsimp only
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  rcases H.motiveTelescopes.seed owner hrecInfo with ⟨S, hparams⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact VEnv.addProjections_le.trans H.installed.le
  exact ⟨S.canonical.mono hbase, hparams.mono hbase⟩

/-- Owner-indexed form of `finalCanonicalMotiveTelescope`, independent of a
particular generated equation rule. -/
theorem CompletedRecursorPhasesResult.finalCanonicalMotiveTelescopeAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let parameterCtx :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
    ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams) stats
        decl owner H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        C.params.reverse parameterCtx := by
  dsimp only
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  rcases H.motiveTelescopes.seed owner hrecInfo with ⟨S, hparams⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact VEnv.addProjections_le.trans H.installed.le
  exact ⟨S.canonical.mono hbase, hparams.mono hbase⟩

end VerifyInductive
end Lean4Lean
