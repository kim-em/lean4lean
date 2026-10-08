import Lean4Lean.Verify.Inductive.Equation.RecursiveApplication

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The local translation of a reconstructed equation determines its full
iota-equation certificate at the canonical owner/constructor selected by the
generated-rule alignment.  Recursor identity and arity come from the installed
recursor certificate; constructor identity comes from source translation. -/
theorem RecursorPhasesResult.GeneratedRuleAlignment.iotaEquationTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    {rule : VDefEq}
    (Htr : A.rule.EquationTranslation H.outVEnv Us Delta rule)
    (hruleUvars : rule.uvars = H.entries[owner].2.uvars) :
    Nonempty (A.rule.IotaEquationTranslationCertificate H.outVEnv Us Delta
      decl (H.blockCertificate rules hrules).block
      (decl.types[owner]'A.abstractOwner_lt)
      ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt)
      rule) := by
  let recursor := H.entries[owner].2
  let E := H.generated.entry owner howner
  have hrecursorMem : recursor ∈
      (H.blockCertificate rules hrules).block.recursors := by
    change recursor ∈ H.entries.map Prod.snd
    exact List.mem_map.mpr
      ⟨H.entries[owner], List.getElem_mem howner, rfl⟩
  have hrecursorIndex : owner < (H.entries.map Prod.snd).length := by
    simpa using howner
  rcases (H.generatedCertificate.recursorCertificate H.localWF H.bindings
      H.params H.noAlias H.cardinality R.core).shapes owner
      A.abstractOwner_lt hrecursorIndex with ⟨Hshape⟩
  have hrecursorName : recursor.name =
      decl.recursorName (decl.types[owner]'A.abstractOwner_lt) := by
    simpa [recursor] using Hshape.name
  have hrecursorUvars :
      (AddInductive.getRecLevels H.elimLevel stats.levels).length =
        recursor.uvars := by
    have htranslated : E.info.levelParams.length = recursor.uvars := by
      simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal, E,
        recursor] using E.translated.1.2.1
    have hrecParams :
        (AddInductive.getRecLevelParams H.elimLevel
          H.localContext.lparams).length = recursor.uvars :=
      (congrArg List.length E.levels).symm.trans htranslated
    have hstatsLevels : stats.levels.length = c.lparams.length :=
      A.semantics.validStats.levels.trans R.core.uvars
    have hlocalLevels : H.localContext.lparams.length = c.lparams.length := by
      rw [H.localExtends.lparams_eq]
    have hadmissible := H.elimLevelAdmissible
    cases hElim : H.elimLevel <;>
      simp_all [AddInductive.getRecLevels, AddInductive.getRecLevelParams,
        AddInductive.AdmissibleElimLevel, Level.isParam]
  rcases htarget : AddInductive.getIIndices stats A.rule.target with
    ⟨selectedOwner, indices⟩
  have hselectedOwner : selectedOwner = owner := by
    have hfirst := checkPositivityStep.getIIndices.fst_eq_of_valid
      A.semantics.target_valid
    rw [htarget] at hfirst
    exact hfirst.trans A.semantic_owner
  subst selectedOwner
  have hselectedLt : owner < decl.types.length := by
    exact A.abstractOwner_lt
  have hindices : indices.size =
      (decl.types[owner]'A.abstractOwner_lt).numIndices := by
    have harity := checkPositivityStep.getIIndices.index_arity
      A.semantics.target_valid
    rw [htarget, A.semantic_owner] at harity
    have hlen : stats.nindices.size = decl.types.length := by
      have := congrArg List.length A.semantics.validStats.indices
      simpa using this
    have hget := congrArg (fun xs => xs[owner]?)
      A.semantics.validStats.indices
    have hn : stats.nindices[owner]! =
        (decl.types[owner]'A.abstractOwner_lt).numIndices := by
      simpa [Array.getElem!_eq_getD, Array.getD, A.abstractOwner_lt, hlen]
        using hget
    exact harity.trans hn
  apply A.rule.iotaEquationCertificate (ownerIdx := owner)
    (indices := indices) (recursor := recursor)
    (ctor := (decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt)
    Htr htarget H.cardinality.params H.cardinality.motives
    H.cardinality.minors hindices
  · simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using
      A.ownerTranslation.header.name.symm
  · exact hrecursorMem
  · exact hrecursorName
  · exact hrecursorUvars
  · simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using
      A.ctorTranslation.name.symm
  · exact A.semantics.validStats.levels
  · simpa [recursor] using hruleUvars

/-- Recover the complete staged iota payload for one generated source rule
from the concrete equation translation alone.  The recursor phase retains
the semantic call trace for the same rule; global installation supplies both
freshness in the constructor environment and presence in the final block. -/
theorem RecursorPhasesResult.stagedIotaRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (Us : List Name) (Delta : VLCtx)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (ownerType : VInductiveType) (ctor : VConstVal) (rule : VDefEq)
    (Hequation : A.rule.IotaEquationTranslationCertificate H.outVEnv Us Delta
      decl (H.blockCertificate rules hrules).block ownerType ctor rule)
    (hctx : VLCtx.NoIndConsts
      ((H.blockCertificate rules hrules).block.recursors.map (·.name)) Delta) :
    Nonempty (A.rule.StagedIotaRuleTranslation H.outVEnv Us Delta
      ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries) decl (H.blockCertificate rules hrules).block
      ownerType ctor rule) := by
  have hfreshRoot : ∀ name ∈
      (H.blockCertificate rules hrules).block.recursors.map (·.name),
      H.recursorWF.venv.constants name = none := by
    rw [H.recursorEnv_legacy, R.declared.contextVEnv]
    simpa using H.recursorNamesFresh rules hrules
  have hrootVEnv : H.recursorWF.venv =
      (R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries :=
    H.recursorEnv_legacy.trans R.declared.contextVEnv
  have hstaged := A.rule.stagedIotaRuleTranslation_ofSemantics A.semantics
    Hequation hfreshRoot hctx (by
      intro i hi _originRoot _callDepth _Rorigin S
      have hstats : S.generated.ownerIdx < stats.indConsts.size :=
        (checkPositivityStep.isValidIndApp?_some
          S.generated.owner_valid).1
      have hdeclOwner : S.generated.ownerIdx < decl.types.length := by
        rwa [H.cardinality.families] at hstats
      have hsourceOwner : S.generated.ownerIdx < indTypes.size := by
        have htypes : indTypes.size = decl.types.length := by
          simpa using
            Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
        rwa [htypes]
      rw [S.generated.recursorName_eq_owner]
      exact H.generatedCertificate.recursorName_mem_block
        (H.blockCertificate rules hrules).block (by
          rw [H.cardinality.records]
          simpa using
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              R.core).symm)
        rfl S.generated.ownerIdx hsourceOwner)
  simpa only [hrootVEnv] using hstaged

/-- Equation-only payload for the generated rule batches of a completed
recursor phase.  Unlike `GeneratedIotaTranslations`, this boundary does not
ask its caller to reconstruct field selection or recursive-result semantics:
each equation is paired with the exact retained semantic rule alignment. -/
inductive RecursorPhasesResult.GeneratedIotaEquationTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (Us : List Name) (Delta : VLCtx) :
    Nat → List VDefEq → Prop
  | nil : H.GeneratedIotaEquationTranslations Us Delta 0 []
  | cons
      (Hprior : H.GeneratedIotaEquationTranslations Us Delta owner prior)
      (howner : owner < H.entries.length)
      (batch : List VDefEq)
      (hlength : batch.length =
        (H.generated.entry owner howner).info.rules.length)
      (hroom : batch.length + prior.length ≤
        decl.ownedConstructors.length)
      (equations : ∀ i
        (hctor : i < indTypes[owner]!.ctors.length)
        (hsource : i <
          (H.generated.entry owner howner).info.rules.length)
        (habstract : i < batch.length)
        (hindex : prior.length + i < decl.ownedConstructors.length),
        ∃ A : H.GeneratedRuleAlignment owner howner i hctor,
          Nonempty (A.rule.EquationTranslation H.outVEnv Us Delta batch[i]) ∧
          batch[i].uvars = H.entries[owner].2.uvars) :
      H.GeneratedIotaEquationTranslations Us Delta (owner + 1)
        (prior ++ batch)

/-- Equation-only traversal has the same flattened rule count as the
concrete mutual-family prefix it covers. -/
theorem RecursorPhasesResult.GeneratedIotaEquationTranslations.ruleLength
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {Us : List Name} {Delta : VLCtx}
    (T : H.GeneratedIotaEquationTranslations Us Delta owner rules) :
    rules.length = recursorMinorOffset indTypes owner := by
  induction T with
  | nil => simp [recursorMinorOffset]
  | @cons actualOwner actualPrior Hprior howner batch hlength _hroom
      _equations ih =>
    let E := H.generated.entry actualOwner howner
    have hsourceOwner : actualOwner < indTypes.size := by
      have hrec : actualOwner < H.recInfos.size := by
        simpa [H.generated.length] using howner
      have htypes : H.recInfos.size = indTypes.size := by
        rw [H.cardinality.records]
        simpa using
          (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      omega
    have hrules : E.info.rules.length =
        indTypes[actualOwner]!.ctors.length := E.rules.length
    simp only [List.length_append]
    rw [hlength, hrules, ih,
      recursorMinorOffset_step indTypes actualOwner hsourceOwner]

/-- Convert the equation-only traversal into the independent iota build
certificate.  All semantic payload is recovered pointwise from the completed
recursor phase. -/
theorem RecursorPhasesResult.GeneratedIotaEquationTranslations.build
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {Us : List Name} {Delta : VLCtx}
    (T : H.GeneratedIotaEquationTranslations Us Delta owner rules)
    (allRules : List VDefEq)
    (allRulesWF : ∀ df ∈ allRules, df.WF H.outVEnv)
    (hctx : VLCtx.NoIndConsts
      ((H.blockCertificate allRules allRulesWF).block.recursors.map (·.name))
      Delta) :
    IotaBuildCertificate ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries) decl
      (H.blockCertificate allRules allRulesWF).block rules := by
  induction T with
  | nil => exact .empty _ _ _
  | @cons actualOwner actualPrior Hprior howner batch hlength hroom
      equations ih =>
    apply ih.append hroom
    intro i habstract
    let E := H.generated.entry actualOwner howner
    have hsource : i < E.info.rules.length := by
      change i < (H.generated.entry actualOwner howner).info.rules.length
      rw [← hlength]
      exact habstract
    have hctor : i < indTypes[actualOwner]!.ctors.length := by
      rw [← E.rules.length]
      exact hsource
    have hindex : actualPrior.length + i <
        decl.ownedConstructors.length := by omega
    rcases equations i hctor hsource habstract hindex with
      ⟨A, ⟨Htranslation⟩, hruleUvars⟩
    rcases A.iotaEquationTranslation allRules allRulesWF Htranslation
        hruleUvars with ⟨Hequation⟩
    rcases H.stagedIotaRuleTranslation allRules allRulesWF Us Delta
        actualOwner howner i hctor A
        (decl.types[actualOwner]'A.abstractOwner_lt)
        ((decl.types[actualOwner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt)
        batch[i]
        Hequation hctx with ⟨Hstaged⟩
    have hpriorOffset : actualPrior.length =
        recursorMinorOffset indTypes actualOwner := Hprior.ruleLength
    have hminorIndex : recursorMinorOffset indTypes actualOwner + i <
        decl.ownedConstructors.length := by
      simpa [hpriorOffset] using hindex
    have howned :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructorAtMinorOffset
        R.core actualOwner i A.sourceOwner_lt hctor A.abstractOwner_lt
        A.abstractCtor_lt hminorIndex
    have hownedPrior :
        decl.ownedConstructors[actualPrior.length + i]'hindex =
          (decl.types[actualOwner]'A.abstractOwner_lt,
            (decl.types[actualOwner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt) := by
      simpa [hpriorOffset] using howned
    rw [hownedPrior]
    exact A.rule.iotaRule_ofStagedTranslation Hstaged

theorem RecursorPhasesResult.GeneratedIotaEquationTranslations.completeLength
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {Us : List Name} {Delta : VLCtx}
    (T : H.GeneratedIotaEquationTranslations Us Delta owner rules)
    (hcomplete : owner = H.entries.length) :
    rules.length = decl.ownedConstructors.length := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have howner : owner = indTypes.size := by
    rw [hcomplete, H.generated.length, H.cardinality.records, ← htypes]
  rw [T.ruleLength, howner]
  have hoffset : recursorMinorOffset indTypes indTypes.size =
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
    unfold recursorMinorOffset
    simp only [List.length_flatMap]
    have hlen : indTypes.size =
        (indTypes.toList.map (fun type => type.ctors.length)).length := by
      simp
    rw [hlen, List.map_take, List.take_length]
  rw [hoffset]
  simpa [ownedConstructors, List.length_flatMap] using
    Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length R.core

/-- The complete recursor phase determines every ordinary-compilation field
except the semantic interpretation of its generated iota-rule batch. Block
layout and name uniqueness are consequences of the staging certificate. -/
theorem RecursorPhasesResult.ordinaryCompilationOfRuleBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (Hrules : IotaBuildCertificate
      ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries) decl
      (H.blockCertificate rules hrules).block rules)
    (hrulesLength : rules.length = decl.ownedConstructors.length) :
    OrdinaryShapeCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block := by
  let Hgenerated : GeneratedRecursors c.safety
      ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries) c.lparams
      H.elimLevel H.localContext stats indTypes H.recInfos H.entries := by
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  apply Hgenerated.ordinaryCompilationCertificate_ofRuleBuild H.localWF
    H.bindings H.params H.noAlias H.cardinality R.core
  · exact Hheaders.values
  · exact R.declared.values
  · rfl
  · rfl
  · exact Hrules
  · simpa [BlockCertificate.block] using hrulesLength
  · exact (H.blockCertificate rules hrules).names

/-- Close ordinary compilation from the exact per-owner generated-rule
translations.  Mutual traversal order, flattened constructor coverage, and
the final rule count are derived from `GeneratedRecursors`; callers retain
only the local executable-to-abstract translation payload. -/
theorem RecursorPhasesResult.ordinaryCompilationOfRuleTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (Us : List Name) (Δ : VLCtx)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv)
    (owner : Nat)
    (Htranslations : GeneratedIotaTranslations H.generatedCertificate
      ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries) H.outVEnv Us Δ decl
      (H.blockCertificate rules hrules).block owner rules)
    (hcomplete : owner = H.entries.length) :
    OrdinaryShapeCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block := by
  have Hbuild : IotaBuildCertificate ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries) decl
      (H.blockCertificate rules hrules).block rules :=
    Htranslations.build H.generatedCertificate H.cardinality R.core rfl
  have hlength : rules.length = decl.ownedConstructors.length :=
    Htranslations.completeLength H.generatedCertificate H.cardinality R.core
      hcomplete
  exact H.ordinaryCompilationOfRuleBuild rules hrules Hbuild hlength

/-- The exact remaining pointwise payload for constructing an ordinary
specification equation.  Unlike the earlier batch interface, this witness is
independent of the eventual rule list and block: it contains one reconstructed
`VDefEq`, its executable-source translation, and the typing proof required by
`VInductBlock.WF`. -/
structure RecursorPhasesResult.GeneratedEquationWitness
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (rule : VDefEq) where
  alignment : H.GeneratedRuleAlignment owner howner i hctor
  translation : alignment.rule.EquationTranslation H.outVEnv Us [] rule
  uvars : rule.uvars = H.entries[owner].2.uvars
  wf : rule.WF H.outVEnv

/-- Canonical abstract equation assembled from the residual bodies exposed by
one generated source rule. -/
def RecursorPhasesResult.GeneratedRuleAlignment.abstractEquation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor)
    (domains : List VExpr) (lhsBody rhsBody typeBody : VExpr) : VDefEq where
  uvars := H.entries[owner].2.uvars
  lhs := VExpr.wrapLams domains lhsBody
  rhs := VExpr.wrapLams domains rhsBody
  type := VExpr.wrapForalls domains typeBody

/-- Residual translation and typing are sufficient to construct the exact
pointwise witness consumed by the flattened equation builder.  In particular,
the wrapper syntax and equation universe count are canonical rather than
caller-supplied proof obligations. -/
def RecursorPhasesResult.GeneratedRuleAlignment.equationWitnessOfBodies
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (domains : List VExpr) (lhsBody rhsBody typeBody : VExpr)
    (hdomains : domains.length = A.rule.binders.length)
    (hlhsResidual : TrExprS H.outVEnv Us
      (abstractForallContext domains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody)
    (hrhsResidual : TrExprS H.outVEnv Us
      (abstractForallContext domains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody)
    (hctx : OnCtx domains.reverse
      (H.outVEnv.IsType H.entries[owner].2.uvars))
    (hlhs : H.outVEnv.HasType H.entries[owner].2.uvars domains.reverse
      lhsBody typeBody)
    (hrhs : H.outVEnv.HasType H.entries[owner].2.uvars domains.reverse
      rhsBody typeBody) :
    H.GeneratedEquationWitness Us owner howner i hctor
      (A.abstractEquation domains lhsBody rhsBody typeBody) where
  alignment := A
  translation := {
    domains := domains
    lhsBody := lhsBody
    rhsBody := rhsBody
    typeBody := typeBody
    domains_length := hdomains
    lhs_wrapped := rfl
    rhs_wrapped := rfl
    type_wrapped := rfl
    lhs_residual := hlhsResidual
    rhs_residual := hrhsResidual }
  uvars := rfl
  wf := VDefEq.wf_of_wrappedBodies hctx hlhs hrhs

/-- The independently translated recursor prefix and the genuine constructor
field suffix have exactly the binder count retained by the production rule.
This is the shared context-length invariant for all canonical equation-body
translations. -/
theorem RecursorPhasesResult.GeneratedRuleAlignment.canonicalEquationDomains_length
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    ((T.params ++ T.motives ++ T.minors) ++ fieldDomains).length =
      A.rule.binders.length := by
  have hparams : A.rule.params_bound.fvars.length = stats.params.size := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length =
      (H.recInfos.map (·.motive)).size := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length =
      (H.recInfos.flatMap (·.minors)).size := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    simpa using h.symm
  have hallArgs : A.rule.all_args_bound.fvars.length =
      A.rule.allArgs.size := by
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  unfold BoundGeneratedRecursorRule.binders
  simp only [List.length_append]
  rw [T.params_length, T.motives_length, T.minors_length,
    hfields, hparams, hmotives, hminors, hallArgs]

/-- Replacing the executable parameter domains by the independently checked
cached parameter declarations preserves the exact production binder count.
This is the length invariant used by the final specification equation. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.cachedEquationDomains_length
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains).length = A.rule.binders.length := by
  let parameterSuffix :=
    R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible
  let parameterDecls := parameterSuffix.parameterDecls
  have hparameterDeclsLength : parameterDecls.toCtx.length =
      stats.params.size := by
    have hcached := parameterSuffix.cached
    have htoCtx :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        hcached
    calc
      parameterDecls.toCtx.length = parameterDecls.length := by
        simpa [parameterDecls, parameterSuffix] using htoCtx
      _ = stats.params.size := by
        simpa [parameterDecls, parameterSuffix] using
          parameterSuffix.parameterDecls_length
  have hcanonical := A.canonicalEquationDomains_length T fieldDomains hfields
  have hparameterDeclsLength' :
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx.length =
          stats.params.size := by
    simpa [parameterDecls, parameterSuffix] using hparameterDeclsLength
  dsimp only
  simp only [List.length_append, List.length_reverse]
  rw [hparameterDeclsLength']
  simpa only [List.length_append, T.params_length] using hcanonical

/-- Every retained source-binder group has its exact canonical de Bruijn
translation in the independently typed equation context.  Keeping the four
groups separate mirrors the two generated equation spines: the recursor uses
parameters, motives, and minors, while the constructor uses parameters and
fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalEquationBinderTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        ((stats.params.map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin stats.params.size =>
          VExpr.bvar (A.rule.binders.length - 1 - i)) ∧
      List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        (((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin (H.recInfos.map (·.motive)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            (A.rule.params_bound.fvars.length + i))) ∧
      List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        (((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin (H.recInfos.flatMap (·.minors)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            ((A.rule.params_bound.fvars ++
              A.rule.motives_bound.fvars).length + i))) ∧
      List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        ((A.rule.allArgs.map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin A.rule.allArgs.size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            (((A.rule.params_bound.fvars ++
              A.rule.motives_bound.fvars) ++
              A.rule.minors_bound.fvars).length + i))) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  exact ⟨A.rule.abstractedParamsTranslation domains [] hdomains,
    A.rule.abstractedMotivesTranslation domains [] hdomains,
    A.rule.abstractedMinorsTranslation domains [] hdomains,
    A.rule.abstractedAllArgsTranslation domains [] hdomains⟩

/-- The owner motive selected from the globally abstracted motive array has
the same de Bruijn index as the owner-motive witness obtained by weakening
the generated telescope beneath minors and constructor fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalOwnerMotiveBvarIndex
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    A.rule.binders.length - 1 -
        (A.rule.params_bound.fvars.length + owner) =
      fieldDomains.length +
        (T.motives.drop (owner + 1) ++ T.minors).length := by
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hownerRecInfo
  have hownerMotiveCount :
      owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have hparams := A.rule.params_bound.length_fvars
  have hmotives := A.rule.motives_bound.length_fvars
  have hminors := A.rule.minors_bound.length_fvars
  have hallArgs := A.rule.all_args_bound.length_fvars
  unfold BoundGeneratedRecursorRule.binders
  simp only [List.length_append, List.length_drop]
  rw [hparams, hmotives, hminors, hallArgs, hfields,
    T.motives_length, T.minors_length]
  rw [Nat.sub_sub]
  omega

/-- In the canonical equation context, the retained constructor fields close
to precisely the innermost canonical variables.  This identifies the direct
source translation with the field application typed by the framed equation
context construction. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalAllArgsTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext domains []))
      ((A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders).toList)
      (recursorCanonicalVars fieldDomains.length) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  have Htr := A.rule.abstractedAllArgsTranslation
    (env := H.outVEnv) (Us := Us) domains [] hdomains
  have hparams : A.rule.params_bound.fvars.length = T.params.length := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    rw [T.params_length]
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length = T.motives.length := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    rw [T.motives_length]
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length = T.minors.length := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    rw [T.minors_length]
    simpa using h.symm
  have htarget :
      (List.ofFn fun i : Fin A.rule.allArgs.size =>
        VExpr.bvar (A.rule.binders.length - 1 -
          (((A.rule.params_bound.fvars ++
            A.rule.motives_bound.fvars) ++
            A.rule.minors_bound.fvars).length + i))) =
        recursorCanonicalVars fieldDomains.length := by
    rw [recursorCanonicalVars_eq_ofFn]
    apply List.ext_getElem
    · simpa using hfields.symm
    · intro j hleft hright
      simp only [List.getElem_ofFn]
      congr 1
      simp only [List.length_append] at hdomains hparams hmotives hminors ⊢
      omega
  rw [← htarget]
  exact Htr

/-- The source constructor arguments close to the parameter variables shifted
below motives, minors, and fields, followed by the innermost canonical field
variables.  This is the exact spine of the independently checked constructor
major in the canonical equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalConstructorArgsTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext domains []))
      ((stats.params.map fun arg =>
          arg.abstractList A.rule.binders).toList ++
        (A.rule.allArgs.map fun arg =>
          arg.abstractList A.rule.binders).toList)
      (List.append
        ((recursorCanonicalVars T.params.length).map (fun arg =>
          arg.liftN
            ((T.motives ++ T.minors).length + fieldDomains.length) 0))
        (recursorCanonicalVars fieldDomains.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  rcases A.canonicalEquationBinderTranslations T fieldDomains hfields with
    ⟨Hp, _Hm, _Hmi, _Ha⟩
  have Ha := A.canonicalAllArgsTranslation T fieldDomains hfields
  have Htr := List.Forall₂.append' Hp Ha
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  have hparams : A.rule.params_bound.fvars.length = T.params.length := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    rw [T.params_length]
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length = T.motives.length := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    rw [T.motives_length]
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length = T.minors.length := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    rw [T.minors_length]
    simpa using h.symm
  have hallArgs : A.rule.all_args_bound.fvars.length = fieldDomains.length := by
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa [hfields] using h.symm
  have htarget :
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (A.rule.binders.length - 1 - i)) =
      (recursorCanonicalVars T.params.length).map (fun arg =>
        arg.liftN
          ((T.motives ++ T.minors).length + fieldDomains.length) 0) := by
    rw [recursorCanonicalVars_eq_ofFn]
    apply List.ext_getElem
    · simp [T.params_length]
    · intro j hleft hright
      simp only [List.getElem_ofFn, List.getElem_map, VExpr.liftN,
        liftVar_base']
      congr 1
      have hj : j < T.params.length := by simpa using hright
      have hbinders := hdomains.symm
      simp only [List.length_append] at hbinders
      rw [hbinders]
      have hle : 1 + j ≤ T.params.length := by omega
      rw [Nat.sub_sub, Nat.sub_sub]
      simpa [List.length_append, Nat.add_assoc] using
        (Nat.sub_add_comm (n := T.params.length)
          (m := (T.motives ++ T.minors).length + fieldDomains.length) hle)
  rw [← htarget]
  exact Htr

/-- Normal form of the checked constructor major after inserting the
motive/minor block.  Its apparent two-stage lifting is precisely the flat
constructor spine produced by translating the source parameter and field
arguments in the full equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalConstructorMajor_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (introTarget : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (HintroShape : introTarget = VExpr.mkApps
      (.const
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible))
      (recursorCanonicalVars stats.params.size)) :
    VExpr.mkApps
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          (recursorDeclarationAbstractLevels c.lparams
            H.elimLevelAdmissible))
        (List.append
          ((recursorCanonicalVars T.params.length).map (fun arg =>
            arg.liftN
              ((T.motives ++ T.minors).length + fieldDomains.length) 0))
          (recursorCanonicalVars fieldDomains.length)) =
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (recursorCanonicalVars A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  have hcanonicalVars :
      recursorCanonicalVars stats.params.size =
        recursorCanonicalVars T.params.length := by
    exact congrArg recursorCanonicalVars T.params_length.symm
  rw [HintroShape, hcanonicalVars, ← hfields]
  simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append,
    recursorCanonicalVars_liftN_at_length]
  rw [recursorCanonicalVars_liftN_comp]
  simp [VExpr.mkApps, List.foldl_append, Nat.add_comm]

/-- Translate the concrete constructor major in the generated equation to
the exact checked abstract major retained by the constructor phase. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalConstructorMajorResidualTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult introTarget : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hmajor : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (recursorCanonicalVars A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size)
      (fieldResult.liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size))
    (HintroShape : introTarget = VExpr.mkApps
      (.const
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible))
      (recursorCanonicalVars stats.params.size)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext domains [])
      (mkAppN
        (mkAppN
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            stats.levels)
          (stats.params.map fun arg =>
            arg.abstractList A.rule.binders))
        (A.rule.allArgs.map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (recursorCanonicalVars A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  let directMajor := VExpr.mkApps
    (.const
      ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
      (recursorDeclarationAbstractLevels c.lparams
        H.elimLevelAdmissible))
    (List.append
      ((recursorCanonicalVars T.params.length).map (fun arg =>
        arg.liftN
          ((T.motives ++ T.minors).length + fieldDomains.length) 0))
      (recursorCanonicalVars fieldDomains.length))
  have hmajorShape : directMajor =
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (recursorCanonicalVars A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
    exact A.canonicalConstructorMajor_eq T fieldDomains introTarget
      hfields HintroShape
  have Hhead := A.finalConstructorHeadTranslation
    (abstractForallContext domains [])
  have Hargs := A.canonicalConstructorArgsTranslation
    T fieldDomains hfields
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have htoCtxReverse : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)).reverse =
        types.reverse := by
    intro types
    rw [← List.map_reverse]
    exact htoCtx types.reverse
  have Hctx' : OnCtx (abstractForallContext domains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains] using Hctx
  have Hwf : VExpr.WF H.outVEnv Us.length
      (abstractForallContext domains []).toCtx directMajor := by
    rw [hmajorShape]
    refine ⟨fieldResult.liftN
      (T.motives ++ T.minors).length A.rule.allArgs.size, ?_⟩
    change H.outVEnv.IsDefEq Us.length
      (abstractForallContext domains []).toCtx _ _ _
    change H.outVEnv.IsDefEq Us.length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      _ _ _ at Hmajor
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains]
      using Hmajor
  have Htr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx' Hhead Hargs Hwf
  change TrExprS H.outVEnv Us (abstractForallContext domains []) _
    directMajor at Htr
  rw [hmajorShape] at Htr
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append, directMajor,
    domains, List.append_assoc]
    using Htr

/-- The retained parameter, motive, and minor groups close to the canonical
recursor-prefix variables, shifted below the genuine field telescope.  This
is the exact argument list appearing in the weakened prefix typing theorem. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursorPrefixTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext domains []))
      (((stats.params.map fun arg =>
          arg.abstractList A.rule.binders).toList ++
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders).toList) ++
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders).toList)
      ((recursorCanonicalVars
        (T.params ++ T.motives ++ T.minors).length).map fun arg =>
          arg.liftN fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  rcases A.canonicalEquationBinderTranslations T fieldDomains hfields with
    ⟨Hp, Hm, Hmi, _Ha⟩
  have Htr := List.Forall₂.append' (List.Forall₂.append' Hp Hm) Hmi
  have hparams : A.rule.params_bound.fvars.length = T.params.length := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    rw [T.params_length]
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length = T.motives.length := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    rw [T.motives_length]
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length = T.minors.length := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    rw [T.minors_length]
    simpa using h.symm
  have hstatsParams : stats.params.size = T.params.length :=
    T.params_length.symm
  have hstatsMotives : (H.recInfos.map (·.motive)).size = T.motives.length :=
    T.motives_length.symm
  have hstatsMinors : (H.recInfos.flatMap (·.minors)).size = T.minors.length :=
    T.minors_length.symm
  have htarget :
      (((List.ofFn fun i : Fin stats.params.size =>
          VExpr.bvar (A.rule.binders.length - 1 - i)) ++
        (List.ofFn fun i : Fin (H.recInfos.map (·.motive)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            (A.rule.params_bound.fvars.length + i)))) ++
        (List.ofFn fun i : Fin (H.recInfos.flatMap (·.minors)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            ((A.rule.params_bound.fvars ++
              A.rule.motives_bound.fvars).length + i)))) =
        (recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length).map fun arg =>
            arg.liftN fieldDomains.length 0 := by
    rw [recursorCanonicalVars_eq_ofFn]
    apply List.ext_getElem
    · simp only [List.length_append, List.length_ofFn, List.length_map]
      rw [T.params_length, T.motives_length, T.minors_length]
    · intro j hleft hright
      simp only [List.getElem_append, List.length_append,
        List.length_ofFn, List.getElem_ofFn, List.getElem_map,
        VExpr.liftN, liftVar_base']
      split <;> rename_i hjp
      · split <;> rename_i hjpm
        · congr 1
          simp only [List.length_append, List.length_ofFn,
            List.length_map] at hdomains hparams hmotives hminors hleft hright ⊢
          omega
        · congr 1
          simp only [List.length_append, List.length_ofFn,
            List.length_map] at hdomains hparams hmotives hminors hleft hright ⊢
          omega
      · congr 1
        simp only [List.length_append, List.length_ofFn,
          List.length_map] at hdomains hparams hmotives hminors hleft hright ⊢
        omega
  rw [← htarget]
  exact Htr

/-- Assemble the translated recursor head and the three translated outer
binder groups into the exact weakened canonical prefix application.  The
independently established typing derivation supplies every application
premise required by `TrExprS`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursorPrefixResidualTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      ((VExpr.mkApps
          ((VExpr.const H.entries[owner].2.name
            (VLevel.params
              (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0)
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext domains [])
      (mkAppN
        (mkAppN
          (mkAppN
            (.const (Lean.mkRecName indTypes[owner]!.name)
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          ((VExpr.const H.entries[owner].2.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have Hhead := A.finalRecursorHeadTranslation
    (abstractForallContext domains [])
  have Hargs := A.canonicalRecursorPrefixTranslation T fieldDomains hfields
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have htoCtxReverse : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)).reverse =
        types.reverse := by
    intro types
    rw [← List.map_reverse]
    exact htoCtx types.reverse
  have Hctx' : OnCtx (abstractForallContext domains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains] using Hctx
  have Hwf : VExpr.WF H.outVEnv Us.length
      (abstractForallContext domains []).toCtx
      (VExpr.mkApps
        (.const H.entries[owner].2.name (VLevel.params Us.length))
        ((recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length).map fun arg =>
            arg.liftN fieldDomains.length 0)) := by
    exact ⟨_, by
      change H.outVEnv.HasType Us.length
        (abstractForallContext domains []).toCtx
        (VExpr.mkApps
          (.const H.entries[owner].2.name (VLevel.params Us.length))
          ((recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length).map fun arg =>
              arg.liftN fieldDomains.length 0)) _
      simpa [abstractForallContext, htoCtx, htoCtxReverse, domains,
        VExpr.liftN_mkApps, VExpr.liftN] using Hprefix⟩
  have Htr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx' Hhead Hargs Hwf
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append,
    VExpr.liftN_mkApps, VExpr.liftN, domains,
    List.append_assoc] using Htr

/-- Cached parameters are already present in the recursive-call root, hence
cannot collide with the call-local binders freshly introduced above it. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.parameterFVarsFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    ∀ fv ∈ A.rule.params_bound.fvars,
      fv ∉ F.semantic.generated.arguments_bound.fvars := by
  intro fv hparam
  intro hlocal
  have hsource : Expr.fvar fv ∈ stats.params.toList := by
    rw [A.rule.params_bound.expressions]
    simpa using hparam
  have go : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂
        (TrExprS A.semantics.context.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          A.semantics.context.mlctx.vlctx) sources targets →
      Expr.fvar fv ∈ sources →
      fv ∈ A.semantics.context.mlctx.vlctx.fvars := by
    intro sources targets Htr
    induction Htr with
    | nil => simp
    | cons Hhead _ ih =>
      simp only [List.mem_cons]
      intro hmem
      rcases hmem with rfl | hmem
      · simpa only [FVarsIn] using Hhead.fvarsIn
      · exact ih hmem
  have hscope := go A.semantics.validStats.params hsource
  have hrootScope : F.semantic.rootScope fv := by
    rw [F.root_scope]
    exact Or.inr (by
      rw [A.rule.params_bound.exprArrayFVarIds]
      exact hparam)
  have hrootContext := F.rootScope_mem_originContext hrootScope
  have hroot : fv ∈ F.originRoot.lctx.fvars := by
    rw [← F.originContext.lctx_eq,
      F.originContext.mlctx_wf.tr.fvars_eq]
    exact hrootContext
  exact F.semantic.generated.arguments_bound.fresh fv hlocal hroot

/-- The common parameter/motive/minor part of a generated recursive call,
after closing its call-local arguments and then the surrounding rule binders,
is exactly the canonical equation prefix weakened below the local lambdas. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.rawRecursorPrefixClosed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    Closed (mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          stats.params)
        (H.recInfos.map (·.motive)))
      (H.recInfos.flatMap (·.minors))) := by
  have mkAppNClosed : ∀ (head : Expr) (args : Array Expr),
      Closed head → (∀ arg ∈ args, Closed arg) →
      Closed (mkAppN head args) := by
    intro head args hhead hargs
    unfold mkAppN
    rw [← Array.foldl_toList]
    have go : ∀ (xs : List Expr) (acc : Expr),
        Closed acc → (∀ arg ∈ xs, Closed arg) →
        Closed (xs.foldl Expr.app acc) := by
      intro xs
      induction xs with
      | nil => simp
      | cons first rest ih =>
        intro acc hacc hall
        simp only [List.foldl_cons]
        apply ih (.app acc first)
        · exact ⟨hacc, hall first (by simp)⟩
        · intro arg harg
          exact hall arg (by simp [harg])
    exact go args.toList head hhead (by
      intro arg harg
      exact hargs arg (by simpa using harg))
  have boundClosed : ∀ {root xs} (B : BoundFVarArray root xs),
      ∀ arg ∈ xs, Closed arg := by
    intro root xs B arg harg
    rw [B.expressions] at harg
    simp at harg
    rcases harg with ⟨fv, _hfv, rfl⟩
    trivial
  apply mkAppNClosed
  · apply mkAppNClosed
    · apply mkAppNClosed
      · trivial
      · exact boundClosed A.rule.params_bound
    · exact boundClosed A.rule.motives_bound
  · exact boundClosed A.rule.minors_bound

/-- The instantiated call template has the raw recursor prefix followed by
the locally abstracted recursive indices.  Closing rule binders distributes
structurally over that exact spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedRecursor_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let sourceIndices := Std.Slice.toList
      (F.semantic.generated.exposedType.getAppArgs.toSubarray
        stats.params.size)
    let localPrefix := mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          stats.params)
        (H.recInfos.map (·.motive)))
      (H.recInfos.flatMap (·.minors))
    F.semantic.generated.outerAbstractedRecursor A.rule.binders =
      Expr.mkAppList
        (localPrefix.abstractList A.rule.binders
          F.semantic.generated.localArgs.size)
        (sourceIndices.map fun index =>
          (index.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.binders F.semantic.generated.localArgs.size) := by
  dsimp only
  unfold BoundGeneratedRecursiveCall.outerAbstractedRecursor
  rw [SemanticBoundGeneratedRecursiveCall.abstractedRecursor_eq
    F.originContext F.semantic]
  have hclosed := F.rawRecursorPrefixClosed
  rw [Expr.liftLooseBVars_eq_self hclosed.looseBVarRange_le]
  rw [Expr.abstractList_mkAppN, Expr.mkAppN_eq_mkAppList]
  have hidx : ∀ index ∈ Std.Slice.toList
      (F.semantic.generated.exposedType.getAppArgs.toSubarray stats.params.size),
      index.abstractN F.semantic.generated.arguments_bound.fvars =
        index.abstractList F.semantic.generated.arguments_bound.fvars := by
    intro index hmem
    have hexposedClosed : Closed F.semantic.generated.exposedType := by
      have h := F.semantic.exposed_translation.closed
      rwa [F.semantic.current_context.mlctx.noBV] at h
    have hmem' : index ∈ F.semantic.generated.exposedType.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      have hsub : index ∈ (F.semantic.generated.exposedType.getAppArgs.toSubarray
          stats.params.size).toList := hmem
      rw [Subarray.toList_eq_drop_take, Array.array_toSubarray] at hsub
      exact List.mem_of_mem_take (List.mem_of_mem_drop hsub)
    exact Expr.abstractN_eq_abstractList F.semantic.generated.arguments_bound.nodup index 0
      (hexposedClosed.getAppArgsList hmem').looseBVarRange_le
  simp [AddInductive.getIIndices, List.map_map, Function.comp_def]
  congr 1
  exact List.map_congr_left fun index hmem => by rw [hidx index hmem]

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedCommonPrefix_eq_lift
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let localPrefix :=
      mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            stats.params)
          (H.recInfos.map (·.motive)))
        (H.recInfos.flatMap (·.minors))
    let canonicalPrefix :=
      mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders)
    localPrefix.abstractList A.rule.binders
        F.semantic.generated.localArgs.size =
      canonicalPrefix.liftLooseBVars' 0
        F.semantic.generated.localArgs.size := by
  dsimp only
  let rawPrefix := mkAppN
    (mkAppN
      (mkAppN
        (.const F.semantic.generated.recursorName
          (AddInductive.getRecLevels H.elimLevel stats.levels))
        stats.params)
      (H.recInfos.map (·.motive)))
    (H.recInfos.flatMap (·.minors))
  have mkAppNClosed : ∀ (head : Expr) (args : Array Expr),
      Closed head → (∀ arg ∈ args, Closed arg) →
      Closed (mkAppN head args) := by
    intro head args hhead hargs
    unfold mkAppN
    rw [← Array.foldl_toList]
    have go : ∀ (xs : List Expr) (acc : Expr),
        Closed acc → (∀ arg ∈ xs, Closed arg) →
        Closed (xs.foldl Expr.app acc) := by
      intro xs
      induction xs with
      | nil => simp
      | cons first rest ih =>
        intro acc hacc hall
        simp only [List.foldl_cons]
        apply ih (.app acc first)
        · exact ⟨hacc, hall first (by simp)⟩
        · intro arg harg
          exact hall arg (by simp [harg])
    exact go args.toList head hhead (by
      intro arg harg
      exact hargs arg (by simpa using harg))
  have boundClosed : ∀ {root xs} (B : BoundFVarArray root xs),
      ∀ arg ∈ xs, Closed arg := by
    intro root xs B arg harg
    rw [B.expressions] at harg
    simp at harg
    rcases harg with ⟨fv, _hfv, rfl⟩
    trivial
  have hclosed : Closed rawPrefix := by
    apply mkAppNClosed
    · apply mkAppNClosed
      · apply mkAppNClosed
        · trivial
        · exact boundClosed A.rule.params_bound
      · exact boundClosed A.rule.motives_bound
    · exact boundClosed A.rule.minors_bound
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := rawPrefix) (fvars := A.rule.binders) (depth := 0)
    (extra := F.semantic.generated.localArgs.size)
    hclosed A.rule.binders_nodup
  simpa [rawPrefix, Expr.abstractList_mkAppN, Array.map_map,
    Function.comp_def] using hshift

/-- Closing semantic recursive indices first over constructor fields and then
over the outer parameter/motive/minor groups is exactly production's single
rule-binder abstraction at the call-local cutoff.  This removes all remaining
order arithmetic from the later context-transport proof. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedSemanticIndexSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    let outer := (A.rule.params_bound.fvars ++
      A.rule.motives_bound.fvars) ++ A.rule.minors_bound.fvars
    let sourceIndices :=
      F.semantic.generated.exposedType.getAppArgs[stats.params.size:].toList
    ((sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).map fun index =>
      index.abstractList outer
        (F.semantic.generated.localArgs.size +
          A.rule.all_args_bound.fvars.length)) =
    sourceIndices.map fun index =>
      (index.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size := by
  let outer := (A.rule.params_bound.fvars ++
    A.rule.motives_bound.fvars) ++ A.rule.minors_bound.fvars
  let sourceIndices :=
    F.semantic.generated.exposedType.getAppArgs[stats.params.size:].toList
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro index hindex
  have Habstract := Expr.abstractList_after_inner
    (e := index.abstractList
      F.semantic.generated.arguments_bound.fvars)
    (outer := outer) (inner := A.rule.all_args_bound.fvars)
    (k := F.semantic.generated.localArgs.size)
    (by
      simpa [outer, BoundGeneratedRecursorRule.binders,
        List.append_assoc] using A.rule.binders_nodup)
  simpa [outer, BoundGeneratedRecursorRule.binders,
    List.append_assoc] using Habstract


end VerifyInductive
end Lean4Lean
