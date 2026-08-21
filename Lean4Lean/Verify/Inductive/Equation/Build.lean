import Lean4Lean.Verify.Inductive.Equation.Final

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Owner-prefix accumulation of reconstructed equations and their typing
proofs.  Keeping the equation traversal independent of the final block lets
this invariant grow in exactly the order used by `declareRecursors`. -/
structure RecursorPhasesResult.GeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name)
    (owner : Nat) (rules : List VDefEq) : Prop where
  equations : H.GeneratedIotaEquationTranslations Us [] owner rules
  rulesWF : ∀ rule ∈ rules, rule.WF H.outVEnv

def RecursorPhasesResult.GeneratedEquationBuild.empty
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name) :
    H.GeneratedEquationBuild Us 0 [] where
  equations := .nil
  rulesWF _ h := by simp at h

theorem RecursorPhasesResult.GeneratedEquationBuild.appendOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
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
theorem RecursorPhasesResult.existsGeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) (Us : List Name)
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
theorem RecursorPhasesResult.existsCanonicalGeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :
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
from `RecursorPhasesResult`; callers retain only post-installation equation
translation plus the opaque projection-preservation boundary. -/
structure OrdinaryRuleTranslationResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) where
  Us : List Name
  Δ : VLCtx
  rules : List VDefEq
  rulesWF : ∀ df ∈ rules, df.WF H.outVEnv
  owner : Nat
  equations : H.GeneratedIotaEquationTranslations Us Δ owner rules
  contextFree : VLCtx.NoIndConsts
    ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) Δ
  projections : ∀ {Delta : VLCtx} {s j e' e''},
    TrProj Delta.toCtx s j e' e'' →
    e'.containsAnyConst
      ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) =
        false →
    e''.containsAnyConst
      ((H.blockCertificate rules rulesWF).block.recursors.map (·.name)) =
        false
  complete : owner = H.entries.length

def RecursorPhasesResult.GeneratedEquationBuild.ordinaryResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {rules : List VDefEq}
    (T : H.GeneratedEquationBuild Us owner rules)
    (hcomplete : owner = H.entries.length)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst
        ((H.blockCertificate rules T.rulesWF).block.recursors.map
          (·.name)) = false →
      e''.containsAnyConst
        ((H.blockCertificate rules T.rulesWF).block.recursors.map
          (·.name)) = false) :
    OrdinaryRuleTranslationResult H where
  Us := Us
  Δ := []
  rules := rules
  rulesWF := T.rulesWF
  owner := owner
  equations := T.equations
  contextFree := by
    intro v mapped type hfind
    simp [VLCtx.find?] at hfind
  projections := hproj
  complete := hcomplete

/-- The completed recursor phase determines the full ordinary compilation
payload.  The only shared-typing premise is the generic structural property
of the opaque `TrProj` relation; no rule, telescope, or equation witness is
chosen by the caller. -/
theorem RecursorPhasesResult.canonicalOrdinaryRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (hproj : ProjectionConstPreservation) :
    Nonempty (OrdinaryRuleTranslationResult H) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases H.existsCanonicalGeneratedEquationBuild with ⟨rules, ⟨T⟩⟩
  refine ⟨T.ordinaryResult rfl ?_⟩
  intro Delta s j e' e'' Hprojection hfree
  exact hproj _ Hprojection hfree

theorem OrdinaryRuleTranslationResult.compilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    (T : OrdinaryRuleTranslationResult H) :
    OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate T.rules T.rulesWF).block :=
  H.ordinaryCompilationOfRuleBuild T.rules T.rulesWF
    (T.equations.build T.rules T.rulesWF T.contextFree T.projections)
    (T.equations.completeLength T.complete)

theorem RecursorPhasesResult.addInductOfOrdinaryCompilation
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
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).addInductOfOrdinaryCompilation
    R.formation R.core hnonempty Hcompile

theorem RecursorPhasesResult.addInductOfNestedCompilation
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
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : NestedCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block) :
    VEnv.AddInduct sourceEnv decl (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).addInductOfNestedCompilation
    R.formation R.core hnonempty Hcompile

/-- Concrete-environment endpoint for an ordinary executable recursor run.
The staged installation, formation, source typing, and compilation proof now
enter `TrEnv'` in one step. -/
theorem RecursorPhasesResult.trEnvOfOrdinaryCompilation
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
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block)
    (htr : TrEnv' c.safety c.env.constants c.env.quotInit sourceEnv)
    (heq : ∀ info, outEnv.constants.find? ``Eq = some (.inductInfo info) →
      (H.outVEnv.addDefEqRules rules).constants ``Eq = some eqConst) :
    TrEnv' c.safety outEnv.constants c.env.quotInit
      (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).trEnvOfOrdinaryCompilation R.formation
    R.core hnonempty Hcompile htr heq

/-- Nested-compilation counterpart of `trEnvOfOrdinaryCompilation`. -/
theorem RecursorPhasesResult.trEnvOfNestedCompilation
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
    (hnonempty : indTypes.toList ≠ [])
    (Hcompile : NestedCompilationCertificate sourceEnv decl
      (H.blockCertificate rules hrules).block)
    (htr : TrEnv' c.safety c.env.constants c.env.quotInit sourceEnv)
    (heq : ∀ info, outEnv.constants.find? ``Eq = some (.inductInfo info) →
      (H.outVEnv.addDefEqRules rules).constants ``Eq = some eqConst) :
    TrEnv' c.safety outEnv.constants c.env.quotInit
      (H.outVEnv.addDefEqRules rules) :=
  (H.blockCertificate rules hrules).trEnvOfNestedCompilation R.formation
    R.core hnonempty Hcompile htr heq

/-- Compositional verifier for the complete production computation after
`checkInductiveTypes` has materialized `stats`. This is the first boundary
whose executable side contains every ordinary installation phase. -/
theorem AddInductive.runWithStats.WF
    (stats : AddInductive.InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context)
    (Hformation :
      ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
        isUnsafe >>= fun headerEnv =>
          AddInductive.withEnv headerEnv do
            AddInductive.checkConstructors indTypes stats isUnsafe
            AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
        fun ctorEnv => ∃ headerEnv : Environment,
          ∃ Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe
            depth sourceEnv indTypes headerEnv,
          ∃ _ : ConstructorPhasesResult Hheaders ctorEnv,
            MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hwhnf : WhnfLParamsCompat)
    (hfieldReplay : RecursorFieldDecisionReplayCompat)
    (hloopUArgsReplay : RecursorLoopUArgsReplayCompat)
    (hrecConsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      fun outEnv => ∃ headerEnv ctorEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
          sourceEnv indTypes headerEnv,
        ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
          Nonempty (RecursorPhasesResult R outEnv) := by
  unfold AddInductive.runWithStats
  have Hcombined := Hformation.bind fun ctorEnv Hresult => by
      rcases Hresult with ⟨headerEnv, Hheaders, R, hclosed⟩
      exact (R.recursorPhasesWF hclosed hlparams hwhnf hfieldReplay
        hloopUArgsReplay hrecConsume hlit hproj hnotPartial hnprim).mono
          fun outEnv Hrecursors =>
            show ∃ headerEnv ctorEnv,
              ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
                isUnsafe depth sourceEnv indTypes headerEnv,
              ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
                Nonempty (RecursorPhasesResult R outEnv)
            from ⟨headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩
  simpa [AddInductive.withEnv, bind, ReaderT.bind] using Hcombined

/-- End-to-end post-analysis verifier specialized with the verified
header/constructor formation pipeline.  Generated recursor types are checked
by the executable pipeline itself, leaving only its production freshness and
formation side conditions. -/
theorem AddInductive.runWithStats.closedWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlparams : c.lparams.Nodup)
    (hwhnf : WhnfLParamsCompat)
    (hfieldReplay : RecursorFieldDecisionReplayCompat)
    (hloopUArgsReplay : RecursorLoopUArgsReplayCompat)
    (hrecConsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hnotPartial : c.safety ≠ .partial)
    (hnprimRecursors : c.allowPrimitive = true →
      ∀ owner (howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats numParams indTypes numNested isUnsafe c).WF
      fun outEnv => ∃ headerEnv ctorEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes headerEnv,
        ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
          Nonempty (RecursorPhasesResult R outEnv) := by
  apply AddInductive.runWithStats.WF stats numParams indTypes numNested
    isUnsafe c
  · exact AddInductive.formationCore.closedWF Hc Hclosed Hdecl Hmaterialized
      hvisible hnprimTypes hconsume hlit hproj hunsafe hnprimCtors
  · exact hlparams
  · exact hwhnf
  · exact hfieldReplay
  · exact hloopUArgsReplay
  · exact hrecConsume
  · exact hlit
  · exact hproj
  · exact hnotPartial
  · exact hnprimRecursors

/-- The production universe-parameter guard succeeds only for a duplicate-free
parameter list. -/
theorem Kernel.Environment.checkDuplicatedUnivParams.WF
    (lparams : List Name) :
    (Kernel.Environment.checkDuplicatedUnivParams lparams).WF
      (fun _ => lparams.Nodup) := by
  induction lparams with
  | nil =>
    intro out hout
    cases hout
    trivial
  | cons param lparams ih =>
    by_cases hmem : param ∈ lparams
    · rw [Kernel.Environment.checkDuplicatedUnivParams]
      simp only [hmem, if_pos, Except.bind]
      exact Except.WF.throw
    · simpa [Kernel.Environment.checkDuplicatedUnivParams, hmem] using
        ih.mono fun _ htail => List.nodup_cons.mpr ⟨hmem, htail⟩

/-- Front-end composition for `AddInductive.run`: the executable header
analysis materializes an independent declaration before the post-analysis
installer is invoked. This theorem deliberately leaves the latter callback
parametric, so environment conservation and formation assumptions are visible
at their exact boundary. -/
theorem AddInductive.run.materialize
    (numNested : Nat) (Q : Environment → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      types.toArray.toList (c.safety != .safe) skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat},
      (Hc' : ContextWF c') →
      c'.env = c.env →
      c'.safety = c.safety →
      TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (c.safety != .safe) decl envTypes →
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth →
      c'.lparams.Nodup →
      (AddInductive.runWithStats stats skeleton.nparams types.toArray
        numNested (c.safety != .safe) c').WF Q) :
    (AddInductive.run skeleton.nparams types numNested c).WF Q := by
  have Hduplicates :
      (Kernel.Environment.checkDuplicatedUnivParams c.lparams).WF
        fun _ => c.lparams.Nodup :=
    Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams
  have Hcombined := Hduplicates.bind fun _ hnodup => by
    apply Lean4Lean.VerifyInductive.checkInductiveTypes.loopInd.checkInductiveTypes.materialize
      (fun stats => AddInductive.runWithStats stats skeleton.nparams
        types.toArray numNested (c.safety != .safe)) Q Hc Hdecl hctx hnonempty
      hconsume
    intro c' stats decl depth Hc' henvEq hsafetyEq hlparamsEq Hdecl' Hmaterialized
    apply Hfinish Hc' henvEq hsafetyEq Hdecl' Hmaterialized
    simpa [hlparamsEq] using hnodup
  simpa [AddInductive.run] using Hcombined

/-- The explicit semantic/freshness inputs needed to verify one set of
statistics materialized by `checkInductiveTypes`. Keeping this bundle indexed
by the materialization prevents any implementation-derived declaration from
being substituted silently. -/
structure RunWithStatsVerificationInputs
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (numParams depth numNested : Nat)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth) : Prop where
  freshTypes : c.allowPrimitive = true → ∀ info ∈
    (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
      isUnsafe c.lparams).toList,
    ¬ Kernel.Environment.primitives.contains info.name
  consume : ConsumeTypeAnnotationsCompat
  whnfLParams : WhnfLParamsCompat
  recursiveFieldReplay : RecursorFieldDecisionReplayCompat
  loopUArgsReplay : RecursorLoopUArgsReplayCompat
  recursorConsume : RecursorConsumeTypeAnnotationsCompat
  literalDisjoint : checkPositivityStep.LiteralDisjoint stats.indConsts
  projections : ProjectionConstPreservation
  freshConstructorConstants : c.allowPrimitive = true →
    ∀ owner ∈ indTypes.toList,
    ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name
  freshRecursors : c.allowPrimitive = true →
    ∀ owner (howner : owner < indTypes.size),
    ¬ Kernel.Environment.primitives.contains
      (Lean.mkRecName indTypes[owner]!.name)

theorem RunWithStatsVerificationInputs.verify
    (H : RunWithStatsVerificationInputs c stats decl numParams depth
      numNested indTypes isUnsafe Hc Hdecl Hmaterialized)
    (Hclosed : MutualInductivesClosed c.env)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnotPartial : c.safety ≠ .partial) :
    c.lparams.Nodup →
    (AddInductive.runWithStats stats numParams indTypes numNested isUnsafe
      c).WF fun outEnv => ∃ headerEnv ctorEnv,
        ∃ Hheaders : DeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes headerEnv,
        ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
          Nonempty (RecursorPhasesResult R outEnv) :=
  fun hlparams => AddInductive.runWithStats.closedWF Hc Hclosed Hdecl
    Hmaterialized hvisible H.freshTypes H.consume
    hlparams H.whnfLParams H.recursiveFieldReplay H.loopUArgsReplay
    H.recursorConsume
    H.literalDisjoint (fun Htr hfree =>
      H.projections (decl.types.map (·.name)) Htr hfree)
    (fun h => Hdecl.isUnsafe.trans h)
    H.freshConstructorConstants hnotPartial
    H.freshRecursors

/-- Declaration-facing successful result of the complete ordinary executable
checker, including the independently materialized declaration and the exact
installed recursor phase. -/
def VerifiedInductiveRunResult
    (source : AddInductive.Context) (skeleton : VInductDeclSkeleton)
    (envTypes : VEnv) (types : List InductiveType) (numNested : Nat)
    (outEnv : Environment) : Prop :=
  ∃ c' stats decl depth,
    ∃ Hc' : ContextWF c',
    ∃ Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
      types.toArray.toList (source.safety != .safe) decl envTypes,
    ∃ Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth,
    ∃ headerEnv ctorEnv,
    ∃ Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
      (source.safety != .safe) depth Hc'.venv types.toArray headerEnv,
    ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
      types.toArray.toList ≠ [] ∧
      Nonempty (RecursorPhasesResult R outEnv)

theorem AddInductive.run.closedWF
    (numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv c.lparams skeleton.nparams
      types.toArray.toList (c.safety != .safe) skeleton envTypes)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat}
      (Hc' : ContextWF c')
      (Hdecl' : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (c.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth),
      RunWithStatsVerificationInputs c' stats decl skeleton.nparams depth
        numNested types.toArray (c.safety != .safe) Hc' Hdecl'
        Hmaterialized) :
    (AddInductive.run skeleton.nparams types numNested c).WF
      (VerifiedInductiveRunResult c skeleton envTypes types numNested) := by
  apply AddInductive.run.materialize numNested
    (VerifiedInductiveRunResult c skeleton envTypes types numNested)
    Hc Hdecl hctx hnonempty hconsume
  intro c' stats decl depth Hc' henvEq hsafetyEq Hdecl' Hmaterialized
    hlparamsNodup
  have Hclosed' : MutualInductivesClosed c'.env := by
    simpa [henvEq] using Hclosed
  have HnotPartial' : c'.safety ≠ .partial := by
    simpa [hsafetyEq] using HnotPartial
  have hvisible : c'.safety ≤
      (if c.safety != .safe then DefinitionSafety.unsafe else .safe) := by
    rw [hsafetyEq]
    cases hsafety : c.safety <;> simp_all
  exact ((Hinputs Hc' Hdecl' Hmaterialized).verify Hclosed' hvisible
    HnotPartial' hlparamsNodup).mono
    fun outEnv Hout => by
      rcases Hout with ⟨headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩
      exact ⟨c', stats, decl, depth, Hc', Hdecl', Hmaterialized,
        headerEnv, ctorEnv, Hheaders, R, by
          simpa using List.ne_nil_of_length_pos
            (by simpa using hnonempty : 0 < types.length),
        Hrecursors⟩

/-- Close a successful ordinary declaration run from the exact generated
rule translations retained per mutual-family owner. -/
theorem VerifiedInductiveRunResult.addInductOfRuleTranslations
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hrules : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      Nonempty (OrdinaryRuleTranslationResult Hrecursors)) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hrules c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
      ctorEnv Hheaders R Hrecursors with ⟨T⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules T.rules,
    Hrecursors.addInductOfOrdinaryCompilation T.rules T.rulesWF hnonempty
      T.compilation⟩

/-- Ordinary executable runs refine the independent inductive specification
without a caller-supplied equation batch.  All generated equations,
including mutual and dependent recursive cases, are reconstructed from the
completed recursor phase. -/
theorem VerifiedInductiveRunResult.addInductCanonical
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (hproj : ProjectionConstPreservation) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  apply Hrun.addInductOfRuleTranslations
  intro c' stats decl depth Hc' Hdecl Hmaterialized headerEnv ctorEnv
    Hheaders R Hrecursors
  exact Hrecursors.canonicalOrdinaryRuleTranslation hproj

/-- Close a verified ordinary executable run against the independent
`VEnv.AddInduct` specification once the generated rule batch and compilation
certificate are supplied. -/
theorem VerifiedInductiveRunResult.addInductOfRuleBuild
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hrules : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      ∃ rules : List VDefEq,
        ∃ hrules : (∀ df ∈ rules, df.WF Hrecursors.outVEnv),
        IotaBuildCertificate R.declared.venvCtors decl
          (Hrecursors.blockCertificate rules hrules).block rules ∧
        rules.length = decl.ownedConstructors.length) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hrules c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
      ctorEnv Hheaders R Hrecursors with
    ⟨rules, hrules, HruleBuild, hrulesLength⟩
  have Hcompile := Hrecursors.ordinaryCompilationOfRuleBuild rules hrules
    HruleBuild hrulesLength
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules rules,
    Hrecursors.addInductOfOrdinaryCompilation rules hrules hnonempty
      Hcompile⟩

theorem VerifiedInductiveRunResult.addInductOfOrdinaryCompilation
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hcompile : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      ∃ rules : List VDefEq,
        ∃ hrules : (∀ df ∈ rules, df.WF Hrecursors.outVEnv),
        OrdinaryCompilationCertificate Hc'.venv decl
          (Hrecursors.blockCertificate rules hrules).block) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hcompile c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
    ctorEnv Hheaders R Hrecursors with
    ⟨rules, hrules, Hcompilation⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules rules,
    Hrecursors.addInductOfOrdinaryCompilation rules hrules hnonempty
      Hcompilation⟩

/-- Nested counterpart of
`VerifiedInductiveRunResult.addInductOfOrdinaryCompilation`. -/
theorem VerifiedInductiveRunResult.addInductOfNestedCompilation
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv)
    (Hcompile : ∀ c' stats decl depth
      (Hc' : ContextWF c')
      (Hdecl : TrInductDeclHeaders Hc'.venv c'.lparams skeleton.nparams
        types.toArray.toList (source.safety != .safe) decl envTypes)
      (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl depth)
      headerEnv ctorEnv
      (Hheaders : DeclaredHeadersResult c' stats decl skeleton.nparams
        (source.safety != .safe) depth Hc'.venv types.toArray headerEnv)
      (R : ConstructorPhasesResult Hheaders ctorEnv)
      (Hrecursors : RecursorPhasesResult R outEnv),
      ∃ rules : List VDefEq,
        ∃ hrules : (∀ df ∈ rules, df.WF Hrecursors.outVEnv),
        Nonempty (NestedCompilationCertificate Hc'.venv decl
          (Hrecursors.blockCertificate rules hrules).block)) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with ⟨c', stats, decl, depth, Hc', Hdecl, Hmaterialized,
    headerEnv, ctorEnv, Hheaders, R, hnonempty, ⟨Hrecursors⟩⟩
  rcases Hcompile c' stats decl depth Hc' Hdecl Hmaterialized headerEnv
    ctorEnv Hheaders R Hrecursors with
    ⟨rules, hrules, ⟨Hcompilation⟩⟩
  exact ⟨c', Hc', decl, Hrecursors.outVEnv.addDefEqRules rules,
    Hrecursors.addInductOfNestedCompilation rules hrules hnonempty
      Hcompilation⟩


end VerifyInductive
end Lean4Lean
