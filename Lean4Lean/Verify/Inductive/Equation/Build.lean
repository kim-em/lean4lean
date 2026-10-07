import Lean4Lean.Verify.Inductive.Equation.Setup
import Lean4Lean.Verify.Inductive.CompletedRuleTranslation
import Lean4Lean.Verify.Inductive.TypeAnnotations
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Ordinary runs use the same completed-constructor translation result as
primitive runs. Their block payloads are definitionally equal. -/
abbrev OrdinaryRuleTranslationResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :=
  CompletedRuleTranslationResult H.completed

/-- Ordinary runs obtain their joint generation and concrete metadata witness
from the shared completed producer, without a caller-chosen equation batch. -/
theorem RecursorPhasesResult.canonicalOrdinaryRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv) :
    Nonempty (OrdinaryRuleTranslationResult H) := by
  exact H.completed.canonicalCompletedRuleTranslation

theorem OrdinaryRuleTranslationResult.compilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    (T : OrdinaryRuleTranslationResult H)
    (hnonempty : indTypes.toList ≠ []) :
    OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate T.rules T.rulesWF).block :=
  CompletedRuleTranslationResult.compilation T hnonempty

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
    VEnv.AddInduct sourceEnv decl (H.blockCertificate rules hrules).finalVEnv :=
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
    VEnv.AddInduct sourceEnv decl (H.blockCertificate rules hrules).finalVEnv :=
  (H.blockCertificate rules hrules).addInductOfNestedCompilation
    R.formation R.core hnonempty Hcompile

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
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
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
      have hlitHeaders := Hheaders.materializedAvailableLiteralDisjoint
      have hlitCtors :=
        R.declared.installed.availableLiteralDisjoint hlitHeaders
      have hlit : checkPositivityStep.AvailableLiteralDisjoint
          R.declared.context.venv stats.indConsts := by
        rw [R.declared.contextVEnv]
        exact hlitCtors.addProjections _
      exact (R.recursorPhasesWF (hsourceSafety := hsourceSafety) hclosed hlparams hlit
        hnotPartial hnprim).mono
          fun outEnv Hrecursors =>
            show ∃ headerEnv ctorEnv,
              ∃ Hheaders : DeclaredHeadersResult c stats decl nparams
                isUnsafe depth sourceEnv indTypes headerEnv,
              ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
                Nonempty (RecursorPhasesResult R outEnv)
            from ⟨headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩
  simpa [AddInductive.withEnv, bind, ReaderT.bind] using Hcombined

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
  freshConstructorConstants : c.allowPrimitive = true →
    ∀ owner ∈ indTypes.toList,
    ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name
  freshRecursors : c.allowPrimitive = true →
    ∀ owner (howner : owner < indTypes.size),
    ¬ Kernel.Environment.primitives.contains
      (Lean.mkRecName indTypes[owner]!.name)


/-- On the ordinary declaration path, primitive-name freshness is automatic:
the three freshness fields are only queried when `allowPrimitive = true`.
This constructor keeps the finite `Bool`/`Nat` bootstrap branch out of the
general verification inputs instead of asking callers for false premises. -/
theorem RunWithStatsVerificationInputs.ofAllowPrimitiveFalse
    (hallow : c.allowPrimitive = false) :
    RunWithStatsVerificationInputs c stats decl numParams depth numNested
      indTypes isUnsafe Hc Hdecl Hmaterialized where
  freshTypes htrue := by simp_all
  freshConstructorConstants htrue := by simp_all
  freshRecursors htrue := by simp_all

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
  exact ⟨c', Hc', decl, (Hrecursors.blockCertificate T.rules T.rulesWF).finalVEnv,
    Hrecursors.addInductOfOrdinaryCompilation T.rules T.rulesWF hnonempty
      (T.compilation hnonempty)⟩

/-- Ordinary executable runs refine the independent inductive specification
without a caller-supplied equation batch.  All generated equations,
including mutual and dependent recursive cases, are reconstructed from the
completed recursor phase. -/
theorem VerifiedInductiveRunResult.addInductCanonical
    (Hrun : VerifiedInductiveRunResult source skeleton envTypes types
      numNested outEnv) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  apply Hrun.addInductOfRuleTranslations
  intro c' stats decl depth Hc' Hdecl Hmaterialized headerEnv ctorEnv
    Hheaders R Hrecursors
  exact Hrecursors.canonicalOrdinaryRuleTranslation


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
  exact ⟨c', Hc', decl, (Hrecursors.blockCertificate rules hrules).finalVEnv,
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
  exact ⟨c', Hc', decl, (Hrecursors.blockCertificate rules hrules).finalVEnv,
    Hrecursors.addInductOfNestedCompilation rules hrules hnonempty
      Hcompilation⟩


end VerifyInductive
end Lean4Lean
