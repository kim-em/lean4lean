import Lean4Lean.Verify.Inductive.CompletedRecursorSetup

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Common executable `runWithStats` seam.  The formation callback may have
come from ordinary per-constant installation or the atomic primitive batch;
recursor generation starts only after either callback supplies the same
completed valid constructor boundary. -/
theorem AddInductive.runWithStats.completedWF
    (stats : AddInductive.InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context)
    (Hformation :
      ((AddInductive.declareInductiveTypes stats nparams indTypes numNested
        isUnsafe >>= fun headerEnv =>
          AddInductive.withEnv headerEnv do
            AddInductive.checkConstructors indTypes stats isUnsafe
            AddInductive.declareConstructors stats indTypes isUnsafe) c).WF
        fun ctorEnv =>
          ∃ R : CompletedConstructorPhases c stats decl nparams isUnsafe
              depth sourceEnv indTypes ctorEnv,
            MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
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
      fun outEnv =>
        ∃ ctorEnv,
        ∃ R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
            sourceEnv indTypes ctorEnv,
          Nonempty (CompletedRecursorPhasesResult R outEnv) := by
  unfold AddInductive.runWithStats
  have Hcombined := Hformation.bind fun ctorEnv Hresult => by
    rcases Hresult with ⟨R, hclosed⟩
    exact (R.recursorPhasesWF hclosed hlparams hloopUArgsReplay hlit hproj
      hnotPartial hnprim).mono
        fun outEnv Hrecursors =>
          show ∃ ctorEnv,
            ∃ R : CompletedConstructorPhases c stats decl nparams isUnsafe
                depth sourceEnv indTypes ctorEnv,
              Nonempty (CompletedRecursorPhasesResult R outEnv)
          from ⟨ctorEnv, R, Hrecursors⟩
  simpa [AddInductive.withEnv, bind, ReaderT.bind] using Hcombined

/-- Ordinary formation embeds into the common executable seam through the
completed-constructor adapter. -/
theorem AddInductive.runWithStats.completedOrdinaryWF
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
          ∃ R : ConstructorPhasesResult Hheaders ctorEnv,
            MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
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
      fun outEnv =>
        ∃ ctorEnv,
        ∃ R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
            sourceEnv indTypes ctorEnv,
          Nonempty (CompletedRecursorPhasesResult R outEnv) := by
  apply AddInductive.runWithStats.completedWF stats nparams indTypes
    numNested isUnsafe c
  · exact Hformation.mono fun ctorEnv Hresult => by
      rcases Hresult with ⟨_headerEnv, _Hheaders, R, hclosed⟩
      exact ⟨R.completed, hclosed⟩
  · exact hlparams
  · exact hloopUArgsReplay
  · exact hlit
  · exact hproj
  · exact hnotPartial
  · exact hnprim

/-- Atomic primitive formation embeds into the same executable seam only
after constructor installation has restored a valid context. -/
theorem AddInductive.runWithStats.completedPrimitiveWF
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
          ∃ Hheaders : PrimitiveDeclaredHeadersResult c stats decl nparams
            isUnsafe depth sourceEnv indTypes headerEnv,
          ∃ R : PrimitiveConstructorPhasesResult Hheaders ctorEnv,
            MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
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
      fun outEnv =>
        ∃ ctorEnv,
        ∃ R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
            sourceEnv indTypes ctorEnv,
          Nonempty (CompletedRecursorPhasesResult R outEnv) := by
  apply AddInductive.runWithStats.completedWF stats nparams indTypes
    numNested isUnsafe c
  · exact Hformation.mono fun ctorEnv Hresult => by
      rcases Hresult with ⟨_headerEnv, _Hheaders, R, hclosed⟩
      exact ⟨R.completed, hclosed⟩
  · exact hlparams
  · exact hloopUArgsReplay
  · exact hlit
  · exact hproj
  · exact hnotPartial
  · exact hnprim

end VerifyInductive
end Lean4Lean
