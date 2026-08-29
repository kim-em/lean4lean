import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.OrdinaryLoweringCorrespondence
import Lean4Lean.Verify.Inductive.Run.SemanticFinalDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The ordinary production branch cannot request a reserved primitive name.
Consequently all three primitive-name side conditions are vacuous; the only
remaining run inputs are the shared, producer-shaped compatibility facts. -/
theorem SemanticRunVerificationInputs.ofAllowPrimitiveFalse
    (hallow : c.allowPrimitive = false) :
    SemanticRunVerificationInputs c stats nparams depth numNested indTypes
      isUnsafe Hc where
  freshTypes htrue := by simp_all
  freshConstructors htrue := by simp_all
  freshRecursors htrue := by simp_all

/-- A completed lowering trace can only have arisen from a nonempty source
mutual block.  This packages the operational nonemptiness check at the
declaration-facing trace boundary. -/
theorem NestedLoweringResult.sourceTypes_nonempty
    (H : NestedLoweringResult env fuel nparams sourceTypes initialState result) :
    sourceTypes ≠ [] := by
  rcases H with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨first, rest, tail, paramsState, lctx, params, htypes, _⟩
  simp [htypes]

/-- Lowering retains every original family, so a successful lowering result
is itself nonempty. -/
theorem NestedLoweringResult.resultTypes_nonempty
    (initialState : ElimNestedInductive.State)
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    result.types ≠ [] := by
  have hsource : 0 < sourceTypes.length := by
    cases htypes : sourceTypes with
    | nil => exact (H.sourceTypes_nonempty htypes).elim
    | cons _ _ => simp
  exact List.ne_nil_of_length_pos
    (Nat.lt_of_lt_of_le hsource H.sourceTypes_length_le)

/-- Complete final-environment refinement for the ordinary post-lowering
branch.  The result is indexed by the exact lowered declaration checked by
production.  Relating this declaration back to the source syntax is kept as
a distinct lowering-correctness obligation rather than folded into execution
soundness. -/
theorem Environment.addInductiveAfterLowering.ordinaryFinalEnvironmentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env) (hEq : CanonicalEqEnvs ves)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0)
    : (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        exists ves' : VEnvs, ves'.WF outEnv /\ CanonicalEqEnvs ves' /\
          forall safety, ves.venv safety <= ves'.venv safety := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel
  have hsource : Hc.venv = ves.venv c.safety := by
    rfl
  have hctx : Hc.mlctx.vlctx = [] := by
    rfl
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have hnonempty : res.types ≠ [] :=
    Hlower.resultTypes_nonempty
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray }
  have Hinputs : forall {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') ->
      c'.allowPrimitive = c.allowPrimitive ->
      c'.fuel = c.fuel ->
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) ->
      SemanticRunVerificationInputs c' stats nparams depth 0
        res.types.toArray (c.safety != .safe) Hc' := by
    intro c' stats depth commonParams commonLevel Hc' hallow _hfuel _Hsemantic
    exact SemanticRunVerificationInputs.ofAllowPrimitiveFalse
      (by simpa [c, initialContext] using hallow)
  have Hrun := AddInductive.run.semanticFinalWF
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hEq hsource
    wf.inductivesClosed hctx hnonempty hnotPartial Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  simpa [c, safety, initialContext] using Hrun

/-- Source-facing ordinary refinement at the exact production boundary.  The
successful source precheck and zero-auxiliary lowering trace prove that the
block checked by `AddInductive.run` is literally the original declaration;
the final model and independent source judgment therefore come from the same
execution. -/
theorem Environment.addInductiveAfterLowering.ordinaryFinalSpecificationModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult
            (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
            sourceTypes isUnsafe) := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel
  have hsource : Hc.venv = ves.venv c.safety := by
    rfl
  have hctx : Hc.mlctx.vlctx = [] := by
    rfl
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have hnonempty : res.types ≠ [] :=
    Hlower.resultTypes_nonempty
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray }
  have htypes : res.types = sourceTypes :=
    Hlower.ordinary_types_eq_source Hsources haux
  have Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth 0
        res.types.toArray (c.safety != .safe) Hc' := by
    intro c' stats depth commonParams commonLevel Hc' hallow _hfuel _Hsemantic
    exact SemanticRunVerificationInputs.ofAllowPrimitiveFalse
      (by simpa [c, initialContext] using hallow)
  have Hrun := AddInductive.run.semanticFinalSpecificationModelWF
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hsource
    wf.inductivesClosed hctx hnonempty hnotPartial Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  rcases Hrun outEnv hout' with ⟨ves', wf', hle, ⟨S⟩⟩
  refine ⟨ves', wf', hle, ⟨?_⟩⟩
  rw [htypes, hsource] at S
  have hisUnsafe : (c.safety != .safe) = isUnsafe := by
    cases isUnsafe <;> rfl
  rw [hisUnsafe] at S
  simpa [c, safety, initialContext] using S

/-- Canonical equality is an orthogonal invariant preserved by monotonicity
of the equality-independent ordinary refinement. -/
theorem Environment.addInductiveAfterLowering.ordinaryFinalSpecificationWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env) (hEq : CanonicalEqEnvs ves)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult
            (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
            sourceTypes isUnsafe) := by
  exact (Environment.addInductiveAfterLowering.ordinaryFinalSpecificationModelWF
    env lparams nparams sourceTypes isUnsafe fuel res ves wf Hsources Hlower
    haux).mono fun _ ⟨ves', wf', hle, Hspec⟩ =>
      ⟨ves', wf', hEq.mono hle, hle, Hspec⟩

end VerifyInductive
end Lean4Lean
