import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.OrdinaryLoweringCorrespondence
import Lean4Lean.Verify.Inductive.Run.SemanticFinalDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The ordinary production branch cannot request a reserved primitive name.
Consequently all three primitive-name side conditions are vacuous; the only
remaining run inputs are facts retained by the shared producer pipeline. -/
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

/-- Well-formedness of the ordinary (zero-auxiliary) branch alone.  Unlike the
specification-facing endpoints below, this needs no closedness of the source
syntax: the checked block is whatever lowering produced. -/
theorem Environment.addInductiveAfterLowering.ordinaryFinalModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WFCore env) (hcorner : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          VEnvs.CertPres env outEnv ves ves' := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel hcorner
  have hsource : Hc.venv = ves.venv c.safety := by
    rfl
  have hctx : Hc.mlctx.vlctx = [] := by
    rfl
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have hnonempty : res.types ≠ [] :=
    Hlower.resultTypes_nonempty
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray }
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
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hcorner hsource
    wf.inductivesClosed hctx hnonempty hnotPartial Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  rcases Hrun outEnv hout' with ⟨ves', wf', hle, hcert, _⟩
  exact ⟨ves', wf', hle, hcert⟩

/-- Source-facing ordinary refinement at the exact production boundary.  The
successful source precheck and zero-auxiliary lowering trace prove that the
block checked by `AddInductive.run` is literally the original declaration;
the final model and independent source judgment therefore come from the same
execution. -/
theorem Environment.addInductiveAfterLowering.ordinaryFinalSpecificationModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WFCore env) (hcorner : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (Hlower : NestedLoweringResult env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult
            (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
            sourceTypes isUnsafe
            (ves'.venv (if isUnsafe then .unsafe else .safe))) ∧
          VEnvs.CertPres env outEnv ves ves' := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel hcorner
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
    Hlower.ordinary_types_eq_source Hsources HsourcesB haux
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
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hcorner hsource
    wf.inductivesClosed hctx hnonempty hnotPartial Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  rcases Hrun outEnv hout' with ⟨ves', wf', hle, hcert, ⟨S⟩⟩
  refine ⟨ves', wf', hle, ⟨?_⟩, hcert⟩
  rw [htypes, hsource] at S
  have hisUnsafe : (c.safety != .safe) = isUnsafe := by
    cases isUnsafe <;> rfl
  rw [hisUnsafe] at S
  simpa [c, safety, initialContext] using S

end VerifyInductive
end Lean4Lean
