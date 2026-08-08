import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Inductive.Basic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf (.axiomInfo v) false hsafety).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hci, hn, hnonprim⟩ := h
  refine .pure <| addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (hnonprim rfl) fun _ _ htr hci hadd old => ?_
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr
      (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addNonrecursiveDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hunsafe : v.safety ≠ .unsafe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  split
  · contradiction
  refine (checkDefinition.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨allow, ci', hp, hu, ht, hname, hvalue, hci, hfresh, hnonprim⟩ := h
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  refine .pure <| addDef.WF wf v ci' v.safety ?_ htr (hci.mono hmono) hfresh ?_ ?_
  · simp [ConstantInfo.defnInfo_safety]
  · intro hnamePrim
    have hallow : allow = true := by
      cases allow
      · simp_all
      · rfl
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hp.safe hallow], hp.no_level_params hallow⟩
  · intro safety base hvisible hadd
    have hs : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) ci' := by
      have hsf : TrDefVal safety (ves.venv v.safety) (.defnInfo v) ci' :=
        ⟨⟨htr.1.1.sf_mono hs, htr.1.2⟩, htr.2⟩
      exact hsf.mono (wf.mono hs)
    have hci' := hci.mono (hmono.trans (wf.mono hs))
    cases allow with
    | false => exact (wf.hasPrimitives.addConst (hnonprim rfl) hadd).addDefEq
    | true =>
      exact hp.preserves (safety := safety) (venv := ves.venv safety)
        (env' := base) (ci' := ci') rfl (wf.mono DefinitionSafety.le_safe)
        (wf.tr (safety := safety)).wf wf.hasPrimitives htr' hci' hadd

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addTheorem
  refine (checkTheorem.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  refine .pure <| addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn hnonprim
    fun safety _ hheader _ hadd old => ?_
  have hle := wf.mono hheader.1
  have htr' : TrThmVal safety (ves.venv safety) v ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  unfold addOpaque
  refine (checkOpaque.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hci, hfresh, hnonprim, _⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci' :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  refine .pure <| addConst.WF wf (.opaqueInfo v) ci' checkSafety ?_ htr
    (hci.mono hmono) hfresh hnonprim fun _ _ htr hci hadd old => ?_
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · exact .opaque ⟨htr, hname⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => (ves.venv .unsafe).QuotReady := by
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    have hfind' : env.constants.find? ``Eq = some (.inductInfo info) := by
      rw [← (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?]
      exact hfind
    exact (wf.tr (safety := .unsafe)).eq_quotReady hfind'
  | _ => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

/-- Exact declaration-dispatch bridge for inductives.  The primitive-family
precheck is retained in the premise so the verified continuation receives the
same `allowPrimitive` bit as the executable branch. -/
theorem addInductiveDeclaration.WF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (Q : Environment → Prop)
    (Hadd : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types isUnsafe =
        .ok allowPrimitive →
      (Environment.addInductive env lparams nparams types isUnsafe
        allowPrimitive fuel).WF Q) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF Q := by
  have Hcheck :
      (Environment.checkPrimitiveInductive env lparams nparams types
        isUnsafe).WF fun allowPrimitive =>
          (Environment.addInductive env lparams nparams types isUnsafe
            allowPrimitive fuel).WF Q := by
    intro allowPrimitive hallow
    exact Hadd allowPrimitive hallow
  have Hcombined := Hcheck.bind fun _ Hrun => Hrun
  simpa [addDecl] using Hcombined

/-- Declaration-level composition through source checking and nested
lowering.  The continuation starts exactly at `addInductiveAfterLowering`
and receives both the source-syntax certificate and the closed lowering
trace; primitive recognition has already been synchronized with `addDecl`. -/
theorem addInductiveDeclaration.checkedLoweringClosedWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (hclosures : VerifyInductive.MutualInductivesClosed env)
    (Henv : VerifyInductive.EnvironmentTypesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ allowPrimitive res,
      Environment.checkPrimitiveInductive env lparams nparams types
        isUnsafe = .ok allowPrimitive →
      VerifyInductive.SourceSyntaxChecks types →
      VerifyInductive.NestedLoweringResultClosed env fuel.inductiveFuel
        nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF Q := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel Q
  intro allowPrimitive hallow
  apply VerifyInductive.Environment.addInductive.checkedLoweringClosedWF
    env lparams nparams types isUnsafe allowPrimitive fuel hclosures Henv Q
  intro res Hsource Hlower
  exact Hfinish allowPrimitive res hallow Hsource Hlower

/-- Well-formed-environment specialization of the declaration bridge.  This
is the inductive analogue of `addAxiom.WF`/`addTheorem.WF`: all front-end and
lowering obligations are discharged here, while `Hfinish` is precisely the
remaining installation/restoration-to-`AddInduct` proof. -/
theorem addInductiveDeclaration.preservesWF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hclosures : VerifyInductive.MutualInductivesClosed env)
    (Hfinish : ∀ allowPrimitive res,
      Environment.checkPrimitiveInductive env lparams nparams types
        isUnsafe = .ok allowPrimitive →
      VerifyInductive.SourceSyntaxChecks types →
      VerifyInductive.NestedLoweringResultClosed env fuel.inductiveFuel
        nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF fun env' =>
          ∃ ves' : VEnvs, ves'.WF env' ∧
            ∀ safety, ves.venv safety ≤ ves'.venv safety) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun env' =>
        ∃ ves' : VEnvs, ves'.WF env' ∧
          ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  exact addInductiveDeclaration.checkedLoweringClosedWF env lparams nparams
    types isUnsafe fuel hclosures
      (VerifyInductive.VEnvs.WF.environmentTypesClosed wf) _ Hfinish

/-- Declaration forms currently represented by `TrEnv`. Recursive unsafe definitions and
mutual definitions require a recursive-body relation, while inductives require a
proof that the executable declaration builder constructs `AddInduct`. Quotient
initialization additionally needs canonical `Eq` in every safety-indexed model; the
production precheck currently establishes this only for the unsafe model. -/
def _root_.Lean.Declaration.IsModelled : Declaration → Prop
  | .axiomDecl _ | .thmDecl _ | .opaqueDecl _ => True
  | .defnDecl v => v.safety ≠ .unsafe
  | .mutualDefnDecl _ | .quotDecl | .inductDecl .. => False

/-- Successful checked addition of a modelled declaration preserves well-formedness and
extends every safety-indexed abstract environment. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration)
    (hdecl : decl.IsModelled) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => exact addAxiom.WF wf v
  | defnDecl v => exact addNonrecursiveDefinition.WF wf v (by simpa [Declaration.IsModelled] using hdecl)
  | thmDecl v => exact addTheorem.WF wf v
  | opaqueDecl v => exact addOpaque.WF wf v
  | mutualDefnDecl _ => simp [Declaration.IsModelled] at hdecl
  | quotDecl => simp [Declaration.IsModelled] at hdecl
  | inductDecl _ _ _ _ => simp [Declaration.IsModelled] at hdecl
