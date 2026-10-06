import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Inductive

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Context strengthening (`VEnv.Strengthening`) of the abstract environments in
which `addDefinition` runs the verified checker: for an unsafe definition, the
unsafe model and that model extended by the definition as an axiom (its body
is checked there, so that it can refer to itself); otherwise the safe model. -/
def VEnvs.DefinitionStrengthening (ves : VEnvs) (v : DefinitionVal) : Prop :=
  (v.safety = .unsafe → (ves.venv .unsafe).Strengthening ∧
    ∀ ci venv', TrConstVal .unsafe (ves.venv .unsafe) (.defnInfo v) ci →
      ci.toVConstant.WF (ves.venv .unsafe) →
      (ves.venv .unsafe).addConst v.name ci.toVConstant = some venv' →
      venv'.Strengthening) ∧
  (v.safety ≠ .unsafe → (ves.venv .safe).Strengthening)

/-- Context strengthening of the abstract environments in which `addMutual` runs
the verified checker: the model at the block's safety level (headers), and that
model extended by the translated headers as axioms (bodies). -/
def VEnvs.MutualStrengthening (ves : VEnvs) (env : Environment) :
    List DefinitionVal → Prop
  | [] => True
  | v₀ :: rest => (ves.venv v₀.safety).Strengthening ∧
    ∀ cis base, List.Forall₂ (TrMutualHeader v₀.safety (ves.venv v₀.safety) env)
        (v₀ :: rest) cis →
      (ves.venv v₀.safety).addConsts cis = some base → base.Strengthening

/-- The environment hypothesis of `addDecl.WF`: context strengthening
(`VEnv.Strengthening`) of exactly the abstract environments in which checking
`decl` runs the verified type checker.  Strengthening is not monotone, so the
intermediate environments are listed individually; each of them is determined
by `ves` and by the abstract translation of `decl` (see
`VEnvs.DefinitionStrengthening`, `VEnvs.MutualStrengthening` and
`VerifyInductive.InductiveDeclStrengthening`).  Nothing is assumed about the
output environment as such. -/
def _root_.Lean.Declaration.Strengthening (ves : VEnvs) (env : Environment) :
    Declaration → Prop
  | .axiomDecl v => (ves.venv (if v.isUnsafe then .unsafe else .safe)).Strengthening
  | .defnDecl v => ves.DefinitionStrengthening v
  | .thmDecl _ => (ves.venv .safe).Strengthening
  | .opaqueDecl _ => (ves.venv .safe).Strengthening
  | .quotDecl => True
  | .mutualDefnDecl vs => ves.MutualStrengthening env vs
  | .inductDecl lparams nparams types isUnsafe =>
    VerifyInductive.InductiveDeclStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) env lparams nparams types
      isUnsafe {}

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal)
    (hs : (ves.venv (if v.isUnsafe then .unsafe else .safe)).Strengthening) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.axiomInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf hs (.axiomInfo v) false hsafety).run wf hs
    |>.bind fun _ ⟨ci', htr, hci, hn, hnonprim⟩ => ?_
  have hnonprim' :
      Environment.primitives.contains (ConstantInfo.axiomInfo v).name = false := by
    cases hprim : Environment.primitives.contains (ConstantInfo.axiomInfo v).name
    · rfl
    · have := hnonprim (by simp [hprim])
      contradiction
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (by intro _ h; cases h) (by intro _ h; cases h) hnonprim'
    fun _ _ htr hci hadd old => ?_
  · exact .pure ⟨ves', hwf, ci', hstep⟩
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hs : ves.DefinitionStrengthening v) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety)) := by
  unfold addDefinition; split
  · rename_i hunsafe
    have hsU := hs.1 (by simpa using hunsafe)
    refine checkConstantVal.WF wf hsU.1 (.defnInfo v) false DefinitionSafety.unsafe_le
      |>.run wf hsU.1 |>.bind fun _ ⟨ci0, htr, hwfc, hn, hnonprim⟩ => ?_; simp at hnonprim
    refine (checkNoMVarNoFVar.WF _ _ _).bind fun _ h => ?_
    have ⟨vesA, wfA, hstepA⟩ := addConst.WF wf (.axiomInfo { v with isUnsafe := true }) ci0
      .unsafe (fun _ => id) ⟨⟨DefinitionSafety.unsafe_le, htr.1.2.1, htr.1.2.2⟩, htr.2⟩
      hwfc hn (by intro _ h; cases h) (by intro _ h; cases h) hnonprim
      fun _ _ htr' hci' hadd' old =>
        .axiom htr' (by rwa [← old.map_wf.find?'_eq_find?]) hci' hadd' old
    have hadd := (hstepA .unsafe).2.2
    have hsA : (vesA.venv .unsafe).Strengthening := hsU.2 ci0 _ htr hwfc hadd
    refine checkBodyCore.WF (wfA.toVEnvAt .unsafe) hsA (.defnDecl v)
      v.levelParams v.type v.value ci0.type (htr.1.2.2.mono (VEnv.addConst_le hadd)) h
      |>.run1 _ hsA |>.bind fun _ h3 => ?_
    obtain ⟨value', hvalue, hvalueType⟩ := h3
    have hciWF : (⟨ci0, value'⟩ : VDefVal).WF (vesA.venv .unsafe) := by
      show (vesA.venv .unsafe).HasType ci0.uvars [] value' ci0.type
      rw [← htr.1.2.1]; exact hvalueType
    have ⟨ves', hwf', hmono'⟩ := addUnsafeDef.WF wf v ⟨ci0, value'⟩ (vesA.venv .unsafe)
      ‹_› htr hwfc hadd hvalue hciWF hn hnonprim
    exact .pure ⟨ves', hwf', hmono', (nomatch · ‹_›)⟩
  rename_i hnotUnsafe
  have hsS := hs.2 (by simpa using hnotUnsafe)
  refine (checkDefinition.WF wf hsS v).run wf hsS |>.bind
    fun _ ⟨ci', hp, hu, ht, hname, hvalue, hci, hfresh⟩ => ?_
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety ?_ htr (hci.mono hmono) hfresh ?_ ?_
  · exact .pure ⟨ves', hwf, (hstep · |>.le), fun _ => ⟨ci', hstep⟩⟩
  · simp [ConstantInfo.defnInfo_safety]
  · exact fun h => ⟨by rw [ConstantInfo.defnInfo_safety, (hp h).safe], (hp h).no_level_params⟩
  · intro safety base hvisible hadd
    have hs : safety ≤ v.safety := by simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hsf : TrDefVal safety (ves.venv v.safety) (.defnInfo v) ci' :=
      ⟨⟨htr.1.1.sf_mono hs, htr.1.2⟩, htr.2⟩
    have hci' := hci.mono (hmono.trans (wf.mono hs))
    cases eq : Environment.primitives.contains v.name
    · exact (wf.hasPrimitives.addConst eq hadd).addDefEq
    · exact (hp eq).preserves (wf.mono DefinitionSafety.le_safe) wf.tr.wf wf.hasPrimitives
        (hsf.mono (wf.mono hs)) (hci.mono (hmono.trans (wf.mono hs))) hadd

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal)
    (hs : (ves.venv .safe).Strengthening) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.thmInfo v) ci'.toVConstant (ves'.venv safety) := by
  refine (checkTheorem.WF wf hs v).run wf hs |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn
    (by intro _ h; cases h) (by intro _ h; cases h) hnonprim
    fun safety _ hheader _ hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  have hle := wf.mono hheader.1
  have htr' : TrDefVal safety (ves.venv safety) (.thmInfo v) ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal)
    (hs : (ves.venv .safe).Strengthening) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.opaqueInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  refine (checkOpaque.WF wf hs v).run wf hs |>.bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hvalue, hciC, hci, hfresh, hnonprim⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci'.toVConstVal :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.opaqueInfo v) ci'.toVConstVal checkSafety ?_ htr
    (hciC.mono hmono) hfresh (by intro _ h; cases h) (by intro _ h; cases h) hnonprim
    fun safety _ htr hciW hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · have hvis : safety ≤ checkSafety := hsafety ▸ htr.1
    have hto := hmono.trans (wf.mono hvis)
    exact .opaque (ci' := ci') ⟨⟨htr, hname⟩, hvalue.mono hto⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) (hci.mono hto) hadd old

private theorem vconstant_eq_of_fields {a b : VConstant}
    (huvars : a.uvars = b.uvars) (htype : a.type = b.type) : a = b := by
  cases a
  cases b
  simp_all

/-- The exact family arity accepted by `checkEqType` translates to the
canonical abstract equality constant.  This statement is independent of the
surrounding environment because the arity contains only a universe parameter,
sorts, and bound variables. -/
theorem expectedEqType_translation (env : VEnv) (u : Name) :
    TrExprS env [u] [] (expectedEqType u) eqConst.type := by
  unfold expectedEqType eqConst
  change TrExprS env [u] []
    (.forallE `α (.sort (.param u))
      (.forallE .anonymous (.bvar 0)
        (.forallE .anonymous (.bvar 1) (.sort .zero) .default) .default)
      .implicit)
    (.forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
  apply TrExprS.forallE
  · refine ⟨_, VEnv.HasType.sort ?_⟩
    change VLevel.WF 1 (.param 0)
    trivial
  · apply VEnv.IsType.forallE
    · refine ⟨.param 0, ?_⟩
      type_tac
    · apply VEnv.IsType.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
  · exact .sort (by simp [VLevel.ofLevel])
  · apply TrExprS.forallE
    · refine ⟨.param 0, ?_⟩
      type_tac
    · apply VEnv.IsType.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
    · exact .bvar rfl
    · apply TrExprS.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
      · exact .bvar rfl
      · exact .sort rfl

theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => (ves.venv .unsafe).QuotReady := by
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    cases hlevels : info.levelParams with
    | nil => simp_all [bind, Except.bind, pure, Pure.pure, Except.pure]
    | cons u us =>
      cases us with
      | cons _ _ => simp_all [bind, Except.bind, pure, Pure.pure, Except.pure]
      | nil =>
        cases hctors : info.ctors with
        | nil => simp_all [bind, Except.bind, pure, Pure.pure, Except.pure]
        | cons eqRefl ctors =>
          cases ctors with
          | cons _ _ => simp_all [bind, Except.bind, pure, Pure.pure, Except.pure]
          | nil =>
            simp [ExprBuildT.run, bind, Except.bind, pure, Pure.pure,
              Except.pure, hlevels, hctors] at h
            split at h
            · contradiction
            · rename_i htype
              have heqv : (info.type == expectedEqType u) = true := by
                simpa [bne] using htype
              obtain ⟨ci', hci', htr⟩ :=
                (wf.tr (safety := .unsafe)).find? hfind DefinitionSafety.unsafe_le
              have huvars : ci'.uvars = eqConst.uvars := by
                rw [← htr.2.1]
                simp [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
                  hlevels, eqConst]
              have htrExpected : TrExprS (ves.venv .unsafe) [u] []
                  (expectedEqType u) ci'.type := by
                simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
                  hlevels] using htr.2.2.eqv heqv
              have htypeV : ci'.type = eqConst.type := by
                apply TrExprS.unique (by trivial) htrExpected
                exact expectedEqType_translation (ves.venv .unsafe) u
              have hciEq : ci' = eqConst :=
                vconstant_eq_of_fields huvars htypeV
              simpa [VEnv.QuotReady, hciEq] using hci'
  | _ => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

/-- Exact declaration-dispatch bridge for inductives.  The primitive-family
precheck is retained in the premise so the verified continuation receives the
same `allowPrimitive` bit as the executable branch. -/
theorem addInductiveDeclaration.WF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (Q : Environment → Prop)
    (Hadd : ∀ allowPrimitive,
      Primitive.checkInductive env lparams nparams types isUnsafe =
        .ok allowPrimitive →
      (Environment.addInductive env lparams nparams types isUnsafe
        allowPrimitive fuel).WF Q) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF Q := by
  have Hcheck :
      (Primitive.checkInductive env lparams nparams types
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
      Primitive.checkInductive env lparams nparams types
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
    (Hfinish : ∀ allowPrimitive res,
      Primitive.checkInductive env lparams nparams types
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
    types isUnsafe fuel wf.inductivesClosed
      (VerifyInductive.VEnvs.WF.environmentTypesClosed wf) _ Hfinish

/-- Complete checked declaration dispatch across the primitive, ordinary,
and nested execution paths.  The executable primitive precheck selects the
primitive branch; otherwise the verified lowering result selects ordinary
versus the exact nested continuation.  Inductive soundness does not depend on
the presence or interpretation of the separately bootstrapped `Eq` constant.
The independent source specification additionally assumes that the source
declaration has no loose bound variables; the executable only rejects
metavariables and free variables, and nested lowering would silently repair
loose bound variables while re-closing constructor types.  Environment
preservation itself (`finalPreservesWF`) does not need this hypothesis. -/
theorem addInductiveDeclaration.finalResultWF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (HsourcesB : VerifyInductive.SourceBVarClosed types)
    (hstrs : VerifyInductive.InductiveDeclStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) env lparams nparams types
      isUnsafe fuel) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (VerifyInductive.InductiveFinalResult outEnv ves lparams
          nparams types isUnsafe) := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel
    (fun outEnv => Nonempty (VerifyInductive.InductiveFinalResult outEnv ves
      lparams nparams types isUnsafe))
  intro allowPrimitive hallow
  cases allowPrimitive with
  | false =>
    exact VerifyInductive.Environment.addInductive.inductiveFinalResultWF (hstrs := hstrs)
      env lparams nparams types isUnsafe fuel ves wf HsourcesB
  | true =>
    have Hprimitive : VerifyInductive.PrimitiveInductiveShape lparams
        nparams types isUnsafe :=
      (VerifyInductive.checkPrimitiveInductive_eq_true_iff env lparams
        nparams types isUnsafe).mp hallow
    exact
      VerifyInductive.Environment.addInductive.primitiveInductiveFinalResultWF
        (hstrs := by
          have hfalse : isUnsafe = false := Hprimitive.2.2.1
          simpa [hfalse] using hstrs.source)
        env lparams nparams types isUnsafe fuel ves wf Hprimitive

/-- Traditional environment-preservation theorem for the complete inductive
declaration dispatch.  This is unconditional: it is derived from the
well-formedness halves of the three execution branches, not from the
source-facing specification. -/
theorem addInductiveDeclaration.finalPreservesWF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hstrs : VerifyInductive.InductiveDeclStrengthening
      (ves.venv (if isUnsafe then .unsafe else .safe)) env lparams nparams types
      isUnsafe fuel) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel
    (fun outEnv => ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety)
  intro allowPrimitive hallow
  cases allowPrimitive with
  | false =>
    apply VerifyInductive.Environment.addInductive.checkedLoweringClosedWF
      env lparams nparams types isUnsafe false fuel wf.inductivesClosed
      (VerifyInductive.VEnvs.WF.environmentTypesClosed wf)
    intro res Hsources Hlower
    have hlowered : InductiveStrengthening
        (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams res.types
        ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe) := by
      rw [VerifyInductive.inductiveSafety_ne_safe]
      exact hstrs.lowered res Hlower.toResult
    by_cases haux : res.aux2nested.size = 0
    · exact VerifyInductive.Environment.addInductiveAfterLowering.ordinaryFinalModelWF
        (hstrs := hlowered)
        env lparams nparams types isUnsafe fuel res ves wf Hlower.toResult haux
    · exact
        (VerifyInductive.Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF
          env lparams nparams types isUnsafe fuel res ves wf Hsources Hlower
            haux hstrs.source hlowered).mono fun _ ⟨H⟩ => H.modelExtension
  | true =>
    have Hprimitive : VerifyInductive.PrimitiveInductiveShape lparams
        nparams types isUnsafe :=
      (VerifyInductive.checkPrimitiveInductive_eq_true_iff env lparams
        nparams types isUnsafe).mp hallow
    exact
      (VerifyInductive.Environment.addInductive.primitiveInductiveFinalResultWF
        (hstrs := by
          have hfalse : isUnsafe = false := Hprimitive.2.2.1
          simpa [hfalse] using hstrs.source)
        env lparams nparams types isUnsafe fuel ves wf Hprimitive).mono
        fun _ ⟨H⟩ => H.modelExtension

private theorem Except.WF.throw' {e : ε} {Q : α → Prop} : (throw e : Except ε α).WF Q :=
  fun _ h => nomatch h

private theorem Except.WF.throwBind {e : ε} {f : α → Except ε β} {Q : β → Prop} :
    ((throw e : Except ε α) >>= f).WF Q := fun _ h => nomatch h

theorem addMutual.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (vs : List DefinitionVal) (hs : ves.MutualStrengthening env vs) :
    (addMutual env vs).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addMutual
  simp only [reduceIte]
  split <;> [rename_i _ v₀ rest; exact Except.WF.throw']
  obtain ⟨hs0, hsBase⟩ := hs
  split <;> [exact Except.WF.throwBind; skip]
  have hsf : v₀.safety ≤ (if v₀.safety == .unsafe then .unsafe else .safe) := by
    cases v₀.safety with
    | «partial» => exact DefinitionSafety.le_safe
    | _ => exact DefinitionSafety.le_rfl
  refine (TypeChecker.M.WF.run (Q := fun _ =>
    (∃ cis, (v₀ :: rest).Forall₂ (fun v ci =>
      TrMutualHeader v₀.safety (ves.venv v₀.safety) env v ci ∧
      v.safety = v₀.safety ∧ v.levelParams = v₀.levelParams) cis) ∧
    (((v₀ :: rest).map (·.name)).Nodup ∧
      ∀ v ∈ (v₀ :: rest), (∅ : NameSet).contains v.name = false)) wf hs0 ?_).bind fun _ h1 => ?_
  · refine (TypeChecker.M.WF.forInFresh fun v found s => ?_).bind fun _ _ _ h => .pure h
    split <;> [exact .bindThrow .throw; rename_i hsafety]
    split <;> [exact .bindThrow .throw; rename_i hlp]
    split <;> [exact .bindThrow .throw; rename_i hfound]
    simp at hsafety hlp hfound
    rw [← hlp]
    refine (checkConstantVal.WF wf hs0 (.defnInfo v) false ?_ s).bind ?_
    · rw [ConstantInfo.defnInfo_safety, hsafety]; exact DefinitionSafety.le_rfl
    refine fun _ _ _ ⟨ci', htr, hciw, hn, hnp⟩ => .pure ?_; simp at hnp
    exact ⟨hfound, ⟨⟨ci', .bvar 0⟩, ⟨htr, hciw, hn, hnp⟩, hsafety, rfl⟩, rfl⟩
  obtain ⟨⟨cis0, hQ0⟩, hnd, -⟩ := h1
  have hhdr := hQ0.imp fun _ _ h => h.1
  have hpull {P : DefinitionVal → VDefVal → Prop} (h : List.Forall₂ P (v₀ :: rest) cis0)
      {R : DefinitionVal → Prop} (H : ∀ v ci, P v ci → R v) : ∀ v ∈ v₀ :: rest, R v :=
    fun v hv => have ⟨ci, _, hp⟩ := h.forall_exists_l v hv; H v ci hp
  have hbs := hpull hQ0 fun _ _ h => h.2.1
  have hfresh := hpull hhdr fun _ _ h => h.2.2.1
  have hnonprim := hpull hhdr fun _ _ h => h.2.2.2
  have hnameeq : (v₀ :: rest).map (·.name) = cis0.map (·.name) := by
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hhdr.imp fun _ _ h => h.1.2
  have hpullr {P : DefinitionVal → VDefVal → Prop} (h : List.Forall₂ P (v₀ :: rest) cis0)
      {R : VDefVal → Prop} (H : ∀ v ci, P v ci → R ci) : ∀ ci ∈ cis0, R ci :=
    fun ci hc => have ⟨v, _, hp⟩ := h.forall_exists_r ci hc; H v ci hp
  obtain ⟨base, hbase0⟩ := (wf.tr (safety := v₀.safety)).exists_addConsts
    (hpullr hhdr fun _ _ h => h.1.2 ▸ h.2.2.1) (hnameeq ▸ hnd)
  have wfA := VEnvAt.addAxioms hsf (wf.toVEnvAt v₀.safety) hhdr hnd hbase0
  have hsB : base.Strengthening := hsBase cis0 base hhdr hbase0
  refine (TypeChecker.M.WF.run1 (Q := fun _ => ∃ cis',
    cis0.Forall₂ (fun (ci ci' : VDefVal) => ci.toVConstVal = ci'.toVConstVal) cis' ∧
    (v₀ :: rest).Forall₂ (fun v ci' => TrExprS base v.levelParams [] v.value ci'.value ∧
      ci'.WF base) cis') wfA hsB ?_).bind fun _ h2 => ?_
  · refine (TypeChecker.M.WF.forInForall₂ (fun v ci s hd => ?_) hQ0).bind fun _ _ _ h => .pure h
    have hdecl := hd.1.1.1.2.2.mono (VEnv.addConsts_le hbase0)
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF _ v.name v.value)).bind fun _ _ _ hclosed => ?_
    have hclosed' : v.value.FVarsIn
        (· ∈ (TypeChecker.VContext.mk1 wfA hsB v.levelParams).vlctx.fvars) := by
      simpa [TypeChecker.VContext.mk1] using hclosed
    refine hd.2.2 ▸ (TypeChecker.checkType.WF hclosed').bind
      fun valType _ _ ⟨value', valType', _, hval, hvalTy, hhasType⟩ => ?_
    refine (TypeChecker.isDefEq.WF hvalTy hdecl).bind fun equal _ _ hequal => ?_
    split <;> [exact .bindThrow .throw; rename_i heq]
    refine .pure ⟨⟨⟨ci.toVConstVal, value'⟩, rfl, hval, ?_⟩, rfl⟩
    rw [VDefVal.WF, ← hd.1.1.1.2.1]
    exact hhasType.defeqU_r wfA.tr.wf (by trivial) (hequal (by simpa using heq))
  obtain ⟨cis, hRR, hbody⟩ := h2
  rw [VEnv.addConsts_congr hRR] at hbase0
  have : List.Forall₂ (TrMutualHeader v₀.safety (ves.venv v₀.safety) env) (v₀ :: rest) cis :=
    hhdr.trans (h₂ := hRR) fun v ci ci' h1 h2 => by
      have hc : ci.toVConstant = ci'.toVConstant := congrArg VConstVal.toVConstant h2
      exact ⟨h2 ▸ h1.1, hc ▸ h1.2.1, h1.2.2.1, h1.2.2.2⟩
  refine .pure <| addMutualBlock.WF wf v₀.safety (v₀ :: rest) cis base hbs hnd hfresh hnonprim
    (fun ci hc => ?_) hbase0 ((this.and hbody).imp (fun _ _ h => ⟨h.1.1, h.2.1⟩)) (fun ci hc => ?_)
  · obtain ⟨v, -, h⟩ := this.forall_exists_r ci hc; exact h.2.1
  · obtain ⟨v, -, h⟩ := hbody.forall_exists_r ci hc; exact h.2

/-- Declaration forms admitted to the generic environment theorem.  Checked
inductive declarations carry no declaration-specific semantic premise;
ordinary, primitive, and nested evidence is reconstructed from execution. -/
def _root_.Lean.Declaration.IsModelled
    (env : Environment) (ves : VEnvs) : Declaration → Prop
  | .quotDecl => False
  | .inductDecl _ _ _ _ => True
  | _ => True

/-- Successful checked addition of a currently modeled declaration preserves
well-formedness and extends every safety-indexed abstract environment. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (hdecl : decl.IsModelled env ves)
    (hs : decl.Strengthening ves env) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => exact (addAxiom.WF wf v hs).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | thmDecl v => exact (addTheorem.WF wf v hs).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | defnDecl v => exact (addDefinition.WF wf v hs).mono fun _ ⟨ves', hwf, h, _⟩ => ⟨ves', hwf, h⟩
  | opaqueDecl v =>
    exact (addOpaque.WF wf v hs).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | quotDecl => simp [Declaration.IsModelled] at hdecl
  | mutualDefnDecl vs => exact addMutual.WF wf vs hs
  | inductDecl lparams nparams types isUnsafe =>
    exact addInductiveDeclaration.finalPreservesWF wf
      lparams nparams types isUnsafe {} hs

/-- Every already-modeled declaration form preserves the canonical `Eq`
invariant needed by the subsequent quotient and inductive boundaries. -/
theorem addDecl.WFCanonicalEq
    {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) (hEq : VerifyInductive.CanonicalEqEnvs ves)
    (decl : Declaration) (hdecl : decl.IsModelled env ves)
    (hs : decl.Strengthening ves env) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        VerifyInductive.CanonicalEqEnvs ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  (addDecl.WF wf decl hdecl hs).mono fun _ ⟨ves', wf', hle⟩ =>
    ⟨ves', wf', hEq.mono hle, hle⟩

/-! ### Discharging `Declaration.Strengthening` from canonical equality -/

/-- Canonical equality (`VEnv.HasCanonicalEq`) at every safety level. -/
def VEnvs.HasCanonicalEq (ves : VEnvs) : Prop :=
  ∀ safety, (ves.venv safety).HasCanonicalEq

theorem VEnvs.HasCanonicalEq.mono {ves ves' : VEnvs} (h : ves.HasCanonicalEq)
    (hle : ∀ safety, ves.venv safety ≤ ves'.venv safety) : ves'.HasCanonicalEq :=
  fun safety => (h safety).mono (hle safety)

/-- `HasCanonicalEq` contains the `Eq` clause of `CanonicalEqEnvs`. -/
theorem VEnvs.HasCanonicalEq.canonicalEqEnvs {ves : VEnvs} (h : ves.HasCanonicalEq) :
    VerifyInductive.CanonicalEqEnvs ves :=
  fun safety => (h safety).quotReady

private theorem VEnv.addConsts_eq_addConstVals' {env : VEnv} {cis : List VDefVal} :
    env.addConsts cis = env.addConstVals (cis.map (·.toVConstVal)) := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, List.map_cons, VEnv.addConstVals]
    cases env.addConst ci.name ci.toVConstant with
    | none => rfl
    | some middle => exact ih (env := middle)

/-- Strengthening of every environment in which an inductive declaration is
checked, from the well-formedness and canonical equality of the base
environment.  Each stage is a `≤`-extension of `env` (so it contains canonical
`Eq`), and is well formed: headers and constructors are added as well-typed
axioms, and the projection and recursor stages carry their own
well-formedness premise. -/
theorem InductiveStrengthening.ofCanonicalEq {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) :
    InductiveStrengthening env lparams nparams types isUnsafe where
  base := VEnv.strengthening_of_canonicalEq henv heq
  headers _targets _envTypes H hadd :=
    VEnv.strengthening_of_canonicalEq
      (VEnv.WF.addConstVals henv
        (fun ci hci => by
          obtain ⟨_, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_r H ci hci
          exact h.wf) hadd)
      (heq.mono (VEnv.addConstVals_le hadd))
  constructors _decl _envTypes _envCtors H hwf :=
    VEnv.strengthening_of_canonicalEq hwf
      (heq.mono (VEnv.LE.trans (VEnv.addConstVals_le H.typesAdded)
        (VEnv.LE.trans (VEnv.addConstVals_le H.ctorsAdded) VEnv.addProjections_le)))
  constructorsUnprojected _decl _envTypes _envCtors H :=
    VEnv.strengthening_of_canonicalEq
      (VerifyInductive.TrInductDeclCore.envCtorsWF H henv)
      (heq.mono (VEnv.LE.trans (VEnv.addConstVals_le H.typesAdded)
        (VEnv.addConstVals_le H.ctorsAdded)))
  recursors _decl _envTypes _envCtors H _recursors _envRecursors hadd hwf :=
    VEnv.strengthening_of_canonicalEq hwf
      (heq.mono (VEnv.LE.trans (VEnv.addConstVals_le H.typesAdded)
        (VEnv.LE.trans (VEnv.addConstVals_le H.ctorsAdded)
          (VEnv.LE.trans VEnv.addProjections_le (VEnv.addConstVals_le hadd)))))

/-- The hypothesis `Declaration.Strengthening` of `addDecl.WF` holds whenever
every safety-indexed abstract environment contains canonical equality, given
the conjecture `VEnv.strengthening_of_canonicalEq`. -/
theorem _root_.Lean.Declaration.strengthening_of_canonicalEq {env : Environment}
    {ves : VEnvs} (wf : ves.WF env) (heq : ∀ safety, (ves.venv safety).HasCanonicalEq) :
    ∀ decl : Declaration, decl.Strengthening ves env
  | .axiomDecl _ => VEnv.strengthening_of_canonicalEq (wf.tr (safety := _)).wf (heq _)
  | .defnDecl v => by
    refine ⟨fun _ => ⟨VEnv.strengthening_of_canonicalEq (wf.tr (safety := _)).wf (heq _),
      fun ci venv' htr hci hadd => ?_⟩,
      fun _ => VEnv.strengthening_of_canonicalEq (wf.tr (safety := _)).wf (heq _)⟩
    have hadd' : (ves.venv .unsafe).addConstVals [ci] = some venv' := by
      simp only [VEnv.addConstVals, ← htr.2]
      simp [ConstantInfo.name, ConstantInfo.toConstantVal, hadd]
    exact VEnv.strengthening_of_canonicalEq
      (VEnv.WF.addConstVals (wf.tr (safety := _)).wf (by simpa using hci) hadd')
      ((heq _).mono (VEnv.addConst_le hadd))
  | .thmDecl _ => VEnv.strengthening_of_canonicalEq (wf.tr (safety := _)).wf (heq _)
  | .opaqueDecl _ => VEnv.strengthening_of_canonicalEq (wf.tr (safety := _)).wf (heq _)
  | .quotDecl => trivial
  | .mutualDefnDecl [] => trivial
  | .mutualDefnDecl (_ :: _) => by
    refine ⟨VEnv.strengthening_of_canonicalEq (wf.tr (safety := _)).wf (heq _),
      fun cis base hhdr hadd => ?_⟩
    rw [VEnv.addConsts_eq_addConstVals'] at hadd
    refine VEnv.strengthening_of_canonicalEq
      (VEnv.WF.addConstVals (wf.tr (safety := _)).wf (fun ci hci => ?_) hadd)
      ((heq _).mono (VEnv.addConstVals_le hadd))
    obtain ⟨ci', hci', rfl⟩ := List.mem_map.1 hci
    obtain ⟨_, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_r hhdr ci' hci'
    exact h.2.1
  | .inductDecl .. =>
    ⟨InductiveStrengthening.ofCanonicalEq (wf.tr (safety := _)).wf (heq _),
      fun _ _ => InductiveStrengthening.ofCanonicalEq (wf.tr (safety := _)).wf (heq _)⟩

/-- `addDecl.WF` with its per-declaration strengthening hypothesis discharged
from canonical equality in the input environments, via the conjecture
`VEnv.strengthening_of_canonicalEq`. -/
theorem addDecl.WF_of_canonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq)
    (decl : Declaration) (hdecl : decl.IsModelled env ves) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  addDecl.WF wf decl hdecl (Declaration.strengthening_of_canonicalEq wf heq decl)

/-- Iterable form of `addDecl.WF_of_canonicalEq`: canonical equality is
preserved by the output environments, so the theorem applies again to the
next declaration of a replay. -/
theorem addDecl.WFHasCanonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ves.HasCanonicalEq) (decl : Declaration) (hdecl : decl.IsModelled env ves) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ves'.HasCanonicalEq ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  (addDecl.WF_of_canonicalEq wf heq decl hdecl).mono fun _ ⟨ves', wf', hle⟩ =>
    ⟨ves', wf', heq.mono hle, hle⟩

/-- `addDecl.WFCanonicalEq` with its strengthening hypothesis discharged from
canonical equality; the `CanonicalEqEnvs` invariant follows from
`HasCanonicalEq`. -/
theorem addDecl.WFCanonicalEq_of_canonicalEq {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) (heq : ves.HasCanonicalEq)
    (decl : Declaration) (hdecl : decl.IsModelled env ves) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        VerifyInductive.CanonicalEqEnvs ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  addDecl.WFCanonicalEq wf heq.canonicalEqEnvs decl hdecl
    (Declaration.strengthening_of_canonicalEq wf heq decl)
