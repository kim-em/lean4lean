import Lean4Lean.Verify.Inductive.PrimitiveDispatch
import Lean4Lean.Verify.Inductive.Header.SemanticAssembly
import Lean4Lean.Verify.Inductive.Header.Installation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A finite abstract constant batch can be installed whenever all names are
fresh in the source environment and pairwise distinct. -/
theorem VEnv.exists_addConstVals
    {env : VEnv} {values : List VConstVal}
    (hfresh : ∀ value ∈ values, env.constants value.name = none)
    (hnodup : (values.map (·.name)).Nodup) :
    ∃ out, env.addConstVals values = some out := by
  induction values generalizing env with
  | nil => exact ⟨env, rfl⟩
  | cons value values ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases VEnv.addConst_eq_none
      (ci := value.toVConstant) (hfresh value (by simp)) with
      ⟨next, hnext⟩
    have htailFresh : ∀ later ∈ values,
        next.constants later.name = none := by
      intro later hlater
      rw [VEnv.addConst_constants_eq hnext]
      have hne : value.name ≠ later.name := by
        intro heq
        exact hnodup.1 (List.mem_map.mpr ⟨later, hlater, heq.symm⟩)
      simp [hne, hfresh later (by simp [hlater])]
    rcases ih htailFresh hnodup.2 with ⟨out, hout⟩
    exact ⟨out, by simp [VEnv.addConstVals, hnext, hout]⟩

/-- Successful production header installation always determines a matching
abstract atomic batch, even when primitive reserved names are allowed.  The
result deliberately stops at `AtomicAddConstants`: no validity claim is made
for the header-only abstract environment. -/
theorem AddInductive.declareInductiveTypes.installsSemanticHeadersAtomicWF
    (Hc : ContextWF c)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams numParams commonParams commonLevel indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ outVEnv,
          Hc.venv.addConstVals Hsemantic.headers.targets = some outVEnv ∧
          AtomicAddConstants c.safety c.env Hc.venv
            (List.zip
              ((AddInductive.inductiveTypeInfos stats numParams indTypes
                numNested isUnsafe c.lparams).toList.map
                  (fun info => .inductInfo info))
              Hsemantic.headers.targets)
            outEnv outVEnv := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Hentries :=
    AddInductive.inductiveTypeInfos.translatedMaterializedHeaders
      (stats := stats) (numParams := numParams) (numNested := numNested)
      Hsemantic.headers hindices hvisible
  have Hproduction := declareInductiveTypeInfos_refines c.allowPrimitive
    infos.toList c.env Hc.checking.tr.map_wf
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  intro outEnv hout
  have Hdeclared := Hproduction outEnv hout
  have hnames : infos.toList.map (fun info => info.name) =
      Hsemantic.headers.targets.map (·.name) := by
    rw [← List.forall₂_eq, List.forall₂_map_left_iff,
      List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ _ Hentry => Hentry.1.2)
      Hentries
  have hfresh : ∀ value ∈ Hsemantic.headers.targets,
      Hc.venv.constants value.name = none := by
    intro value hvalue
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hentries value hvalue with
      ⟨info, hinfo, Hentry⟩
    have hprod : c.env.find? value.name = none := by
      rw [← Hentry.1.2]
      exact Hdeclared.sourceFresh info hinfo
    cases habstract : Hc.venv.constants value.name with
    | none => rfl
    | some ci =>
      rcases Hc.checking.tr.find?_iff.mpr ⟨ci, habstract⟩ with
        ⟨source, hsource, _⟩
      rw [hprod] at hsource
      contradiction
  have hnodup : (Hsemantic.headers.targets.map (·.name)).Nodup := by
    rw [← hnames]
    exact Hdeclared.namesNodup
  rcases VEnv.exists_addConstVals hfresh hnodup with ⟨outVEnv, habstract⟩
  have Hatomic := AtomicAddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive) Hc.checking.tr Hentries VEnv.LE.rfl
      habstract
  exact ⟨outVEnv, habstract, Hatomic outEnv hout⟩

/-- The semantic header traversal and a successful atomic header installation
determine raw constructor targets for either canonical primitive source.
These targets are finite and source-derived; no declaration skeleton is an
input. -/
theorem PrimitiveInductiveShape.checkedConstructorRows
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        env lparams nparams params commonLevel types)
    (htypesAdded : env.addConstVals Hsemantic.headers.targets =
      some envTypes) :
    Nonempty (CheckedSourceConstructorRows envTypes lparams types) := by
  rcases Hshape with ⟨rfl, rfl, rfl, hbool | ⟨binderName, binderInfo, hnat⟩⟩
  · subst types
    rcases List.Forall₂.leftSingleton Hsemantic.headers.translations with
      ⟨target, htargets, Htarget⟩
    have hlookup : envTypes.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      simp [htargets]
    let falseVal : VConstVal :=
      { name := ``Bool.false, uvars := 0, type := .const target.name [] }
    let trueVal : VConstVal :=
      { name := ``Bool.true, uvars := 0, type := .const target.name [] }
    have hconst : TrExprS envTypes [] [] (.const ``Bool [])
        (.const target.name []) := by
      simpa [Htarget.name] using
        (TrExprS.const (env := envTypes) (Us := []) (Δ := []) hlookup
          (by rfl) (by simp [Htarget.uvars]))
    have Hfalse : TrSourceConstRaw envTypes [] ``Bool.false
        (.const ``Bool []) falseVal := by
      exact ⟨rfl, rfl, by simpa [falseVal] using hconst⟩
    have Htrue : TrSourceConstRaw envTypes [] ``Bool.true
        (.const ``Bool []) trueVal := by
      exact ⟨rfl, rfl, by simpa [trueVal] using hconst⟩
    exact ⟨{
      targets := [[falseVal, trueVal]]
      translations := .cons (.cons Hfalse (.cons Htrue .nil)) .nil }⟩
  · subst types
    rcases List.Forall₂.leftSingleton Hsemantic.headers.translations with
      ⟨target, htargets, Htarget⟩
    have hlookup : envTypes.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      simp [htargets]
    have htargetType : target.type = .sort (.succ .zero) := by
      have hcanonical : TrExprS env [] [] (.sort (.succ .zero))
          (.sort (.succ .zero)) := TrExprS.sort rfl
      exact TrExprS.unique (by trivial) Htarget.type hcanonical
    have hconst (Delta : VLCtx) : TrExprS envTypes [] Delta
        (.const ``Nat []) (.const target.name []) := by
      simpa [Htarget.name] using
        (TrExprS.const (env := envTypes) (Us := []) (Δ := Delta) hlookup
          (by rfl) (by simp [Htarget.uvars]))
    have hconstIsType (Gamma : List VExpr) :
        envTypes.IsType 0 Gamma (.const target.name []) := by
      refine ⟨.succ .zero, ?_⟩
      simpa [htargetType, VExpr.instL, VLevel.inst] using
        (VEnv.HasType.const (U := 0) (ls := []) (Γ := Gamma) hlookup
          (by simp) (by simp [Htarget.uvars]))
    let zeroVal : VConstVal :=
      { name := ``Nat.zero, uvars := 0, type := .const target.name [] }
    let succVal : VConstVal := {
      name := ``Nat.succ
      uvars := 0
      type := .forallE (.const target.name []) (.const target.name []) }
    have Hzero : TrSourceConstRaw envTypes [] ``Nat.zero
        (.const ``Nat []) zeroVal := by
      exact ⟨rfl, rfl, by simpa [zeroVal] using hconst []⟩
    have Hsucc : TrSourceConstRaw envTypes [] ``Nat.succ
        (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
        succVal := by
      refine ⟨rfl, rfl, ?_⟩
      simpa [succVal] using
        (TrExprS.forallE (env := envTypes) (Us := []) (Δ := [])
          (hconstIsType []) (hconstIsType [.const target.name []])
          (hconst []) (hconst [(none, .vlam (.const target.name []))]))
    exact ⟨{
      targets := [[zeroVal, succVal]]
      translations := .cons (.cons Hzero (.cons Hsucc .nil)) .nil }⟩

end VerifyInductive
end Lean4Lean
