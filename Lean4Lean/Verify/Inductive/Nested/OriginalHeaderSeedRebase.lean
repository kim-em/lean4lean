import Lean4Lean.Verify.Inductive.Recursor.Origins
import Lean4Lean.Verify.Inductive.Recursor.Telescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem VExpr.wrapForalls_domains_inj
    (hlen : left.length = right.length)
    (H : VExpr.wrapForalls left residual =
      VExpr.wrapForalls right residual) :
    left = right := by
  exact VExpr.wrapForalls_prefix_domains_eq
    (n := left.length) (suffix := []) (leftBody := residual)
    (rightBody := residual) rfl hlen.symm (by simpa using H)

/-- Adding constants changes no definitional-equality rules.  This exact
equality is the missing reverse-facing companion to `VEnv.addConstVals_le`:
the latter is sufficient for monotone typing transport, while nested header
restoration compares two different constant batches installed over the same
rule environment. -/
theorem VEnv.addConstVals_defeqs_eq
    {base out : VEnv} {constants : List VConstVal}
    (H : base.addConstVals constants = some out) :
    out.defeqs = base.defeqs := by
  induction constants generalizing base with
  | nil =>
      simp [VEnv.addConstVals] at H
      subst out
      rfl
  | cons ci constants ih =>
      simp only [VEnv.addConstVals] at H
      cases hadd : base.addConst ci.name ci.toVConstant with
      | none => simp [hadd] at H
      | some next =>
          rw [hadd] at H
          rw [ih H]
          unfold VEnv.addConst at hadd
          split at hadd <;> cases hadd
          rfl

theorem VEnv.addConstVals_projections_eq
    {base out : VEnv} {constants : List VConstVal}
    (H : base.addConstVals constants = some out) :
    out.projections = base.projections := by
  induction constants generalizing base with
  | nil =>
      simp [VEnv.addConstVals] at H
      subst out
      rfl
  | cons ci constants ih =>
      simp only [VEnv.addConstVals] at H
      cases hadd : base.addConst ci.name ci.toVConstant with
      | none => simp [hadd] at H
      | some next =>
          rw [hadd] at H
          rw [ih H]
          unfold VEnv.addConst at hadd
          split at hadd <;> cases hadd
          rfl

/-- Two successful constant batches over the same base agree away from the
names installed by the source batch.  This is the environment relation used
to move a lowered header's family-independent prefix into the independently
rebuilt source block: no equality between the batches themselves is needed. -/
theorem VEnv.addConstVals_LEExcept
    {base source target : VEnv} {sourceConstants targetConstants : List VConstVal}
    {changed : Name -> Prop}
    (Hsource : base.addConstVals sourceConstants = some source)
    (Htarget : base.addConstVals targetConstants = some target)
    (Hchanged : forall ci, ci ∈ sourceConstants -> changed ci.name) :
    VEnv.LEExcept changed source target where
  constants := by
    intro name ci hlookup hunchanged
    have hne : forall value, value ∈ sourceConstants -> value.name ≠ name := by
      intro value hvalue hname
      apply hunchanged
      rw [← hname]
      exact Hchanged value hvalue
    have hbase : base.constants name = some ci := by
      rw [VEnv.addConstVals_constants_of_forall_ne Hsource hne] at hlookup
      exact hlookup
    exact (VEnv.addConstVals_le Htarget).constants hbase
  defeqs := by
    intro df hdf
    rw [VEnv.addConstVals_defeqs_eq Hsource] at hdf
    rw [VEnv.addConstVals_defeqs_eq Htarget]
    exact hdf
  projections := by
    rw [VEnv.addConstVals_projections_eq Hsource]
    rw [VEnv.addConstVals_projections_eq Htarget]
    exact id
  eliminators := by
    rw [VEnv.addConstVals_eliminators Hsource, VEnv.addConstVals_eliminators Htarget]
    exact id

/-- Constructor environments produced from two independently translated
inductive blocks over the same base agree away from the first block's own
header and constructor names.  In the nested application the first block is
the lowered declaration and the second is the original source declaration. -/
theorem TrInductDeclCore.ctorEnvsLEExcept
    (Hfrom : TrInductDeclCore base fromLparams fromNparams fromTypes
      fromUnsafe fromDecl fromEnvTypes fromEnvCtors)
    (Hto : TrInductDeclCore base toLparams toNparams toTypes
      toUnsafe toDecl toEnvTypes toEnvCtors) :
    VEnv.LEExcept (fun name => name ∈ fromDecl.sourceNames)
      fromEnvCtors toEnvCtors := by
  have HfromAdded : base.addConstVals
      (fromDecl.typeConstants ++ fromDecl.constructorConstants) =
      some fromEnvCtors :=
    VEnv.addConstVals_append Hfrom.typesAdded Hfrom.ctorsAdded
  have HtoAdded : base.addConstVals
      (toDecl.typeConstants ++ toDecl.constructorConstants) =
      some toEnvCtors :=
    VEnv.addConstVals_append Hto.typesAdded Hto.ctorsAdded
  apply VEnv.addConstVals_LEExcept HfromAdded HtoAdded
  intro ci hci
  simp only [List.mem_append] at hci
  rcases hci with htype | hctor
  · unfold VInductDecl.sourceNames
    exact List.mem_append_left _ (List.mem_map.mpr ⟨ci, htype, rfl⟩)
  · unfold VInductDecl.sourceNames
    exact List.mem_append_right _ (List.mem_map.mpr ⟨ci, hctor, rfl⟩)

/-- Every source-block name is absent from the independent environment in
which its headers were checked.  This follows from successful abstract
installation, rather than from a separate freshness premise. -/
theorem TrInductDeclCore.baseAvoidsSourceNames
    (H : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    {name : Name} {ci : VConstant}
    (hlookup : base.constants name = some ci) :
    name ∉ decl.sourceNames := by
  intro hname
  have Hadd : base.addConstVals
      (decl.typeConstants ++ decl.constructorConstants) = some envCtors :=
    VEnv.addConstVals_append H.typesAdded H.ctorsAdded
  have Hfresh := (VEnv.addConstVals_names_fresh Hadd).2
  unfold VInductDecl.sourceNames at hname
  simp only [List.mem_append] at hname
  rcases hname with htype | hctor
  · rcases List.mem_map.mp htype with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_left _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction
  · rcases List.mem_map.mp hctor with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_right _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction

end VerifyInductive
end Lean4Lean
