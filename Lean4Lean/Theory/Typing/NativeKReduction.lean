import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Declaration-derived nullary constructor reconstruction for native K
reduction. The constructor is fixed by installed singleton-family metadata;
its arguments are the supplied native parameter spine. Reconstructing a
constructor is permitted only when both the actual major and this exact
constructor inhabit the same proposition. This checks the constructor's
result indices, rather than treating every indexed singleton as unindexed.

This is the nullary component of native singleton reconstruction. General
singleton reconstruction must recover data fields from syntactically fixed
recursor indices and synthesize proof fields by declaration-generated case
projections into Prop. It must not choose arbitrary constructor witnesses.
-/

namespace Lean4Lean.VEnv
open Lean4Lean VExpr
variable {env : VEnv} {U : Nat}

/-- The reconstruction function contains no term search or equality oracle. -/
def nativeNullaryConstructor (info : VProjectionInfo) (levels : List VLevel)
    (parameters : List VExpr) : VExpr :=
  VExpr.mkApps (.const info.ctorName levels) parameters

/-- A nullary singleton's checked native parameter telescope. Metadata comes
from an installed declaration, and the entire constructor telescope consists
of its common parameters; an apparent syntactic arity is insufficient. -/
def NativeNullaryConstructor (env : VEnv) (family : Name)
    (info : VProjectionInfo) : Prop :=
  env.projections family info ∧ ∃ domains indices : List VExpr,
    domains.length = info.nparams ∧ indices.length = info.nindices ∧
    env.IsDefEqU info.uvars [] info.ctorType
      (VExpr.wrapForalls domains (VExpr.mkApps (.const family (VLevel.params info.uvars))
        (VExpr.bvarRange info.nparams info.nparams ++ indices)))

/-- The result family and its specialized indices are fixed before
reconstruction. The typed constructor premise checks this exact index tuple;
there is no definitional-equality premise between arbitrary terms. -/
structure NativeKReconstruction (env : VEnv) (U : Nat) (Γ : List VExpr)
    (family : Name) (info : VProjectionInfo) (levels : List VLevel)
    (parameters indices : List VExpr) (major : VExpr) : Prop where
  declaration : NativeNullaryConstructor env family info
  levels_length : levels.length = info.uvars
  levels_wf : ∀ level ∈ levels, level.WF U
  parameters_length : parameters.length = info.nparams
  indices_length : indices.length = info.nindices
  family_prop : env.HasType U Γ
    (VExpr.mkApps (.const family levels) (parameters ++ indices)) (.sort .zero)
  major_typed : env.HasType U Γ major
    (VExpr.mkApps (.const family levels) (parameters ++ indices))
  constructor_typed : env.HasType U Γ (nativeNullaryConstructor info levels parameters)
    (VExpr.mkApps (.const family levels) (parameters ++ indices))

theorem NativeKReconstruction.defeq
    (H : NativeKReconstruction env U Γ family info levels parameters indices major) :
    env.IsDefEq U Γ major (nativeNullaryConstructor info levels parameters)
      (VExpr.mkApps (.const family levels) (parameters ++ indices)) :=
  .proofIrrel H.family_prop H.major_typed H.constructor_typed

/-- Replacing only the major in a typed native application is sound even
when its dependent result type mentions that major. -/
theorem NativeKReconstruction.app_defeq
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : NativeKReconstruction env U Γ family info levels parameters indices major)
    (hfn : env.HasType U Γ fn (.forallE domain body))
    (hmajor : env.HasType U Γ major domain) :
    env.IsDefEq U Γ (.app fn major)
      (.app fn (nativeNullaryConstructor info levels parameters)) (body.inst major) := by
  exact .appDF hfn ((IsDefEqU.of_l henv hΓ ⟨_, H.defeq⟩ hmajor))

/-- A concrete native K preprocessing step. The native recursor head and
constructor originate in one installed iota equation. Its actual parameter
prefix determines the reconstructed constructor arguments; its constructor
universe template determines the specialized universe spine. This first rule
covers direct nullary families, before parameter-specialized reconstruction. -/
inductive NativeKHeadStep (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → VExpr → Prop where
  | intro {equation : VDefEq} {info : VProjectionInfo}
      {recursorLevels ctorLevels : List VLevel} {parameters pre indices domains : List VExpr}
      {major : VExpr} :
    env.defeqs equation →
    equation.lhs = VExpr.wrapLams domains (.app
      (VExpr.mkApps (.const recursor recursorLevels) pre)
      (VExpr.mkApps (.const info.ctorName ctorLevels)
        (VExpr.bvarRange info.nparams domains.length))) →
    (hparameters : parameters = actualArguments.take info.nparams) →
    NativeKReconstruction env U Γ family info (ctorLevels.map (·.inst actualLevels))
      parameters indices major →
    NativeKHeadStep env U Γ
      (.app (VExpr.mkApps (.const recursor actualLevels) actualArguments) major)
      (.app (VExpr.mkApps (.const recursor actualLevels) actualArguments)
        (nativeNullaryConstructor info (ctorLevels.map (·.inst actualLevels)) parameters))

theorem NativeKHeadStep.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : NativeKHeadStep env U Γ e e') (ht : env.HasType U Γ e resultType) :
    env.IsDefEqU U Γ e e' := by
  cases H with
  | intro _ _ _ h =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact ⟨_, h.app_defeq henv hΓ hf ha⟩

end Lean4Lean.VEnv
