import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjCtorType
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.HTS

/-! # Validity of a projection entry (stage C, decision D11)

The soundness cases of the projection rules (`projDF`, `projIota`, `structEta`, `unitLike`) need
semantic facts about the registered constructor and family that come from derivations in the
environment in which the entry's family and constructor were checked (`VEnv.ProjDeclAt`): the
constructor type is a sound telescope, and the family's declared type is soundly a telescope
ending in the recorded result sort. As for rules (`RuleValid`) and eliminator rules
(`ElimValid`), these facts are provided by the induction along the declaration history: the
types environment of an entry is earlier in the history, so soundness of its derivations in the
model of the final environment is available when the entry is registered. `ProjValid` records
exactly that soundness; it is not a hypothesis about the entry itself. -/

namespace Lean4Lean

/-- The origin of a projection entry (`VEnv.ProjDecl`), at a given types environment. -/
def VEnv.ProjDeclAt (env envTypes : VEnv) (S : Name) (info : VProjectionInfo) : Prop :=
  ∃ (base : VEnv) (dsb : List VDecl) (decl : VInductDecl) (type : VInductiveType)
    (ctor : VConstVal),
    base.WF' dsb ∧ base.addConstVals decl.typeConstants = some envTypes ∧ envTypes ≤ env ∧
    envTypes.Ordered ∧ type ∈ decl.types ∧ type.ctors = [ctor] ∧ type.name = S ∧
    info.uvars = decl.uvars ∧ info.nparams = decl.nparams ∧ info.nindices = type.numIndices ∧
    info.resultLevel = type.resultLevel ∧ info.ctorName = ctor.name ∧ info.ctorType = ctor.type ∧
    ctor.uvars = decl.uvars ∧ envTypes.IsType decl.uvars [] ctor.type ∧
    decl.RawCtorShape type ctor ∧ decl.sourceNames.Nodup ∧ decl.SourceParameterWF base

theorem VEnv.projDecl_iff {env : VEnv} {S : Name} {info : VProjectionInfo} :
    env.ProjDecl S info ↔ ∃ envTypes, env.ProjDeclAt envTypes S info :=
  ⟨fun ⟨b, e, d, h⟩ => ⟨e, b, d, h⟩, fun ⟨e, b, d, h⟩ => ⟨b, e, d, h⟩⟩

theorem VEnv.ProjDeclAt.origin {env envTypes : VEnv} {S : Name} {info : VProjectionInfo}
    (h : env.ProjDeclAt envTypes S info) : env.ProjDecl S info :=
  VEnv.projDecl_iff.2 ⟨_, h⟩

namespace VEnv
namespace Model

/-- Soundness, with the semantic typing derivations of both sides, of every strong derivation of
an earlier environment `E`, in the model of `env` at the target context `Δ`. This is the
conclusion of `Model.sound` for `E`. -/
def SoundTypedIn (env E : VEnv) (U : Nat) (Δ : List VExpr) : Prop :=
  ∀ {Γ t t' T}, E.IsDefEqStrong U Γ t t' T →
    SoundAt env U Δ Γ t t' T ∧ HTS env U Δ Γ t T ∧ HTS env U Δ Γ t' T

theorem SoundTypedIn.soundIn {env E : VEnv} {U : Nat} {Δ : List VExpr}
    (h : SoundTypedIn env E U Δ) : SoundIn env E U Δ := fun H => (h H).1

/-- Static facts about a projection entry of a well-formed environment, used by the
soundness cases of the projection rules. Every field is a property of the environment that is
proved for well-formed environments (`VEnv.WF.projStatic`); none is a semantic assumption. -/
structure ProjStatic (env : VEnv) (S : Name) (info : VProjectionInfo) : Prop where
  famRigid : env.Rigid S
  ctorRigid : env.Rigid info.ctorName
  famNotInstalledCtor : ¬ IsInstalledCtor env S
  famNotProjCtor : ¬ IsProjCtor env S
  ctorClosed : info.ctorType.Closed

/-- **Validity of a projection entry** in the model of `env`: its static facts, and an origin
whose types environment is sound in the model of `env`, at every target context. -/
def ProjValid (env : VEnv) (S : Name) (info : VProjectionInfo) : Prop :=
  ProjStatic env S info ∧ ∃ envTypes, env.ProjDeclAt envTypes S info ∧
    ∀ U Δ, OnCtx Δ (env.IsType U) → SoundTypedIn env envTypes U Δ

end Model
end VEnv
end Lean4Lean
