import Lean4Lean.Verify.Inductive.Basic
import Lean4Lean.Verify.TypeChecker.CheckingContext
import Lean4Lean.Verify.TypeChecker.MLCtxLemmas

/-! # The checker context of the inductive pipeline

`ContextWF c` is the invariant of an `AddInductive.Context` (`Inductive/Add.lean`) in which the
executable inductive checker runs embedded type-checker calls: the abstract environment `venv`
of the kernel environment `c.env` with the checking invariant (`CheckingEnv.Valid`, wave 1B)
and the two recursor facts the checker reads (`RecursorShapesCoherent`, `IotaRulesRegistered`,
wave 1A's `CheckerEnv`), the main local context `mlctx` with its translation, and the embedded
checking context (`CheckBase`). `ContextWF.initial` is the context `Environment.addInductive`
starts from; `ContextWF.withEnv` moves it to a larger kernel environment with the same local
context, as `AddInductive.withEnv` does after each installation stage.

Wave 2 scaffold: the structure's fields are the interface (frozen); the frame operations of the
source branch (`withLocalDecl`, `withCheckedLocalDecl`, `RecursorContextWF`, ...) are the
`Header/`+`Context/` agent's to port beneath it.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The invariant of an `AddInductive.Context`: its kernel environment has the abstract model
`venv` with the checking invariant and the recursor facts the checker reads, its local context
is the main metacontext `mlctx` (all λ-declarations, fresh for both name generators), and the
checking context `c.checkLCtx` embeds in it. -/
structure ContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv
  /-- The shapes of the visible recursors (wave 1A's `CheckerEnv.shapes`). -/
  shapes : RecursorShapesCoherent c.safety c.env.constants venv
  /-- The ι rules of the visible recursors are registered (wave 1A's `CheckerEnv.iota`). -/
  iota : IotaRulesRegistered c.safety c.env venv

  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  typeCheckerLParams_eq : c.typeCheckerLParams = none
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv
  /-- The semantic checker context, embedded in the main one. -/
  check : CheckBase venv c.lparams mlctx c.lctx c.checkLCtx

/-- What the embedded type checker reads of the context's environment. -/
def ContextWF.checkerEnv (H : ContextWF c) : CheckerEnv c.safety c.env H.venv :=
  { H.checking with shapes := H.shapes, iota := H.iota }

theorem ContextWF.wf (H : ContextWF c) : H.venv.WF := H.checking.tr.wf

theorem ContextWF.map_wf (H : ContextWF c) : c.env.constants.WF := H.checking.tr.map_wf

/-- The context `Environment.addInductive` runs the ordinary and nested branches in
(`addInductiveAfterLowering`). -/
def initialContext (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context where
  env; lparams; safety; allowPrimitive; fuel

/-- The initial context is well formed under the environment model at its safety level. -/
def ContextWF.initial {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) (lparams : List Name)
    (allowPrimitive : Bool) (fuel : FuelConfig) :
    ContextWF (initialContext env lparams safety allowPrimitive fuel) where
  venv := ves.venv safety
  checking := wf.toCheckingValid safety
  shapes := (wf.toVEnvAt safety).recursorShapes
  iota := (wf.tr (safety := safety)).iotaRulesRegistered
  mlctx := .nil
  mlctx_wf := trivial
  typeCheckerLParams_eq := rfl
  onlyLams := MLCtxOnlyLams.nil
  lctx_eq := rfl
  ngen_prefix := rfl
  indFresh := nofun
  kernelFresh := nofun
  check := CheckBase.nil (wf.tr (safety := safety)).wf.orderedStrong trivial

@[simp] theorem ContextWF.initial_venv {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) (lparams : List Name) (allowPrimitive : Bool)
    (fuel : FuelConfig) :
    (ContextWF.initial wf safety lparams allowPrimitive fuel).venv = ves.venv safety := rfl

@[simp] theorem ContextWF.initial_mlctx {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) (lparams : List Name) (allowPrimitive : Bool)
    (fuel : FuelConfig) :
    (ContextWF.initial wf safety lparams allowPrimitive fuel).mlctx = .nil := rfl

/-- Keep the local checker state while moving to a kernel and abstract environment pair
known to represent the same extension (`AddInductive.withEnv`). -/
def ContextWF.withEnv (H : ContextWF c) {env' : Environment} {venv' : VEnv}
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hshapes : RecursorShapesCoherent c.safety env'.constants venv')
    (hiota : IotaRulesRegistered c.safety env' venv')
    (hle : H.venv ≤ venv') :
    ContextWF { c with env := env' } where
  venv := venv'
  checking := hchecking
  shapes := hshapes
  iota := hiota
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := H.check.mono hle

@[simp] theorem ContextWF.withEnv_venv (H : ContextWF c) {env' : Environment} {venv' : VEnv}
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hshapes : RecursorShapesCoherent c.safety env'.constants venv')
    (hiota : IotaRulesRegistered c.safety env' venv') (hle : H.venv ≤ venv') :
    (H.withEnv hchecking hshapes hiota hle).venv = venv' := rfl

@[simp] theorem ContextWF.withEnv_mlctx (H : ContextWF c) {env' : Environment} {venv' : VEnv}
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hshapes : RecursorShapesCoherent c.safety env'.constants venv')
    (hiota : IotaRulesRegistered c.safety env' venv') (hle : H.venv ≤ venv') :
    (H.withEnv hchecking hshapes hiota hle).mlctx = H.mlctx := rfl

end VerifyInductive
end Lean4Lean
