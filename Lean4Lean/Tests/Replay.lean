import Lean4Lean.Verify.Replay

/-! The pure replay core.

* `replayFresh` replays a hand-built constant table (an axiom, an inductive type, a definition,
  an inductive predicate and a theorem using them) from the empty environment: it adds the five
  declarations, and every source constant, including the constructors and recursors the kernel
  generated, is present in the result and agrees with the source.
* A source constructor that differs from the generated one is rejected by the postponed
  constructor check, and a source recursor that differs is rejected by the postponed recursor
  check.
* A source inductive type whose metadata differs from the generated one is rejected by the final
  agreement check. -/

namespace Lean4Lean.Tests.Replay

axiom A : Type

inductive T : Type
  | a
  | b (x : A)

def d : T := .a

inductive P : T → Prop
  | mk : P d

theorem thm : P d := .mk

open Lean Lean4Lean.Replay

def sourceNames : List Name :=
  [``A, ``T, ``T.a, ``T.b, ``T.rec, ``d, ``P, ``P.mk, ``P.rec, ``thm]

def sourceTable : CoreM (Std.HashMap Name ConstantInfo) := do
  let env ← getEnv
  sourceNames.foldlM (init := {}) fun m n => do
    let some ci := env.find? n | throwError "missing test constant {n}"
    return m.insert n ci

def check (cond : Bool) (msg : String) : CoreM Unit :=
  unless cond do throwError msg

def errorText : ReplayError → String
  | .kernel n _ => s!"kernel error at {n}"
  | .msg s => s

run_meta do
  let src ← sourceTable
  match replayFresh src with
  | .error e => throwError "replayFresh failed: {errorText e}"
  | .ok r =>
    check (r.numAdded == 5) s!"expected 5 declarations, got {r.numAdded}"
    check (r.checked.length == sourceNames.length) "not every source constant was checked"
    for n in sourceNames do
      check (r.checked.contains n) s!"{n} was not checked"
      let some ci' := r.env.find? n | throwError "{n} is missing from the replayed environment"
      check (ci' == src[n]!) s!"{n} differs from the source"
  -- Only the dependency cone of `d` is replayed with `decl := some d`.
  match replayFresh src (decl := some ``d) with
  | .error e => throwError "replayFresh (decl := d) failed: {errorText e}"
  | .ok r =>
    check (r.numAdded == 3) s!"expected 3 declarations for the cone of d, got {r.numAdded}"
    check ((r.env.find? ``thm).isNone) "thm is outside the cone of d"
    check (!r.checked.contains ``thm) "thm is outside the cone of d"

/-- Replay `src` with the constant `n` replaced by `f` of it, and return the error text. -/
def replayError (src : Std.HashMap Name ConstantInfo) (n : Name)
    (f : ConstantInfo → ConstantInfo) : CoreM String := do
  match replayFresh (src.insert n (f src[n]!)) with
  | .ok _ => throwError "a corrupted {n} was accepted"
  | .error e => return errorText e

run_meta do
  let src ← sourceTable
  -- A source constructor with the wrong constructor index.
  let e ← replayError src ``T.b fun
    | .ctorInfo v => .ctorInfo { v with cidx := 0 }
    | ci => ci
  check (e == s!"Invalid constructor {``T.b}") s!"unexpected error: {e}"
  -- A source recursor with the wrong number of minor premises.
  let e ← replayError src ``T.rec fun
    | .recInfo v => .recInfo { v with numMinors := v.numMinors + 1 }
    | ci => ci
  check (e == s!"Invalid recursor {``T.rec}") s!"unexpected error: {e}"
  -- A source inductive type whose recursive flag is wrong: no constructor or recursor check
  -- covers it, the final agreement check does.
  let e ← replayError src ``T fun
    | .inductInfo v => .inductInfo { v with isRec := true }
    | ci => ci
  check (e == s!"Replayed constant {``T} differs from the source") s!"unexpected error: {e}"

end Lean4Lean.Tests.Replay
