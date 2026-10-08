import Lean4Lean.Theory.Inductive.SingletonReconstruction

/-!
Run with `lake env lean docs/inductives/history/DependentSingletonObstruction.lean`.

This is a reproduction of the current reconstruction obstruction, not a
regression requiring a future generator to preserve the defect. It reads the
kernel's actual family and constructor types, constructs their case schema,
and checks the actual generated selectors with the Lean kernel. There are no
admitted proofs and no hand-written replacement for the generated motive.
-/

namespace DependentSingletonObstruction

inductive I (f : Nat → Nat)
    (P : (k : Nat) → Fin (f k) → Prop) :
    (n : Nat) → (m : Nat) → Fin n → Prop where
  | mk (k : Nat) (v : Fin (f k)) (h : P k v) :
      I f P (f k) k v

-- Extraction is possible at an aligned occurrence. This establishes neither
-- global selector typing nor availability of Eq/HEq in the abstract bootstrap.
example (f : Nat → Nat) (P : (k : Nat) → Fin (f k) → Prop)
    (m : Nat) (v : Fin (f m)) (p : I f P (f m) m v) : P m v :=
  I.rec (motive := fun _ k w _ => ∀ e : k = m, HEq w v → P m v)
    (fun k w h e he => by cases e; cases he; exact h) p rfl HEq.rfl

open Lean Lean.Meta Lean.Elab.Command Lean4Lean
open Lean4Lean.InductiveSignature Lean4Lean.InductiveSignature.CaseSchema

private def readLevel : Level → Except String VLevel
  | .zero => return .zero
  | .succ u => return .succ (← readLevel u)
  | .max u v => return .max (← readLevel u) (← readLevel v)
  | .imax u v => return .imax (← readLevel u) (← readLevel v)
  | _ => .error "unexpected nonground source universe"

private def readExpr : Expr → Except String VExpr
  | .bvar i => return .bvar i
  | .sort u => return .sort (← readLevel u)
  | .const n us => return .const n (← us.mapM readLevel)
  | .app f a => return .app (← readExpr f) (← readExpr a)
  | .lam _ a b _ => return .lam (← readExpr a) (← readExpr b)
  | .forallE _ a b _ => return .forallE (← readExpr a) (← readExpr b)
  | .mdata _ e => readExpr e
  | _ => .error "unexpected source expression"

private def writeLevel : VLevel → Except String Level
  | .zero => return .zero
  | .succ u => return .succ (← writeLevel u)
  | .max u v => return .max (← writeLevel u) (← writeLevel v)
  | .imax u v => return .imax (← writeLevel u) (← writeLevel v)
  | .param _ => .error "unexpected generated universe parameter"

-- For this nonrecursive one-family schema, the case type is checked against
-- I.rec below before this interpretation of the abstract head is used.
private def writeExpr : VExpr → Except String Expr
  | .bvar i => return .bvar i
  | .sort u => return .sort (← writeLevel u)
  | .const n us => return .const n (← us.mapM writeLevel)
  | .elim n i us =>
    if n == ``I && i == 0 then return .const ``I.rec (← us.mapM writeLevel)
    else .error "unexpected abstract eliminator"
  | .app f a => return .app (← writeExpr f) (← writeExpr a)
  | .lam a b => return .lam `x (← writeExpr a) (← writeExpr b) .default
  | .forallE a b => return .forallE `x (← writeExpr a) (← writeExpr b) .default
  | .proj .. => .error "unexpected primitive projection"

private def unpack : VExpr → List VExpr × VExpr
  | .forallE a b => let (as, r) := unpack b; (a :: as, r)
  | e => ([], e)

private def appArgs : VExpr → List VExpr
  | .app f a => appArgs f ++ [a]
  | _ => []

private def requireSome (label : String) : Option α → MetaM α
  | some x => return x
  | none => throwError "{label}: generation unexpectedly failed"

private def requireOk : Except String α → MetaM α
  | .ok x => return x
  | .error e => throwError e

private def requireKernelError (label : String) (e : Expr) : MetaM Unit := do
  match Kernel.check (← getEnv) {} e with
  | .ok _ => throwError "{label}: obstruction no longer reproduced; review this file"
  | .error ex => logInfo m!"{label}: kernel rejected actual generated output\n{ex.toMessageData (← getOptions)}"

run_elab do
  let family ← getConstInfo ``I
  let ctor ← getConstInfo ``I.mk
  let (familyDomains, .sort resultLevel) := unpack (← requireOk (readExpr family.type))
    | throwError "unexpected family result"
  let (ctorDomains, ctorResult) := unpack (← requireOk (readExpr ctor.type))
  unless familyDomains.length == 5 && ctorDomains.length == 5 do
    throwError "unexpected source telescope lengths"
  let sig : InductiveSignature := {
    uvars := 0
    params := familyDomains.take 2
    families := #[{name := ``I, indices := familyDomains.drop 2, resultLevel}]
    constructors := #[{
      name := ``I.mk
      owner := ⟨0, by simp⟩
      fields := (ctorDomains.drop 2).map Field.external
      indices := (appArgs ctorResult).drop 2 }] }
  let schema : CaseSchema := { originalFamilies := [``I], signature := sig, restoration := {} }
  let owner : Fin schema.signature.families.size := ⟨0, by simp [schema, sig]⟩
  let generatedCtor ← requireOk (writeExpr
    (sig.constructorType (getElem sig.constructors 0 (by simp [sig]))))
  checkWithKernel generatedCtor
  unless ← isDefEq generatedCtor ctor.type do throwError "source constructor round trip failed"
  for target in [VLevel.zero, VLevel.succ .zero] do
    let generatedCase ← requireSome "case type" (schema.type owner 0 [] target)
    let generatedCase ← requireOk (writeExpr generatedCase)
    checkWithKernel generatedCase
    let nativeCase ← inferType (.const ``I.rec [← requireOk (writeLevel target)])
    unless ← isDefEq generatedCase nativeCase do throwError "case/native recursor types differ"
  logInfo "Source constructor round trip and generated case/native recursor type agreement checked."

  let data ← requireSome "projection data" (schema.projectionData owner [])
  let fields ← requireSome "reconstruction prefix"
    (data.reconstructionPrefix ``I 0 [] data.fields [.zero, .zero, .zero] [])
  unless fields.length == 3 && data.fieldIndex 0 == some 1 &&
      data.fieldIndex 1 == some 2 && data.fieldIndex 2 == none do
    throwError "unexpected reconstructed field selection"
  let [fieldK, fieldV, fieldH] := fields | throwError "unexpected prefix length"
  -- The two actual data selector values are naturally typable.
  checkWithKernel (← requireOk (writeExpr fieldK.value))
  checkWithKernel (← requireOk (writeExpr fieldV.value))
  logInfo "Both actual index selector values are kernel-typable."

  -- This exact field target is inserted under fresh indices by proofSelector.
  -- It contains no abstract eliminator, so its rejection does not depend on
  -- interpreting .elim as the native recursor.
  let motive := VExpr.wrapLams (data.params ++ data.indices ++ [data.major])
    (data.fieldTarget data.fields[2]! (fields.take 2))
  requireKernelError "Proof motive" (← requireOk (writeExpr motive))
  requireKernelError "Full proof selector" (← requireOk (writeExpr fieldH.value))

  -- Design probe: the existing general case-projection generator produces
  -- well-typed terms if it projects the earlier data fields by LARGE singleton
  -- elimination, instead of reading them from the index spine. This does not
  -- establish abstract permission (currently more restrictive), occurrence
  -- alignment, reduction compatibility, or a general reconstruction theorem.
  let projected ← requireSome "full case projection prefix"
    (data.prefix ``I 0 [] data.fields [.succ .zero, .succ .zero, .zero] [])
  unless projected.length == 3 do throwError "unexpected full projection prefix length"
  for field in projected do
    let value ← requireOk (writeExpr field.value)
    let type ← requireOk (writeExpr field.type)
    checkWithKernel value
    checkWithKernel type
    unless ← isDefEq (← inferType value) type do
      throwError "case projection has a different type than the generator declares"
  logInfo "All three general case projections have their exact generated types in Lean."

end DependentSingletonObstruction
