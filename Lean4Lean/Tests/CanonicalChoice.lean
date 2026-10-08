import Lean4Lean.Environment
import Lean4Lean.Theory.Meta
import Lean4Lean.Verify.Inductive.ChoiceCanonicalForms

/-! Realizability of `VEnv.HasCanonicalChoice` for the real `Nonempty` and `Classical.choice`.

The declarations of `Nonempty` (with `Nonempty.intro`) and of the axiom `Classical.choice` are
rebuilt exactly as `Init.Prelude` submits them, read back from the environment, and added to
an empty environment through `Lean4Lean.addDecl`. The test checks that

* the real constants satisfy `IsProductionNonempty`, `IsProductionNonemptyIntro` and
  `IsProductionChoice`: their types are `nonemptyBootstrapType`,
  `nonemptyBootstrapIntroType` and `choiceBootstrapType`, they are safe, and they have one
  universe parameter. So `VEnvs.WFCore.hasCanonicalChoice` applies to every environment that
  contains them;
* the executable installs the three constants exactly as Lean's kernel does;
* their translations are the terms stored by `VEnv.HasCanonicalChoice`. -/

namespace Lean4Lean.Tests.CanonicalChoice

open Lean Meta

deriving instance BEq for VLevel
deriving instance BEq for VExpr

/-- The names of the leading `∀` binders. -/
def forallNames : Expr → List Name
  | .forallE n _ b _ => n :: forallNames b
  | _ => []

def check (cond : Bool) (msg : String) : MetaM Unit :=
  unless cond do throwError msg

def toV (ls : List Name) (e : Expr) : MetaM VExpr :=
  Lean4Lean.Meta.ofExpr ls {} e

run_meta do
  let env ← getEnv
  let some (.inductInfo I) := env.find? ``Nonempty | throwError "no Nonempty"
  let some (.ctorInfo C) := env.find? ``Nonempty.intro | throwError "no Nonempty.intro"
  let some (.axiomInfo A) := env.find? ``Classical.choice | throwError "no Classical.choice"
  -- The production forms.
  let [u] := I.levelParams | throwError "Nonempty: unexpected level parameters"
  check (!I.isUnsafe && I.numParams == 1 && I.numIndices == 0) "Nonempty: unexpected shape"
  let [alpha] := forallNames I.type | throwError "Nonempty: unexpected type"
  check (I.type.equal (nonemptyBootstrapType u alpha)) "Nonempty: type is not nonemptyBootstrapType"
  let [cu] := C.levelParams | throwError "Nonempty.intro: unexpected level parameters"
  check (!C.isUnsafe) "Nonempty.intro: unsafe"
  let [cAlpha, cVal] := forallNames C.type | throwError "Nonempty.intro: unexpected type"
  check (C.type.equal (nonemptyBootstrapIntroType cu cAlpha cVal))
    "Nonempty.intro: type is not nonemptyBootstrapIntroType"
  let [au] := A.levelParams | throwError "Classical.choice: unexpected level parameters"
  check (!A.isUnsafe) "Classical.choice: unsafe"
  let [aAlpha, aH] := forallNames A.type | throwError "Classical.choice: unexpected type"
  check (A.type.equal (choiceBootstrapType au aAlpha aH))
    "Classical.choice: type is not choiceBootstrapType"
  -- Translations are the stored terms of `HasCanonicalChoice`.
  check ((← toV [u] I.type) == canonicalNonemptyType) "Nonempty: translation differs"
  check ((← toV [cu] C.type) == canonicalNonemptyIntroType) "Nonempty.intro: translation differs"
  check ((← toV [au] A.type) == canonicalChoiceType) "Classical.choice: translation differs"
  -- The executable on the real declarations, from an empty environment.
  let intro : Constructor := { name := ``Nonempty.intro, type := C.type }
  let neType : InductiveType := { name := ``Nonempty, type := I.type, ctors := [intro] }
  let neDecl := Declaration.inductDecl I.levelParams I.numParams [neType] I.isUnsafe
  let choiceDecl := Declaration.axiomDecl
    { name := ``Classical.choice, levelParams := A.levelParams, type := A.type,
      isUnsafe := A.isUnsafe }
  let empty ← mkEmptyEnvironment
  let kenv ← match Lean4Lean.addDecl empty.toKernelEnv neDecl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected Nonempty: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  let kenv ← match Lean4Lean.addDecl kenv choiceDecl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected Classical.choice: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  for n in [``Nonempty, ``Nonempty.intro, ``Classical.choice] do
    let some ci := kenv.find? n | throwError "Lean4Lean did not install {n}"
    let some ci₀ := env.find? n | throwError "missing {n}"
    check (ci.levelParams == ci₀.levelParams && ci.type.equal ci₀.type &&
      ci.isUnsafe == ci₀.isUnsafe) s!"{n}: Lean4Lean and Lean's kernel disagree"

end Lean4Lean.Tests.CanonicalChoice
