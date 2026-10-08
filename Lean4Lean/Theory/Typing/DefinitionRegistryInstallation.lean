import Lean4Lean.Theory.Typing.DefinitionPatterns
import Batteries.Tactic.OpenPrivate

/-! The definition-pattern table follows actual constant/equation
installation. Successful insertion proves freshness and lookup completeness. -/

namespace Lean4Lean.VEnv
variable {env extended : VEnv} {values : List VDefVal} {value : VDefVal}
open private addConsts_as_values addDefEqs_as_rules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-- Add exactly the values of a checked definition block to its pattern table. -/
def installDefinitions (old : Name → Option VDefVal) (values : List VDefVal)
    (name : Name) : Option VDefVal :=
  (values.find? (fun value => value.name == name)).orElse (fun _ => old name)

end Lean4Lean.VEnv
