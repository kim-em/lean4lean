import Lean4Lean.Theory.Typing.CanonicalHeadTrace
import Lean4Lean.Theory.Typing.NativeIotaPatterns
import Lean4Lean.Theory.Quot

/-! Deterministic ordinary iota and primitive projection dispatch.

The additional rules come from the actual native equations, generated case
equations, and primitive quotient equation. The machine preserves the existing
beta/delta/singleton step whenever it succeeds. Otherwise it enters function
positions, registered major positions, and primitive projection majors.

Only syntax is decided here. An origin identifies the actual equation and its
captured arguments; typing, parameter/index alignment and elimination guards
must be proved from the original declaration observations by its consumer.
-/

namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature
set_option backward.isDefEq.respectTransparency false

structure Rule where
  constructor : Name
  constructorArity : Nat
  prefixCount : Nat
  fieldCount : Nat
  equation : VDefEq

def Rule.native (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) : Rule :=
  { constructor := data.ruleConstructor index
    constructorArity := (NativeRecursorData.ruleMajorArguments equation).length
    prefixCount := data.indexOffset
    fieldCount := data.schema.signature.constructors[index].fields.length
    equation := equation }

def nativeRules (data : NativeRecursorData) : List Rule :=
  data.constructorIndices.filterMap fun index =>
    (data.equation index).map (Rule.native data index)

def Rule.caseRule (rule : CaseSchema.AppliedRule) : Rule :=
  { constructor := rule.application.ctorName
    constructorArity := rule.application.ctorArguments.length
    prefixCount := rule.numPrefix
    fieldCount := rule.numFields
    equation := rule.equation }

def quotientRule : Rule :=
  { constructor := ``Quot.mk, constructorArity := 3, prefixCount := 5,
    fieldCount := 1, equation := quotDefEq }

def CaseEntry.majorOffset (entry : CaseEntry) : Nat :=
  entry.schema.signature.params.length + 1 + (entry.schema.view entry.owner).constructors.size +
    entry.schema.signature.families[entry.owner].indices.length

def CaseEntry.rules (entry : CaseEntry) (block : Name) : List Rule :=
  ((entry.schema.appliedRules block entry.owner).getD []).map Rule.caseRule

structure Selected where
  levels : List VLevel
  arguments : List VExpr
  majorOffset : Nat
  rules : List Rule

/-- A selected family retains a major position even when it has no rules. -/
def select (registry : Registry) (function : VExpr) : Option Selected :=
  match function.getAppFnArgs with
  | (.const name levels, arguments) =>
    match registry.natives name with
    | some data =>
      if data.name = name then some ⟨levels, arguments, data.majorOffset, nativeRules data⟩
      else none
    | none =>
      if registry.quotient && name == ``Quot.lift then
        some ⟨levels, arguments, 5, [quotientRule]⟩
      else none
  | (.elim block owner levels, arguments) =>
    match registry.cases block owner with
    | some entry =>
      if entry.owner.val = owner then
        some ⟨levels, arguments, entry.majorOffset, entry.rules block⟩
      else none
    | none => none
  | _ => none

def Selected.isMajor (selected : Selected) : Bool :=
  selected.arguments.length == selected.majorOffset

def Rule.captures (rule : Rule) (prefixArguments constructorArguments : List VExpr) : List VExpr :=
  prefixArguments.take rule.prefixCount ++
    constructorArguments.drop (constructorArguments.length - rule.fieldCount)

/-- The closed original RHS is applied to its actual finite captures. Keeping
its telescope explicit avoids inventing scopes for a stripped open body. -/
def Rule.run (rule : Rule) (selected : Selected) (major : VExpr) : Option VExpr :=
  match major.getAppFnArgs with
  | (.const name _, constructorArguments) =>
    if name = rule.constructor ∧ constructorArguments.length = rule.constructorArity ∧
        selected.levels.length = rule.equation.uvars ∧
        rule.prefixCount ≤ selected.arguments.length ∧ rule.fieldCount ≤ constructorArguments.length then
      some (mkApps (rule.equation.rhs.instL selected.levels)
        (rule.captures selected.arguments constructorArguments))
    else none
  | _ => none

def directIota (selected : Selected) (major : VExpr) : Option VExpr :=
  selected.rules.findSome? (fun rule => rule.run selected major)

/-- Structure eta permits the unique branch to inspect primitive projections
of a neutral major. The reverse constructor index is checked against the
ordinary projection registry; indexed families are excluded explicitly.
Specialized recursors must retain the actual restored constructor arity. -/
def etaIota (registry : Registry) (selected : Selected) (major : VExpr) : Option VExpr := do
  let [rule] := selected.rules | none
  let entry ← registry.structureConstructors rule.constructor
  let info ← registry.projections entry.typeName
  if info.ctorName = rule.constructor ∧ info.nindices = 0 ∧
      rule.constructorArity = info.nparams + info.numFields ∧
      rule.fieldCount = info.numFields ∧ selected.levels.length = rule.equation.uvars ∧
      rule.prefixCount ≤ selected.arguments.length then
    some (mkApps (rule.equation.rhs.instL selected.levels)
      (selected.arguments.take rule.prefixCount ++
        (List.range info.numFields).map (fun index => .proj entry.typeName index major)))
  else none

def project (registry : Registry) (typeName : Name) (index : Nat) (major : VExpr) : Option VExpr := do
  let info ← registry.projections typeName
  match major.getAppFnArgs with
  | (.const name _, arguments) =>
    if name = info.ctorName then arguments[info.nparams + index]? else none
  | _ => none

def appFunction (out : CanonicalHead.Output) (argument : VExpr) : CanonicalHead.Output :=
  ⟨out.added, .app out.result (argument.lift' (.skipN .refl out.added.length))⟩

def appMajor (function : VExpr) (out : CanonicalHead.Output) : CanonicalHead.Output :=
  ⟨out.added, .app (function.lift' (.skipN .refl out.added.length)) out.result⟩

def projMajor (typeName : Name) (index : Nat) (out : CanonicalHead.Output) : CanonicalHead.Output :=
  ⟨out.added, .proj typeName index out.result⟩

/-- Structure dispatch always uses projections, even for constructor majors.
At a registered major position dispatch precedes function descent; other
applications descend only into their function.
Recursion follows proper source subexpressions. In particular a failed
outer head check never recurses on a freshly rewritten expression. -/
def step (registry : Registry) (expression : VExpr) : Option CanonicalHead.Output :=
  match CanonicalHead.step registry.toRegistry expression with
  | some out => some out
  | none =>
    match expression with
    | .app function argument =>
      match select registry function with
      | some selected =>
        if selected.isMajor then
          match etaIota registry selected argument with
          | some result => some ⟨[], result⟩
          | none =>
            match directIota selected argument with
            | some result => some ⟨[], result⟩
            | none => (step registry argument).map (appMajor function)
        else (step registry function).map (fun out => appFunction out argument)
      | none => (step registry function).map (fun out => appFunction out argument)
    | .proj typeName index major =>
      match project registry typeName index major with
      | some result => some ⟨[], result⟩
      | none => (step registry major).map (projMajor typeName index)
    | _ => none
termination_by expression

inductive RuleOrigin (registry : Registry) : Selected → Rule → Prop where
  | native (lookup : registry.natives name = some data) (named : data.name = name)
      (index : Fin data.schema.signature.constructors.size)
      (owned : data.schema.signature.constructors[index].owner = data.owner)
      (generated : data.equation index = some equation) :
      RuleOrigin registry ⟨levels, arguments, data.majorOffset, nativeRules data⟩
        (Rule.native data index equation)
  | caseRule (lookup : registry.cases block owner = some entry) (owned : entry.owner.val = owner)
      (generated : entry.schema.Generates block entry.owner rule) :
      RuleOrigin registry ⟨levels, arguments, entry.majorOffset, entry.rules block⟩ (Rule.caseRule rule)
  | quotient (lookup : registry.natives ``Quot.lift = none) (installed : registry.quotient = true) :
      RuleOrigin registry ⟨levels, arguments, 5, [quotientRule]⟩ quotientRule

/-- Every chosen rule has declaration provenance, including the actual
constructor owner. No free-standing RHS can enter the generated rule list. -/
theorem select_origin (chosen : select registry function = some selected)
    (member : rule ∈ selected.rules) : RuleOrigin registry selected rule := by
  unfold select at chosen
  split at chosen <;> try contradiction
  · rename_i name levels arguments spine
    split at chosen
    · rename_i data lookup
      split at chosen <;> try contradiction
      rename_i named
      cases chosen
      obtain ⟨index, owned, generated⟩ := List.mem_filterMap.mp member
      simp only [Option.map_eq_some_iff] at generated
      obtain ⟨equation, equationSelected, rfl⟩ := generated
      exact .native lookup named index (NativeRecursorData.mem_constructorIndices.mp owned) equationSelected
    · rename_i lookup
      split at chosen <;> try contradiction
      rename_i installed
      simp only [Bool.and_eq_true, beq_iff_eq] at installed
      obtain ⟨installed, rfl⟩ := installed
      cases chosen
      cases List.mem_singleton.mp member
      exact .quotient lookup installed
  · rename_i block owner levels arguments spine
    split at chosen <;> try contradiction
    rename_i entry lookup
    split at chosen <;> try contradiction
    rename_i owned
    cases chosen
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    cases generated : entry.schema.appliedRules block entry.owner with
    | none => simp [generated] at present
    | some rules =>
      simp only [generated, Option.getD_some] at present
      exact .caseRule lookup owned (CaseSchema.generates_of_appliedRules generated present)

theorem directIota_origin (selected : select registry function = some chosen)
    (reduced : directIota chosen major = some result) :
    ∃ rule, RuleOrigin registry chosen rule ∧ rule.run chosen major = some result := by
  obtain ⟨rule, member, reduced⟩ := List.exists_of_findSome?_eq_some reduced
  exact ⟨rule, select_origin selected member, reduced⟩

/-- Eta dispatch retains the same generated equation and the actual
projection metadata. Its typed consumer must produce the projection fields
from the original constructor telescope, just as ordinary iota does. -/
theorem etaIota_origin (selected : select registry function = some chosen)
    (reduced : etaIota registry chosen major = some result) :
    ∃ rule entry info, chosen.rules = [rule] ∧ RuleOrigin registry chosen rule ∧
      registry.structureConstructors rule.constructor = some entry ∧
      registry.projections entry.typeName = some info ∧
      info.ctorName = rule.constructor ∧ info.nindices = 0 ∧
      rule.constructorArity = info.nparams + info.numFields ∧ rule.fieldCount = info.numFields ∧
      chosen.levels.length = rule.equation.uvars ∧ rule.prefixCount ≤ chosen.arguments.length ∧
      result = mkApps (rule.equation.rhs.instL chosen.levels)
        (chosen.arguments.take rule.prefixCount ++
          (List.range info.numFields).map (fun index => .proj entry.typeName index major)) := by
  cases rules : chosen.rules with
  | nil => simp [etaIota, rules] at reduced
  | cons rule rest =>
    cases rest with
    | cons next rest => simp [etaIota, rules] at reduced
    | nil =>
      simp only [etaIota, rules, bind, Option.bind_eq_some_iff] at reduced
      obtain ⟨entry, reverse, info, lookup, reduced⟩ := reduced
      split at reduced <;> try contradiction
      rename_i checks
      cases reduced
      exact ⟨rule, entry, info, rfl, select_origin selected (rules ▸ List.mem_singleton_self _),
        reverse, lookup, checks.1, checks.2.1, checks.2.2.1, checks.2.2.2.1,
        checks.2.2.2.2.1, checks.2.2.2.2.2, rfl⟩

inductive Origin (registry : Registry) : VExpr → CanonicalHead.Output → Prop where
  | legacy (selected : CanonicalHead.step registry.toRegistry expression = some out) :
      Origin registry expression out
  | function (child : Origin registry function out) :
      Origin registry (.app function argument) (appFunction out argument)
  | iota (selected : select registry function = some chosen) (major : chosen.isMajor = true)
      (origin : RuleOrigin registry chosen rule) (reduced : rule.run chosen argument = some result) :
      Origin registry (.app function argument) ⟨[], result⟩
  | major (selected : select registry function = some chosen) (major : chosen.isMajor = true)
      (child : Origin registry argument out) :
      Origin registry (.app function argument) (appMajor function out)
  | structureEta (selected : select registry function = some chosen) (major : chosen.isMajor = true)
      (reduced : etaIota registry chosen argument = some result) :
      Origin registry (.app function argument) ⟨[], result⟩
  | projection (lookup : registry.projections typeName = some info)
      (constructor : major.getAppFnArgs = (.const info.ctorName levels, arguments))
      (field : arguments[info.nparams + index]? = some result) :
      Origin registry (.proj typeName index major) ⟨[], result⟩
  | projectionMajor (child : Origin registry major out) :
      Origin registry (.proj typeName index major) (projMajor typeName index out)

/-- Recursive origins expose each actual major path as well as the final
generated rule or primitive projection field. -/
theorem step_origin (selected : step registry expression = some out) :
    Origin registry expression out := by
  induction expression generalizing out with
  | app function argument functionIH argumentIH =>
    rw [step] at selected
    split at selected
    · rename_i old success
      cases selected
      exact .legacy success
    · split at selected
      · rename_i chosen chosenEq
        split at selected
        · rename_i major
          split at selected
          · rename_i result reduced
            cases selected
            exact .structureEta chosenEq major reduced
          · split at selected
            · rename_i result reduced
              cases selected
              obtain ⟨rule, origin, reduced⟩ := directIota_origin chosenEq reduced
              exact .iota chosenEq major origin reduced
            · obtain ⟨child, success, equality⟩ := Option.map_eq_some_iff.mp selected
              cases equality
              exact .major chosenEq major (argumentIH success)
        · obtain ⟨child, success, equality⟩ := Option.map_eq_some_iff.mp selected
          cases equality
          exact .function (functionIH success)
      · obtain ⟨child, success, equality⟩ := Option.map_eq_some_iff.mp selected
        cases equality
        exact .function (functionIH success)
  | proj typeName index major majorIH =>
    rw [step] at selected
    split at selected
    · rename_i old success
      cases selected
      exact .legacy success
    · split at selected
      · rename_i result reduced
        cases selected
        unfold project at reduced
        simp only [bind, Option.bind_eq_some_iff] at reduced
        obtain ⟨info, lookup, reduced⟩ := reduced
        split at reduced <;> try contradiction
        rename_i name levels arguments constructor
        split at reduced <;> try contradiction
        rename_i same
        cases same
        exact .projection lookup constructor reduced
      · obtain ⟨child, success, equality⟩ := Option.map_eq_some_iff.mp selected
        cases equality
        exact .projectionMajor (majorIH success)
  | _ =>
    simp only [step] at selected
    split at selected
    · rename_i old success
      cases selected
      exact .legacy success
    · contradiction

end Lean4Lean.CanonicalDataHead
