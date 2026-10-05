import Lean4Lean.Theory.Typing.DefinitionHistory
import Lean4Lean.Theory.Typing.Strong

/-! Original transparent-definition stages, recovered from actual declaration
history. Mutual bodies are typed after all headers and before any equation;
the recorded ordinal is the original declaration position. -/
namespace Lean4Lean.VEnv
open VExpr
open private declaration_le from Lean4Lean.Theory.Typing.DefinitionHistory
open private addConsts_as_values addDefEqs_as_rules from Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-- A concrete original definition constructor, including its complete mutual
block. This is raw declaration evidence, not a semantic recursion callback. -/
inductive DefinitionTypingStage (base : VEnv) : VDecl → VEnv → VDefVal → Type where
  | single {header : VEnv} {value : VDefVal}
      (body : value.WF base)
      (headers : base.addConst value.name value.toVConstant = some header) :
      DefinitionTypingStage base (.def value) (header.addDefEq value.toDefEq) value
  | mutualBlock {header : VEnv} {values : List VDefVal} {value : VDefVal}
      (types : ∀ entry ∈ values, entry.toVConstant.WF base)
      (headers : base.addConsts values = some header)
      (bodies : ∀ entry ∈ values, entry.WF header)
      (member : value ∈ values) :
      DefinitionTypingStage base (.mutualDef values) (header.addDefEqs values) value

namespace DefinitionTypingStage
variable {base installed : VEnv} {declaration : VDecl} {value : VDefVal}

def header (stage : DefinitionTypingStage base declaration installed value) : VEnv :=
  match stage with
  | @single _ header _ _ _ => header
  | @mutualBlock _ header _ _ _ _ _ _ => header

def values (stage : DefinitionTypingStage base declaration installed value) : List VDefVal :=
  match stage with
  | single .. => [value]
  | @mutualBlock _ _ values _ _ _ _ _ => values

theorem declarationWF (stage : DefinitionTypingStage base declaration installed value) :
    VDecl.WF base declaration installed := by
  cases stage with
  | single body headers => exact .def body headers
  | mutualBlock types headers bodies _ => exact .mutualDef types headers bodies

theorem entries (stage : DefinitionTypingStage base declaration installed value) :
    stage.values = declaration.definitionEntries := by cases stage <;> rfl

theorem member (stage : DefinitionTypingStage base declaration installed value) :
    value ∈ stage.values := by
  cases stage with
  | single => exact List.mem_singleton_self _
  | mutualBlock _ _ _ member => exact member

theorem headers (stage : DefinitionTypingStage base declaration installed value) :
    base.addConsts stage.values = some stage.header := by
  cases stage with
  | single _ headers => simpa [values, header, VEnv.addConsts] using headers
  | mutualBlock _ headers _ _ => exact headers

theorem installed_eq (stage : DefinitionTypingStage base declaration installed value) :
    installed = stage.header.addDefEqs stage.values := by
  cases stage <;> rfl

theorem header_le (stage : DefinitionTypingStage base declaration installed value) :
    stage.header ≤ installed := by
  simpa only [stage.installed_eq, addDefEqs_as_rules] using
    (VEnv.addDefEqRules_le (env := stage.header) (dfs := stage.values.map VDefVal.toDefEq))


theorem headerWF (stage : DefinitionTypingStage base declaration installed value)
    (formed : base.WF) : stage.header.WF := by
  cases stage with
  | single body headers =>
    obtain ⟨declarations, history⟩ := formed
    exact ⟨.axiom value.toVConstVal :: declarations,
      .decl (.axiom (body.isType (VEnv.WF.ordered ⟨_, history⟩) trivial) headers) history⟩
  | mutualBlock types headers _ _ =>
    apply formed.addConstVals (fun entry member => ?_) (addConsts_as_values ▸ headers)
    obtain ⟨entry, inValues, rfl⟩ := List.mem_map.mp member
    exact types entry inValues

/-- The singleton body was checked in the old base. Its raw weakening here
only normalizes the header interface; mutual bodies are retained literally. -/
theorem body (stage : DefinitionTypingStage base declaration installed value) :
    value.WF stage.header := by
  cases stage with
  | single body headers => exact body.mono (VEnv.addConst_le headers)
  | mutualBlock _ _ bodies member => exact bodies _ member

theorem type (stage : DefinitionTypingStage base declaration installed value)
    (formed : base.WF) : value.toVConstant.WF base := by
  cases stage with
  | single body _ => exact body.isType formed.ordered trivial
  | mutualBlock types _ _ member => exact types _ member

theorem ofDeclaration (original : VDecl.WF base declaration installed)
    (member : value ∈ declaration.definitionEntries) :
    Nonempty (DefinitionTypingStage base declaration installed value) := by
  cases original with
  | «def» body headers =>
    have same := List.mem_singleton.mp member
    subst value
    exact ⟨.single body headers⟩
  | mutualDef types headers bodies => exact ⟨.mutualBlock types headers bodies member⟩
  | «axiom» | «opaque» | «example» | quot | induct => cases member

end DefinitionTypingStage

structure DefinitionDeclarationOrigin (env : VEnv) (declarations : List VDecl)
    (value : VDefVal) where
  base : VEnv
  installed : VEnv
  earlierDeclarations : List VDecl
  history : base.WF' earlierDeclarations
  declaration : VDecl
  stage : DefinitionTypingStage base declaration installed value
  laterDeclarations : List VDecl
  declarations_eq : declarations = laterDeclarations ++ declaration :: earlierDeclarations
  installedBelow : installed ≤ env

namespace DefinitionDeclarationOrigin
variable {env extended : VEnv} {declarations : List VDecl} {value : VDefVal} {declaration : VDecl}

def later (origin : DefinitionDeclarationOrigin env declarations value)
    (original : VDecl.WF env declaration extended) :
    DefinitionDeclarationOrigin extended (declaration :: declarations) value where
  base := origin.base
  installed := origin.installed
  earlierDeclarations := origin.earlierDeclarations
  history := origin.history
  declaration := origin.declaration
  stage := origin.stage
  laterDeclarations := declaration :: origin.laterDeclarations
  declarations_eq := by simpa only [List.cons_append] using congrArg (List.cons declaration) origin.declarations_eq
  installedBelow := origin.installedBelow.trans (declaration_le original)

def metadata (origin : DefinitionDeclarationOrigin env declarations value)
    (extension : env ≤ extended) : DefinitionDeclarationOrigin extended declarations value :=
  { origin with installedBelow := origin.installedBelow.trans extension }

theorem ordinal_lt (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.earlierDeclarations.length < declarations.length := by
  have lengths := congrArg List.length origin.declarations_eq
  simp only [List.length_append, List.length_cons] at lengths
  omega

def current (origin : DefinitionDeclarationOrigin env declarations value) (name : Name) : Bool :=
  origin.stage.values.any (fun entry => entry.name == name)

theorem current_self (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.current value.name = true :=
  List.any_eq_true.mpr ⟨value, origin.stage.member, by simp⟩

theorem header_le (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.stage.header ≤ env := origin.stage.header_le.trans origin.installedBelow

theorem headerWF (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.stage.header.WF := origin.stage.headerWF ⟨_, origin.history⟩

/-- The RHS theorem's source environment is the recorded pre-equation header,
not the completed environment in which the table was queried. -/
theorem bodyStrong (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.stage.header.IsDefEqStrong value.uvars [] value.value value.value value.type :=
  origin.stage.body.strong origin.headerWF.ordered trivial

/-- Declared type formation genuinely precedes the whole mutual header. -/
theorem typeStrong (origin : DefinitionDeclarationOrigin env declarations value) :
    ∃ level, origin.base.IsDefEqStrong value.uvars [] value.type value.type (.sort level) := by
  obtain ⟨level, formed⟩ := origin.stage.type ⟨_, origin.history⟩
  exact ⟨level, formed.strong (VEnv.WF.ordered ⟨_, origin.history⟩) trivial⟩

/-- The header contains precisely the OLD equations. -/
theorem header_defeqs (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.stage.header.defeqs = origin.base.defeqs :=
  VEnv.addConstVals_defeqs (addConsts_as_values ▸ origin.stage.headers)

theorem current_old (origin : DefinitionDeclarationOrigin env declarations value)
    (lookup : origin.base.constants name = some constant) : origin.current name = false := by
  cases selected : origin.current name with
  | false => rfl
  | true =>
    obtain ⟨entry, member, same⟩ := List.any_eq_true.mp selected
    have fresh := VEnv.addConstVals_names_fresh (addConsts_as_values ▸ origin.stage.headers)
      entry.toVConstVal (List.mem_map.mpr ⟨entry, member, rfl⟩)
    have nameEq : entry.name = name := by simpa only [beq_iff_eq] using same
    change origin.base.constants entry.name = none at fresh
    rw [nameEq, lookup] at fresh
    cases fresh

theorem registered (origin : DefinitionDeclarationOrigin env declarations value) :
    DefinitionRegistered env value := by
  have installed := DefinitionRegistered.of_addConsts origin.stage.headers origin.stage.member
  have normalized : DefinitionRegistered origin.installed value := by
    simpa only [← origin.stage.installed_eq] using installed
  exact normalized.mono origin.installedBelow

theorem closed (origin : DefinitionDeclarationOrigin env declarations value) :
    value.value.Closed ∧ value.type.Closed := by
  obtain ⟨level, type⟩ := origin.typeStrong
  exact ⟨origin.stage.body.closedN origin.headerWF.ordered trivial,
    type.defeq.closedN (VEnv.WF.ordered ⟨_, origin.history⟩) trivial⟩

theorem levelWF (origin : DefinitionDeclarationOrigin env declarations value) :
    value.value.LevelWF value.uvars ∧ value.type.LevelWF value.uvars :=
  ⟨(origin.stage.body.levelWF trivial).1, (origin.stage.body.levelWF trivial).2.2⟩

/-- Specialization preserves the actual original header. No completed-stage
Strong theorem or newly chosen declaration packet is used. -/
theorem bodyInstance (origin : DefinitionDeclarationOrigin env declarations value)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    origin.stage.header.IsDefEqStrong U [] (value.value.instL levels)
      (value.value.instL levels) (value.type.instL levels) :=
  origin.bodyStrong.instL levelsWF

theorem typeInstance (origin : DefinitionDeclarationOrigin env declarations value)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    ∃ level, origin.base.IsDefEqStrong U [] (value.type.instL levels)
      (value.type.instL levels) (.sort level) := by
  obtain ⟨level, type⟩ := origin.typeStrong
  exact ⟨level.inst levels, type.instL levelsWF⟩

theorem equivalentInstances (origin : DefinitionDeclarationOrigin env declarations value)
    (leftWF : ∀ level ∈ left, level.WF U)
    (rightWF : ∀ level ∈ right, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) left right) :
    EqUpToLevels U (value.value.instL left) (value.value.instL right) ∧
      EqUpToLevels U (value.type.instL left) (value.type.instL right) :=
  ⟨EqUpToLevels.instL_expr _ leftWF rightWF equivalent,
    EqUpToLevels.instL_expr _ leftWF rightWF equivalent⟩

end DefinitionDeclarationOrigin

/-- Registry lookup walks the actual finite declaration history. Metadata
installation preserves the exact packet and its original declaration ordinal. -/
theorem WF'.definitionOrigin {env : VEnv} {declarations : List VDecl}
    (history : env.WF' declarations)
    (lookup : definitionRegistry declarations name = some value) :
    Nonempty (DefinitionDeclarationOrigin env declarations value) := by
  induction history with
  | empty => cases lookup
  | @decl declaration installed declarations base original history ih =>
    change installDefinitions (definitionRegistry declarations) declaration.definitionEntries name = some value at lookup
    unfold installDefinitions at lookup
    cases found : declaration.definitionEntries.find? (fun entry => entry.name == name) with
    | none =>
      obtain ⟨origin⟩ := ih (by simpa only [found, Option.orElse_none] using lookup)
      exact ⟨origin.later original⟩
    | some selected =>
      simp only [found, Option.orElse_some, Option.some.injEq] at lookup
      subst selected
      obtain ⟨stage⟩ := DefinitionTypingStage.ofDeclaration original (List.mem_of_find?_eq_some found)
      exact ⟨⟨base, installed, declarations, history, declaration, stage, [], rfl, .rfl⟩⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨origin⟩ := ih lookup
    exact ⟨origin.metadata VEnv.addProjections_le⟩
  | inductEliminators _ _ _ _ _ _ _ _ ih =>
    obtain ⟨origin⟩ := ih lookup
    exact ⟨origin.metadata VEnv.addEliminator_le⟩

/-- A finite bank keeps one actual origin packet per declared definition.
Its order is the concrete newest-first declaration order, including every
member of each original mutual block. -/
structure DefinitionOriginBank (env : VEnv) (declarations : List VDecl) where
  entries : List (Σ value, DefinitionDeclarationOrigin env declarations value)
  values_eq : entries.map Sigma.fst = declarations.flatMap VDecl.definitionEntries

theorem WF'.definitionBank {env : VEnv} {declarations : List VDecl}
    (history : env.WF' declarations) : Nonempty (DefinitionOriginBank env declarations) := by
  have build : ∀ values : List VDefVal,
      (∀ value ∈ values, Nonempty (DefinitionDeclarationOrigin env declarations value)) →
      ∃ entries : List (Σ value, DefinitionDeclarationOrigin env declarations value),
        entries.map Sigma.fst = values := by
    intro values
    induction values with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons value rest ih =>
      intro origins
      obtain ⟨origin⟩ := origins value (List.mem_cons_self)
      obtain ⟨tail, same⟩ := ih (fun value member => origins value (List.mem_cons_of_mem _ member))
      exact ⟨⟨value, origin⟩ :: tail, congrArg (List.cons value) same⟩
  obtain ⟨entries, same⟩ := build (declarations.flatMap VDecl.definitionEntries) (by
    intro value member
    obtain ⟨declaration, listed, member⟩ := List.mem_flatMap.mp member
    exact history.definitionOrigin (history.definitionRegistry_complete listed member))
  exact ⟨⟨entries, same⟩⟩

namespace DefinitionOriginBank

theorem lookup (bank : DefinitionOriginBank env declarations)
    (history : env.WF' declarations)
    (selected : definitionRegistry declarations name = some value) :
    ∃ origin : DefinitionDeclarationOrigin env declarations value,
      (⟨value, origin⟩ : Σ value, DefinitionDeclarationOrigin env declarations value) ∈ bank.entries := by
  obtain ⟨origin⟩ := history.definitionOrigin selected
  have declared : origin.declaration ∈ declarations := by
    have member : origin.declaration ∈ origin.laterDeclarations ++
        origin.declaration :: origin.earlierDeclarations :=
      List.mem_append_right _ (List.mem_cons_self)
    simpa only [origin.declarations_eq] using member
  have member : value ∈ declarations.flatMap VDecl.definitionEntries :=
    List.mem_flatMap.mpr ⟨origin.declaration, declared,
      origin.stage.entries ▸ origin.stage.member⟩
  rw [← bank.values_eq] at member
  obtain ⟨⟨actual, packet⟩, inEntries, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨packet, inEntries⟩

end DefinitionOriginBank

end Lean4Lean.VEnv
