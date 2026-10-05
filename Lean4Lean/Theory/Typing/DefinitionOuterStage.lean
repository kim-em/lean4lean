import Lean4Lean.Theory.Typing.DefinitionEquationMeasure
import Lean4Lean.Theory.Typing.CanonicalHeadRegistryData

/-! An outer declaration stage counts both installed names and installed
equations. A retained delta origin either moves to an earlier outer stage or
spends fuel for a registered equation absent from the actual source. -/
namespace Lean4Lean.VEnv
set_option Elab.async false
variable {env source extended : VEnv}

noncomputable def Ordered.definitionStage (ordered : env.Ordered) : Nat × Nat :=
  (ordered.constantCount, ordered.equationCount)

theorem Ordered.definitionStage_components_le
    (left : source.Ordered) (right : env.Ordered) (below : source ≤ env) :
    left.definitionStage.1 ≤ right.definitionStage.1 ∧
      left.definitionStage.2 ≤ right.definitionStage.2 :=
  ⟨(Classical.choice left.constantDomain).length_le (Classical.choice right.constantDomain) below,
    left.equationCount_le right below⟩

theorem Ordered.definitionStage_eq (left right : env.Ordered) :
    left.definitionStage = right.definitionStage := by
  apply Prod.ext
  · exact (Classical.choice left.constantDomain).length_eq (Classical.choice right.constantDomain)
  · exact left.equationCount_eq right

/-- A fresh constant already decreases the first coordinate, independently
of how many equations were present at its original formation stage. -/
theorem ConstantHeaderOrigin.definitionStage_lt
    (origin : ConstantHeaderOrigin env name value) (ordered : env.Ordered) :
    Prod.Lex Nat.lt Nat.lt origin.ordered.definitionStage ordered.definitionStage :=
  Prod.Lex.left _ _ (origin.count_lt ordered)

/-- Keeping all constants while removing one actual installed equation also
decreases the outer stage. No choice of declaration origin is canonicalized. -/
theorem DefinitionDeclarationOrigin.header_definitionStage_lt
    (origin : DefinitionDeclarationOrigin env declarations value)
    (sourceOrdered : source.Ordered) (headerBelow : origin.stage.header ≤ source)
    (present : source.defeqs value.toDefEq) :
    Prod.Lex Nat.lt Nat.lt origin.headerWF.ordered.definitionStage sourceOrdered.definitionStage := by
  have constants := (origin.headerWF.ordered.definitionStage_components_le sourceOrdered headerBelow).1
  change origin.headerWF.ordered.constantCount ≤ sourceOrdered.constantCount at constants
  by_cases smaller : origin.headerWF.ordered.constantCount < sourceOrdered.constantCount
  · exact Prod.Lex.left _ _ smaller
  · have same : origin.headerWF.ordered.constantCount = sourceOrdered.constantCount := by omega
    change Prod.Lex Nat.lt Nat.lt
      (origin.headerWF.ordered.constantCount, origin.headerWF.ordered.equationCount)
      (sourceOrdered.constantCount, sourceOrdered.equationCount)
    rw [same]
    exact Prod.Lex.right _ (origin.header_equationCount_lt sourceOrdered headerBelow present)

/-- The active control selects registered definition heads whose defining
equation has not been installed in this actual source environment. -/
noncomputable def activeMissing (source : VEnv) (registry : CanonicalHead.Registry) (name : Name) : Bool := by
  classical
  exact match registry.definitions name with
    | none => false
    | some value => decide (¬ source.defeqs value.toDefEq)

theorem activeMissing_of_missing
    (lookup : registry.definitions name = some value) (missing : ¬ source.defeqs value.toDefEq) :
    activeMissing source registry name = true := by
  classical
  simp only [activeMissing, lookup, decide_eq_true_eq]
  exact missing

/-- An installed defining equation is always quiet under the source's
active control, regardless of which origin a query retains for it. -/
theorem activeMissing_of_installed
    (lookup : registry.definitions name = some value) (present : source.defeqs value.toDefEq) :
    activeMissing source registry name = false := by
  classical
  simp [activeMissing, lookup, present]

theorem activeMissing_eq_true_iff :
    activeMissing source registry name = true ↔
      ∃ value, registry.definitions name = some value ∧ ¬ source.defeqs value.toDefEq := by
  classical
  cases lookup : registry.definitions name with
  | none => simp [activeMissing, lookup]
  | some value => simp [activeMissing, lookup]

theorem activeMissing_ne_installed
    (active : activeMissing source registry name = true)
    (lookup : registry.definitions name = some value) : ¬ source.defeqs value.toDefEq := by
  intro present
  have quiet := activeMissing_of_installed lookup present
  rw [active] at quiet
  cases quiet

/-- The two branches apply to the actual source environment and the exact
retained origin. In the missing-equation branch the delta constructor's
named depth increases by one under this very active control. -/
theorem DefinitionDeclarationOrigin.delta_stage_or_active
    (origin : DefinitionDeclarationOrigin env declarations value)
    (sourceOrdered : source.Ordered) (headerBelow : origin.stage.header ≤ source)
    (lookup : registry.definitions name = some value) :
    (source.defeqs value.toDefEq ∧
      Prod.Lex Nat.lt Nat.lt origin.headerWF.ordered.definitionStage sourceOrdered.definitionStage) ∨
    (¬ source.defeqs value.toDefEq ∧ activeMissing source registry name = true) := by
  classical
  by_cases installed : source.defeqs value.toDefEq
  · exact .inl ⟨installed, origin.header_definitionStage_lt sourceOrdered headerBelow installed⟩
  · exact .inr ⟨installed, activeMissing_of_missing lookup installed⟩

end Lean4Lean.VEnv
