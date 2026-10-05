import Lean4Lean.Theory.Typing.AnchoredDataExposureTransport
import Lean4Lean.Theory.Typing.AnchoredAdmission
import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.CanonicalDataHeadTrace

/-! The ordinary-data clause for a future constructor observation atom.

A demand at successor rank freezes a constructor tag and a finite list of
argument keys at the preceding rank. Its interpretation uses actual canonical
traces, generated inhabited proof insertions, and the already defined lower
rank admission relation. In particular, a constructor tag is retained even
when every argument input is empty.

This file leaves the existing atom and source grammars unchanged. It checks
composition of the proposed clause, including independently chosen private
proof contexts, without constructor injectivity or datatype-type injectivity.
The clause is for relevant ordinary data. Structure eta needs a destructor
clause, and observing proposition constructors with this clause is unsound.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- All recursive semantic queries of a constructor demand at rank `n + 1`
are made through the argument inputs at rank `n`. Parameters are included in
the argument list, permitting the declared dependent telescope to be reused. -/
structure ConstructorDemand (n : Nat) where
  name : Name
  levels : List VLevel
  arguments : List (Key n)

def ConstructorDemand.rename (demand : ConstructorDemand n) (ρ : Lift) :
    ConstructorDemand n :=
  { demand with arguments := demand.arguments.map (·.rename ρ) }

/-- Exact argument positions matter: a consumer may select any constructor
field, including a recursive field or a function-valued field. -/
inductive ConstructorArguments (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : List (Key n) → List VExpr → List VExpr → Prop where
  | nil : ConstructorArguments env U registry Γ [] [] []
  | cons : Admitted env U registry Γ key left right →
      ConstructorArguments env U registry Γ keys lefts rights →
      ConstructorArguments env U registry Γ (key :: keys) (left :: lefts) (right :: rights)

namespace ConstructorArguments

variable {n : Nat} {keys : List (Key n)} {key : Key n} {index : Nat}

theorem transport (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (arguments : ConstructorArguments env U registry Γ keys lefts rights) :
    ConstructorArguments env U registry Δ (keys.map (·.rename ρ))
      (lefts.map (·.lift' ρ)) (rights.map (·.lift' ρ)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (route.admitted henv head) ih

private theorem admittedTrans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : Admitted env U registry Γ key left middle)
    (second : Admitted env U registry Γ key middle right) :
    Admitted env U registry Γ key left right := by
  obtain ⟨anchor, pair, old, _, _, _, before, across⟩ := first
  obtain ⟨_, next, support, typed, formed, code, _, after⟩ := second
  have selfCode := code
  have before' := Related.retag henv typed selfCode before
  exact ⟨anchor, pair.trans next, support, typed, formed, code,
    before', Related.trans henv hscoped across after⟩

theorem trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : ConstructorArguments env U registry Γ keys lefts middles)
    (second : ConstructorArguments env U registry Γ keys middles rights) :
    ConstructorArguments env U registry Γ keys lefts rights := by
  induction first generalizing rights with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (admittedTrans henv hscoped head next) (ih rest)

/-- A selected iota field is available at the exact frozen lower-rank key;
selection does not invent a typing certificate for the field. -/
theorem getElem? (arguments : ConstructorArguments env U registry Γ keys lefts rights)
    (selected : keys[index]? = some key) :
    ∃ left right, lefts[index]? = some left ∧ rights[index]? = some right ∧
      Admitted env U registry Γ key left right := by
  induction arguments generalizing index with
  | nil => simp at selected
  | cons head tail ih =>
    cases index with
    | zero => cases Option.some.inj selected; exact ⟨_, _, rfl, rfl, head⟩
    | succ index => exact ih selected

end ConstructorArguments

/-- Candidate successor-rank term clause for ordinary relevant data. All
fields are interpreted at the preceding rank. Universe packets may differ
by the existing universe equivalence, while the constructor tag is exact. -/
structure ConstructorWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (left right type : VExpr) (demand : ConstructorDemand n) where
  context : List VExpr
  map : Lift
  relevant : ∃ level, env.HasType U context (type.lift' map) (.sort level) ∧ ¬level ≈ .zero
  leftLevels : List VLevel
  rightLevels : List VLevel
  leftArguments : List VExpr
  rightArguments : List VExpr
  leftExposure : ConstructorExposure env U registry Γ left type context map
    (mkApps (.const demand.name leftLevels) leftArguments)
  rightExposure : ConstructorExposure env U registry Γ right type context map
    (mkApps (.const demand.name rightLevels) rightArguments)
  leftTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name leftLevels) leftArguments) = none
  rightTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name rightLevels) rightArguments) = none
  leftUniverses : List.Forall₂ (· ≈ ·) demand.levels leftLevels
  rightUniverses : List.Forall₂ (· ≈ ·) demand.levels rightLevels
  arguments : ConstructorArguments env U registry.toRegistry context
    (demand.arguments.map (·.rename map)) leftArguments rightArguments

private theorem constructor_lift (name : Name) (levels : List VLevel)
    (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ head, (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

private theorem constructor_spine (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    (mkApps (.const name levels) arguments).getAppFnArgs = (.const name levels, arguments) := by
  have getSpine : ∀ (head : VExpr) arguments accumulated,
      getAppFnArgs.go (mkApps head arguments) accumulated =
        getAppFnArgs.go head (arguments ++ accumulated) := by
    intro head arguments
    induction arguments generalizing head with
    | nil => intro accumulated; rfl
    | cons arg rest ih =>
      intro accumulated
      exact ih (.app head arg) accumulated
  simp only [getAppFnArgs, getSpine, getAppFnArgs.go, List.append_nil]

private theorem constructor_arguments_inj
    (same : mkApps (.const name levels) left = mkApps (.const name' levels') right) :
    left = right := by
  have spine := congrArg VExpr.getAppFnArgs same
  simpa only [constructor_spine] using congrArg Prod.snd spine

/-- Two observations of the same major cannot select different iota
branches, even when their field demands, ranks and assigned types differ. -/
theorem ConstructorWitness.sameConstructor
    {firstDemand : ConstructorDemand n} {secondDemand : ConstructorDemand m}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : ConstructorWitness env U registry Γ major firstRight firstType firstDemand)
    (second : ConstructorWitness env U registry Γ major secondRight secondType secondDemand) :
    firstDemand.name = secondDemand.name := by
  obtain ⟨_, i, j, _, _, _, heads⟩ := first.leftExposure.sameHead henv hscoped
    second.leftExposure first.leftTerminal second.leftTerminal
  rw [constructor_lift, constructor_lift] at heads
  have spine := congrArg VExpr.getAppFnArgs heads
  have names : VExpr.const firstDemand.name first.leftLevels =
      VExpr.const secondDemand.name second.leftLevels := by
    simpa only [constructor_spine] using congrArg Prod.fst spine
  exact (VExpr.const.inj names).1

/-- The ordinary constructor clause composes in actual common proof worlds.
Middle argument identity comes from the deterministic trace, not from raw
definitional equality or an injectivity theorem for constructor typing. -/
theorem ConstructorWitness.trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : ConstructorWitness env U registry Γ left middle type demand)
    (second : ConstructorWitness env U registry Γ middle right type demand) :
    Nonempty (ConstructorWitness env U registry Γ left right type demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps, heads⟩ :=
    first.rightExposure.sameHead henv hscoped second.leftExposure
      first.rightTerminal second.leftTerminal
  have middleArguments : first.rightArguments.map (·.lift' i) =
      second.leftArguments.map (·.lift' j) := by
    rw [constructor_lift, constructor_lift] at heads
    exact constructor_arguments_inj heads
  obtain ⟨leftExposure⟩ := first.leftExposure.transport henv firstLeg
  obtain ⟨rightExposure⟩ := second.rightExposure.transport henv secondLeg
  have firstArguments := first.arguments.transport henv firstLeg
  have secondArguments := second.arguments.transport henv secondLeg
  simp only [List.map_map, Function.comp_def, ← Key.rename_comp, maps] at firstArguments secondArguments
  rw [middleArguments] at firstArguments
  refine ⟨{
    context := Ω
    map := second.map.comp j
    relevant := ?_
    leftLevels := first.leftLevels
    rightLevels := second.rightLevels
    leftArguments := first.leftArguments.map (·.lift' i)
    rightArguments := second.rightArguments.map (·.lift' j)
    leftExposure := ?_
    rightExposure := ?_
    leftTerminal := ?_
    rightTerminal := ?_
    leftUniverses := first.leftUniverses
    rightUniverses := second.rightUniverses
    arguments := firstArguments.trans henv hscoped.base secondArguments }⟩
  · obtain ⟨level, typed, relevant⟩ := second.relevant
    exact ⟨level, by simpa only [HasType, ← lift'_comp, lift'] using secondLeg.eq henv typed, relevant⟩
  · simpa only [constructor_lift, maps] using leftExposure
  · simpa only [constructor_lift] using rightExposure
  · rw [← constructor_lift, CanonicalDataHead.step_rename registry hscoped, first.leftTerminal]
    rfl
  · rw [← constructor_lift, CanonicalDataHead.step_rename registry hscoped, second.rightTerminal]
    rfl

end Lean4Lean.AnchoredSemantics
