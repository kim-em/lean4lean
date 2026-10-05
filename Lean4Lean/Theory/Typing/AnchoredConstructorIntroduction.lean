import Lean4Lean.Theory.Typing.AnchoredFamilyIntroduction
import Lean4Lean.Theory.Typing.AnchoredDataDropFrame
import Lean4Lean.Theory.Typing.CanonicalDataHeadProjection

/-! Actual constructor values retain their declaration result headers and
both family bridges. Each future query shifts these same finite requests. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem TypeRelated.familyRelation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right : VExpr} {support : Profile (n + 1)}
    {family : FamilyData (Profile n)}
    (code : TypeRelated env U registry Γ left right support)
    (member : (.family family : Atom (n + 1)) ∈ support.atoms) :
    RankedData.FamilyRelation env U registry (relations env U registry n) Γ left right family := by
  intro Δ ρ future
  simpa only [Atom.rename_family, FamilyData.rename, CodeAtom] using
    code Δ ρ future _ (List.mem_map.mpr ⟨_, member, rfl⟩)

namespace RankedData
private theorem head_lift (name : Name) (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ fn, (mkApps fn arguments).lift' ρ =
      mkApps (fn.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro fn; rfl
  | cons arg rest ih => intro fn; exact ih (.app fn arg)

private def literalExposure (hTarget : OnCtx target (env.IsType U))
    (typed : env.HasType U target expression type) :
    ConstructorExposure env U registry target expression type target .refl expression where
  added := []
  result := expression
  postMap := .refl
  trace := .refl
  generated := .refl hTarget
  postContext := target
  post := .refl hTarget
  terminal := .refl
  map_eq := rfl
  result_eq := lift'_refl
  sound := by simpa only [lift'_refl, HasType] using typed

private theorem levels_self (levels : List VLevel) : List.Forall₂ (· ≈ ·) levels levels := by
  induction levels with
  | nil => exact .nil
  | cons level rest ih => exact .cons rfl ih

/-- The constructor terminal rule consumes actual typed endpoints, literal
headers from declaration lookup, and exact binary result-family bridges. -/
theorem literalConstructor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} {xs ys : List VExpr} {type : VExpr}
    {demand : ConstructorData (Profile n)}
    (inert : CanonicalDataHead.HeadInert registry demand.name)
    (raw : env.IsDefEq U Γ (mkApps (.const demand.name demand.levels) xs)
      (mkApps (.const demand.name demand.levels) ys) type)
    (arguments : Arguments env U (relations env U registry n) Γ demand.arguments xs ys)
    (leftHeader : ConstructorResultHeader env demand.name demand.family.name demand.levels xs)
    (rightHeader : ConstructorResultHeader env demand.name demand.family.name demand.levels ys)
    (leftBridge : FamilyRelation env U registry (relations env U registry n) Γ
      leftHeader.result type demand.family)
    (rightBridge : FamilyRelation env U registry (relations env U registry n) Γ
      rightHeader.result type demand.family) :
    ConstructorRelation env U registry (relations env U registry n) Γ
      (mkApps (.const demand.name demand.levels) xs)
      (mkApps (.const demand.name demand.levels) ys) type demand := by
  intro Δ ρ future
  have pair := raw.weak' henv future.weakening
  simp only [head_lift] at pair
  have renamedRefl (d : FamilyData (Profile n)) : d.rename .refl = d := by
    unfold FamilyData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl, FamilyData.map_id]
  change Nonempty (ConstructorWitness env U registry (relations env U registry n) Δ
    ((mkApps (.const demand.name demand.levels) xs).lift' ρ)
    ((mkApps (.const demand.name demand.levels) ys).lift' ρ) (type.lift' ρ) (demand.rename ρ))
  rw [head_lift, head_lift]
  refine ⟨{
    headInert := inert
    context := Δ, map := .refl
    leftLevels := demand.levels, rightLevels := demand.levels
    leftArguments := xs.map (·.lift' ρ), rightArguments := ys.map (·.lift' ρ)
    leftExposure := .ofExposure henv (literalExposure (future.targetWF henv) pair.hasType.1)
    rightExposure := .ofExposure henv (literalExposure (future.targetWF henv) pair.hasType.2)
    leftTerminal := inert.step _ _, rightTerminal := inert.step _ _
    leftUniverses := levels_self _, rightUniverses := levels_self _
    arguments := ?_
    leftHeader := by simpa only [ConstructorData.rename, ConstructorData.map, FamilyData.map] using leftHeader.rename ρ
    rightHeader := by simpa only [ConstructorData.rename, ConstructorData.map, FamilyData.map] using rightHeader.rename ρ
    leftBridge := ?_, rightBridge := ?_ }⟩
  · change Arguments env U (relations env U registry n) Δ
      ((demand.arguments.map (DataRequest.rename ρ)).map (DataRequest.rename .refl))
      (xs.map (·.lift' ρ)) (ys.map (·.lift' ρ))
    have same : DataRequest.rename (n := n) .refl = id := by
      funext request; exact DataRequest.rename_refl request
    rw [same, List.map_id]
    exact arguments.future henv future
  · change FamilyRelation env U registry (relations env U registry n) Δ
      (id (leftHeader.rename ρ)).result ((type.lift' ρ).lift' .refl)
      ((demand.family.rename ρ).rename .refl)
    simpa only [id_eq, renamedRefl, lift'_refl, leftHeader.result_rename henv] using
      leftBridge.future henv future
  · change FamilyRelation env U registry (relations env U registry n) Δ
      (id (rightHeader.rename ρ)).result ((type.lift' ρ).lift' .refl)
      ((demand.family.rename ρ).rename .refl)
    simpa only [id_eq, renamedRefl, lift'_refl, rightHeader.result_rename henv] using
      rightBridge.future henv future

end RankedData

theorem Related.constructor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right type : VExpr}
    {demand : ConstructorData (Profile n)} {support : Profile (n + 1)}
    (typed : (Profile.singleton (n := n + 1) (.ctor demand)).HasType support)
    (code : TypeRelated env U registry Γ type type support)
    (value : RankedData.ConstructorRelation env U registry (relations env U registry n)
      Γ left right type demand) :
    Related env U registry Γ left right type (Profile.singleton (n := n + 1) (.ctor demand)) support := by
  apply CoreRelated.related henv hscoped
  refine ⟨typed, code, ?_⟩
  intro atom member
  cases List.mem_singleton.mp member
  exact value

end Lean4Lean.AnchoredSemantics
