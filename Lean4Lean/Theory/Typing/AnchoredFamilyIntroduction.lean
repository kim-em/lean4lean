import Lean4Lean.Theory.Typing.AnchoredFamilyHead
import Lean4Lean.Theory.Typing.AnchoredAdmission
import Lean4Lean.Theory.Typing.AnchoredCoreIntroduction
import Lean4Lean.Theory.Typing.CanonicalDataHeadProjection

/-! Literal family heads introduce the actual data clause using their
concrete argument admissions and declaration-independent inertness facts. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem ranked_future (henv : env.Ordered)
    (arguments : RankedData.Arguments env U (relations env U registry n) target keys xs ys)
    (route : FutureInsertion env U target future ρ) :
    RankedData.Arguments env U (relations env U registry n) future
      (keys.map (DataRequest.rename ρ)) (xs.map (·.lift' ρ)) (ys.map (·.lift' ρ)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨anchor, pair, typed, formed, code, first, second⟩ := head
    exact .cons ⟨anchor.weak' henv route.weakening, pair.weak' henv route.weakening,
      Profile.rename_hasType_iff.mpr typed,
      by simpa only [DataRequest.rename, DataRequest.map, Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed,
      TypeRelated.future henv route code,
      Related.future henv route first, Related.future henv route second⟩ ih

private theorem family_lift (name : Name) (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ fn, (mkApps fn arguments).lift' ρ =
      mkApps (fn.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro fn; rfl
  | cons arg rest ih => intro fn; exact ih (.app fn arg)

private def literalExposure (hTarget : OnCtx target (env.IsType U))
    (typed : env.HasType U target expression (.sort level)) :
    Exposure env U registry target expression target .refl expression where
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
  sound := by simpa only [lift'_refl] using TypeConversion.refl (A := expression)
  headType := ⟨level, typed⟩

private theorem family_head (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    (mkApps (.const name levels) arguments).getAppFnArgs.1 = .const name levels := by
  suffices ∀ fn, (mkApps fn arguments).getAppFnArgs.1 = fn.getAppFnArgs.1 from this _
  induction arguments with
  | nil => intro fn; rfl
  | cons arg rest ih => intro fn; simpa only [mkApps, List.foldl_cons, getAppFnArgs_app] using ih (.app fn arg)

private theorem levels_self (levels : List VLevel) : List.Forall₂ (· ≈ ·) levels levels := by
  induction levels with
  | nil => exact .nil
  | cons level rest ih => exact .cons rfl ih

theorem literalFamilyCodeOfInert
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {name : Name} {levels : List VLevel} {xs ys : List VExpr} {keys : List (DataRequest (Profile n))}
    {level : VLevel} {relevant : Bool} {target : List VExpr}
    (inert : CanonicalDataHead.HeadInert registry name)
    (raw : env.IsDefEq U target (mkApps (.const name levels) xs)
      (mkApps (.const name levels) ys) (.sort level))
    (flag : Relevant level relevant)
    (arguments : RankedData.Arguments env U (relations env U registry.toRegistry n) target keys xs ys) :
    RankedData.FamilyRelation env U registry (relations env U registry.toRegistry n) target
      (mkApps (.const name levels) xs) (mkApps (.const name levels) ys)
      ⟨name, levels, relevant, keys⟩ := by
  intro Δ ρ future
  have paired := raw.weak' henv future.weakening
  simp only [family_lift, lift'] at paired
  let code : RankedData.FamilyWitness env U registry (relations env U registry.toRegistry n) Δ
      (mkApps (.const name levels) (xs.map (·.lift' ρ)))
      (mkApps (.const name levels) (ys.map (·.lift' ρ)))
      ⟨name, levels, relevant, keys.map (DataRequest.rename ρ)⟩ := {
    registryScoped := hscoped
    headInert := inert
    context := Δ
    map := .refl
    leftLevel := level
    rightLevel := level
    leftRelevance := flag
    rightRelevance := flag
    path := by simpa only [lift'_refl] using TypeConversion.single paired
    leftType := by simpa only [lift'_refl] using paired.hasType.1
    rightType := by simpa only [lift'_refl] using paired.hasType.2
    leftLevels := levels
    rightLevels := levels
    leftArguments := xs.map (·.lift' ρ)
    rightArguments := ys.map (·.lift' ρ)
    leftExposure := literalExposure (future.targetWF henv) paired.hasType.1
    rightExposure := literalExposure (future.targetWF henv) paired.hasType.2
    leftTerminal := inert.step _ _
    rightTerminal := inert.step _ _
    leftUniverses := levels_self _
    rightUniverses := levels_self _
    arguments := by
      have same : DataRequest.rename (n := n) .refl = id := by
        funext request; exact DataRequest.rename_refl request
      rw [same, List.map_id]
      exact ranked_future henv arguments future }
  change Nonempty (RankedData.FamilyWitness env U registry (relations env U registry.toRegistry n) Δ
    ((mkApps (.const name levels) xs).lift' ρ) ((mkApps (.const name levels) ys).lift' ρ)
    ⟨name, levels, relevant, keys.map (DataRequest.rename ρ)⟩)
  simpa only [family_lift] using (show Nonempty _ from ⟨code⟩)

theorem literalFamilyCode
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {name : Name} {levels : List VLevel} {xs ys : List VExpr} {keys : List (DataRequest (Profile n))}
    {level : VLevel} {relevant : Bool} {target : List VExpr}
    (definitions : registry.definitions name = none)
    (natives : registry.natives name = none) (quotient : name ≠ ``Quot.lift)
    (raw : env.IsDefEq U target (mkApps (.const name levels) xs)
      (mkApps (.const name levels) ys) (.sort level))
    (flag : Relevant level relevant)
    (arguments : RankedData.Arguments env U (relations env U registry.toRegistry n) target keys xs ys) :
    RankedData.FamilyRelation env U registry (relations env U registry.toRegistry n) target
      (mkApps (.const name levels) xs) (mkApps (.const name levels) ys)
      ⟨name, levels, relevant, keys⟩ :=
  literalFamilyCodeOfInert henv hscoped ⟨definitions, natives, Or.inr quotient⟩ raw flag arguments

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Related.family
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right type : VExpr}
    {demand : FamilyData (Profile n)} {support : Profile (n + 1)}
    (typed : (Profile.singleton (n := n + 1) (.family demand)).HasType support)
    (code : TypeRelated env U registry Γ type type support)
    (family : RankedData.FamilyRelation env U registry (relations env U registry n)
      Γ left right demand) :
    Related env U registry Γ left right type (Profile.singleton (n := n + 1) (.family demand)) support := by
  apply CoreRelated.related henv hscoped
  refine ⟨typed, code, ?_⟩
  intro atom member
  cases List.mem_singleton.mp member
  intro Δ ρ future atom member
  simp only [Profile.rename_singleton, Atom.rename_family] at member
  cases List.mem_singleton.mp member
  exact family Δ ρ future

end Lean4Lean.AnchoredSemantics
