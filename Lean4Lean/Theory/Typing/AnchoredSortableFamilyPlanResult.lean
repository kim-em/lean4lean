import Lean4Lean.Theory.Typing.AnchoredSortableFamilyPlan
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanRows
import Lean4Lean.Theory.Typing.AnchoredSortableAdapter

/-! A rich family plan retains its own source type certificate; both are
closed over the actual declaration rows without erasing formation queries. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

/-- The source type support is rebuilt along with the computational plan.
Both keep their actual footprints in the retained finite ledger. -/
structure SortableFamilyPlanResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (name : Name) (levels : List VLevel) {declaredType : VExpr}
    (signature : ConstantTelescope declaredType) (arguments : List VExpr)
    (available : Valuation) (expression : VExpr) (atom : Atom n) where
  footprint : Footprint
  plan : SortableFamilyPlan env U registry target name levels signature arguments (.singleton atom) footprint
  resources : footprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : SortableCert env U registry target (List.range arguments.length)
    (nativeCaptureSubst arguments) expression true support typeFootprint
  typeResources : typeFootprint.Available available
  typed : (Profile.singleton atom).HasType support

noncomputable def SortableFamilyPlanResult.terminal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {available : Valuation} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (saturated : arguments.length = signature.domains.length)
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (captures : FamilyCaptures env U registry target signature.domains.reverse
      (List.range arguments.length) (nativeCaptureSubst arguments)
      (constantCaptureVariables arguments.length) keys footprint)
    (resources : footprint.Available available) :
    SortableFamilyPlanResult env U registry target name levels signature arguments available signature.result
      (n := n + 1) (.family ⟨name, levels, relevant, keys⟩) where
  footprint := footprint
  plan := .terminal saturated resultSort relevance captures
  resources := resources
  support := .sort relevant
  typeFootprint := []
  certificate := by
    rw [resultSort]
    exact .seed (.sort relevance) (Profile.HasType.sort relevant)
  typeResources := fun _ _ member => nomatch member
  typed := captures.familyTyped relevant

noncomputable def SortableFamilyPlanResult.raise
    {name : Name} {levels : List VLevel} {atom : Atom n}
    (result : SortableFamilyPlanResult env U registry target name levels signature arguments available expression atom)
    {N : Nat} (bound : n ≤ N) :
    SortableFamilyPlanResult env U registry target name levels signature arguments available expression
      (raiseAtom N bound atom) where
  footprint := result.footprint
  plan := by simpa only [raiseProfile_singleton] using result.plan.raise bound
  resources := result.resources
  support := raiseProfile N bound result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate.raise bound
  typeResources := result.typeResources
  typed := by simpa only [raiseProfile_singleton] using Profile.HasType.raise bound result.typed

noncomputable def SortableFamilyPlanResult.view
    {name : Name} {levels : List VLevel} {atom atom' : Atom n}
    (result : SortableFamilyPlanResult env U registry target name levels signature arguments available expression atom)
    (view : AtomView env U registry target atom atom') :
    SortableFamilyPlanResult env U registry target name levels signature arguments available expression atom' where
  footprint := result.footprint
  plan := .view result.plan view
  resources := result.resources
  support := view.mapType result.support
  typeFootprint := result.typeFootprint
  certificate := .map view result.certificate
  typeResources := result.typeResources
  typed := view.mapType_typed result.typed

theorem SortableFamilyPlanResult.bareObservation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {seed : Subst}
    {name : Name} {levels : List VLevel} {info : VConstant}
    {signature : ConstantTelescope (info.type.instL levels)} {atom : Atom n}
    (result : SortableFamilyPlanResult env U registry target name levels signature [] (fun _ => [])
      (info.type.instL levels) atom)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = info.uvars)
    (typeClosed : info.type.Closed) :
    Nonempty (SortableObs env U registry target locals seed (.const name levels) (.singleton atom) []) := by
  have footprintEmpty : result.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.resources index need member
  have typeEmpty : result.typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.typeResources index need member
  have levelsSelf : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls := by
    intro ls
    induction ls with
    | nil => exact .nil
    | cons level levels ih => exact .cons rfl ih
  exact ⟨.family lookup notDefinition notNative notQuotient levelsWF length levelsWF (levelsSelf levels)
    signature typeClosed (by simpa only [List.length_nil, List.range_zero, typeEmpty] using result.certificate)
    result.typed (by simpa only [footprintEmpty] using result.plan)⟩

end Lean4Lean.AnchoredSource.Adapted
