import Lean4Lean.Theory.Typing.AnchoredFamilyCodeOrigins

/-! A fully applied literal family has only its own family atoms in source
code certificates, with arbitrary outer padding. Downward grade changes may
erase atoms; they cannot replace the family with a sort or function shape. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

/-- Outer padding preserves the exact original family name. -/
def FamilyCodeAtom (name : Name) : {n : Nat} → Atom n → Prop
  | _ + 1, .family family => family.name = name
  | _ + 1, .pad atom => FamilyCodeAtom name atom
  | _, _ => False

def FamilyCodeProfile (name : Name) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, FamilyCodeAtom name atom

/-- Structural refinement of family-only profiles preserves the exact
family descriptor or descends through the same outer padding. -/
private theorem FamilyCodeProfile.refine {focused profile : Profile n}
    (bound : focused ≤ profile) (shape : FamilyCodeProfile name profile) :
    FamilyCodeProfile name focused := by
  induction n with
  | zero =>
    intro atom member
    obtain ⟨other, present, _⟩ := bound atom member
    exact False.elim (shape other present)
  | succ n ih =>
    intro atom member
    obtain ⟨other, present, covered⟩ := bound atom member
    have original := shape other present
    cases other with
    | sort | fn | pi | ctor | record => exact False.elim original
    | family family =>
      cases atom <;> try contradiction
      cases covered
      exact original
    | pad other =>
      cases atom <;> try contradiction
      exact ih covered (fun atom member => by
        cases List.mem_singleton.mp member
        exact original) _ (List.mem_singleton_self _)

private theorem FamilyCodeAtom.shift {atom : Atom n} :
    FamilyCodeAtom name (AdapterNormal.shiftAtom atom) ↔ FamilyCodeAtom name atom := by
  cases n with
  | zero => rfl
  | succ n => cases atom <;> rfl

private theorem FamilyCodeAtom.normal {atom : Atom n} :
    FamilyCodeAtom name (AdapterNormal.atom atom) ↔ FamilyCodeAtom name atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases atom with
    | pad atom => exact FamilyCodeAtom.shift.trans ih
    | sort | fn | pi | family | ctor | record => rfl

private theorem FamilyCodeAtom.adapter {a b : Atom n}
    (adapter : AtomAdapter env U registry target a b)
    (shape : FamilyCodeAtom name a) : FamilyCodeAtom name b := by
  induction n with
  | zero => exact False.elim shape
  | succ n ih =>
    cases adapter with
    | refl => exact shape
    | fn => exact False.elim shape
    | pad child => exact ih child shape

private theorem FamilyCodeAtom.normalAdapter {a b : Atom n}
    (adapter : NormalAtomAdapter env U registry target a b)
    (shape : FamilyCodeAtom name a) : FamilyCodeAtom name b :=
  FamilyCodeAtom.normal.mp (FamilyCodeAtom.adapter adapter (FamilyCodeAtom.normal.mpr shape))

private theorem FamilyCodeAtom.raise {n N : Nat} (bound : n ≤ N) {atom : Atom n} :
    FamilyCodeAtom name (raiseAtom N bound atom) ↔ FamilyCodeAtom name atom := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rw [raiseAtom_self]
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; rw [raiseAtom_self]
    · have small : n ≤ N := by omega
      rw [raiseAtom_step small]
      exact ih small

theorem FamilyPlanConsumption.familyShape
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {atom : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels arguments atom)
    (saturated : arguments.length = info.type.forallArity) : FamilyCodeAtom name atom := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature,
    typeClosed, anchors, length, output, footprint, plan, adapter, valuation,
    valuationClosed, originalRaw, originalFits, originalResources, originalObserved⟩
  have arity := congrArg VExpr.forallArity signature.type_eq
  simp only [forallArity_instL, forallArity_wrapForalls] at arity
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  cases front with
  | terminal full resultSort relevance captures bound frontAdapter =>
    exact (FamilyCodeAtom.raise demandBound).mp (FamilyCodeAtom.normalAdapter (frontAdapter.comp adapter)
      ((FamilyCodeAtom.raise bound).mpr rfl))
  | binder origin =>
    have before := (List.getElem?_eq_some_iff.mp origin).1
    omega


private theorem FamilyCodeProfile.pad
    (shape : FamilyCodeProfile name (profile : Profile n)) : FamilyCodeProfile name profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact shape old ho

private theorem FamilyCodeProfile.down
    (shape : FamilyCodeProfile name (profile : Profile (n + 1))) :
    FamilyCodeProfile name profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := shape old ho
  cases old with
  | sort | fn | pi | ctor | record => exact False.elim origin
  | family => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem FamilyCodeProfile.rankShift
    (shape : FamilyCodeProfile name (profile : Profile (n + 1))) :
    FamilyCodeProfile name profile.rankShift := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  have origin := shape old ho
  cases old with
  | sort | fn | pi | ctor | record => exact False.elim origin
  | family | pad => exact origin

private theorem FamilyCodeProfile.unshift (key : Key n)
    (shape : FamilyCodeProfile name (profile : Profile (n + 2))) :
    FamilyCodeProfile name (profile.unshift key) := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := shape old ho
  cases old with
  | sort | fn | pi | ctor | record => exact False.elim origin
  | family => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem FamilyCodeProfile.map {a b : Atom n}
    (change : AtomView env U registry target a b)
    (shape : FamilyCodeProfile name profile) : FamilyCodeProfile name (change.mapType profile) := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact shape
  | _ + 1, _, _, .reanchor admitted =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := shape old ho
    cases old with
    | sort | fn | pi | ctor | record => exact False.elim origin
    | family | pad => exact origin
  | _ + 1, _, _, .domainRekey path typed formed related =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := shape old ho
    cases old with
    | sort | fn | pi | ctor | record => exact False.elim origin
    | family | pad => exact origin
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := shape old ho
    cases old with
    | sort | fn | pi | ctor | record => exact False.elim origin
    | family | pad => exact origin
  | _ + 2, _, _, .commutePadFn _ _ => exact shape.down.rankShift
  | _ + 2, _, _, .uncommutePadFn key _ => exact (shape.unshift key).pad
  | _ + 1, _, _, .fn _ child =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := shape old ho
    cases old with
    | sort | fn | pi | ctor | record => exact False.elim origin
    | family | pad => exact origin
  | _ + 1, _, _, .pad child => exact (FamilyCodeProfile.map child shape.down).pad
  | _, _, _, .trans first second => exact (shape.map first).map second
termination_by sizeOf change

variable {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ A level}, origin.source.IsDefEqStrong U Γ A A (.sort level) →
      GradedJoint env U registry Γ A A (.sort level))
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {levels : List VLevel}
    (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (saturated : expression.getAppFnArgs.2.length = info.type.forallArity)

include origin henv hscoped earlier shape notDefinition notNative hTarget fits head scope saturated in
/-- Saturation rules out a function demand in the actual family observer. -/
theorem Obs.familyShape
    (observation : Obs env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) : FamilyCodeProfile name profile := by
  intro atom member
  obtain ⟨consumed⟩ := observation.consumeFamily origin henv hscoped (fun H => earlier H)
    shape notDefinition notNative hTarget fits head scope resources member
  exact consumed.familyShape henv hscoped hTarget saturated

include origin henv hscoped earlier shape notDefinition notNative hTarget fits head scope saturated in
/-- Every code atom of the fully applied original family has the same family
name under padding; no other atom case is left unconstrained. -/
theorem CodeCert.familyShape
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) : FamilyCodeProfile name profile := by
  match certificate with
  | .seed observation _ =>
    exact observation.familyShape origin henv hscoped earlier shape notDefinition notNative
      hTarget fits head scope saturated resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyShape (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyShape (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.familyShape resources).pad
  | .familyPad source =>
    intro atom member
    cases List.mem_singleton.mp member
    exact source.familyShape resources _ (List.mem_singleton_self _)
  | .unpad source =>
    intro atom member
    exact source.familyShape resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.familyShape resources).down
  | .map change source => exact (source.familyShape resources).map change
  | .focusMinimal source _ bound =>
    exact FamilyCodeProfile.refine bound (source.familyShape resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.familyShape resources _ member
termination_by sizeOf certificate

end Lean4Lean.AnchoredSource.Adapted
