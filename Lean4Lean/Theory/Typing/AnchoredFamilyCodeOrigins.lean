import Lean4Lean.Theory.Typing.AnchoredFamilyObservedCaptures

/-! Recover original family parameter observations from a code certificate.
The extracted requests retain their exact domains, anchors, and input profiles;
family-specific padding changes only the finite grade of those inputs. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

def FamilyAtomOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) : {n : Nat} → Atom n → Prop
  | _ + 1, .family family => List.Forall₂ (fun expression request => Nonempty
      (GradedResult env U registry target locals σ available expression request.input))
      arguments family.arguments
  | _ + 1, .pad atom => FamilyAtomOrigins env U registry target locals σ available arguments atom
  | _, _ => True

def FamilyProfileOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, FamilyAtomOrigins env U registry target locals σ available arguments atom

/-- Family refinement retains the entire literal descriptor. Only outer
padding recurses; this does not assert arbitrary code-support restriction. -/
private theorem FamilyProfileOrigins.refine {focused profile : Profile n}
    (bound : focused ≤ profile)
    (origins : FamilyProfileOrigins env U registry target locals σ available arguments profile) :
    FamilyProfileOrigins env U registry target locals σ available arguments focused := by
  induction n with
  | zero => exact fun _ _ => trivial
  | succ n ih =>
    intro atom member
    obtain ⟨other, present, covered⟩ := bound atom member
    have origin := origins other present
    cases atom with
    | sort | fn | pi | ctor | record => trivial
    | family family =>
      cases other <;> try contradiction
      cases covered
      exact origin
    | pad atom =>
      cases other <;> try contradiction
      exact ih covered (fun other member => by
        cases List.mem_singleton.mp member
        exact origin) atom (List.mem_singleton_self _)

theorem FamilyConsumedCaptures.requestObservations
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand)}
    (packet : FamilyConsumedCaptures consumed) :
    List.Forall₂ (fun expression request => Nonempty
      (GradedResult env U registry target locals σ available expression request.input))
      arguments demand.arguments := by
  have observed := packet.observations
  obtain ⟨rankEq, descriptorEq⟩ := packet.exactDemand
  rcases packet with ⟨rank, level, relevant, resultSort, relevance, requests, bound, adapter,
    footprint, captures, resources, sourceCaptures⟩
  dsimp only at rankEq descriptorEq observed
  cases rankEq
  have same := congrArg FamilyData.arguments (eq_of_heq descriptorEq)
  rwa [← same]

private theorem FamilyProfileOrigins.pad
    (origins : FamilyProfileOrigins env U registry target locals σ available arguments (profile : Profile n)) :
    FamilyProfileOrigins env U registry target locals σ available arguments profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem FamilyProfileOrigins.sort (relevant : Bool) :
    FamilyProfileOrigins env U registry target locals σ available arguments (Profile.sort (n := n) relevant) := by
  cases n with
  | zero => exact fun _ _ => True.intro
  | succ n =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial

private theorem FamilyProfileOrigins.down
    (origins : FamilyProfileOrigins env U registry target locals σ available arguments (profile : Profile (n + 1))) :
    FamilyProfileOrigins env U registry target locals σ available arguments profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact FamilyProfileOrigins.sort relevant atom member
  | fn | pi | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem FamilyProfileOrigins.rankShift
    (origins : FamilyProfileOrigins env U registry target locals σ available arguments (profile : Profile (n + 1))) :
    FamilyProfileOrigins env U registry target locals σ available arguments profile.rankShift := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  have origin := origins old ho
  cases old with
  | pi => trivial
  | sort | fn | pad | family | ctor | record => exact origin

private theorem FamilyProfileOrigins.unshift
    (key : Key n)
    (origins : FamilyProfileOrigins env U registry target locals σ available arguments (profile : Profile (n + 2))) :
    FamilyProfileOrigins env U registry target locals σ available arguments (profile.unshift key) := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact FamilyProfileOrigins.sort relevant atom member
  | fn | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi => cases List.mem_singleton.mp member; trivial

private theorem FamilyProfileOrigins.map
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : FamilyProfileOrigins env U registry target locals σ available arguments profile) :
    FamilyProfileOrigins env U registry target locals σ available arguments (change.mapType profile) := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origins
  | _ + 1, _, _, .reanchor admitted =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => trivial
  | _ + 1, _, _, .domainRekey path typed formed related =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => simp only [domainRekeyAtom]; split <;> trivial
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => simp only [AtomView.mapType, inputTypes] at *; split <;> trivial
  | _ + 2, _, _, .commutePadFn _ _ => exact origins.down.rankShift
  | _ + 2, _, _, .uncommutePadFn key _ => exact (origins.unshift key).pad
  | _ + 1, _, _, .fn _ child =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => trivial
  | _ + 1, _, _, .pad child => exact (FamilyProfileOrigins.map child origins.down).pad
  | _, _, _, .trans first second => exact (origins.map first).map second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem familyObservations_pad
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    {arguments : List VExpr} {requests : List (DataRequest (Profile n))}
    (observations : List.Forall₂ (fun expression request => Nonempty
      (GradedResult env U registry target locals σ available expression request.input)) arguments requests) :
    List.Forall₂ (fun expression request => Nonempty
      (GradedResult env U registry target locals σ available expression request.input))
      arguments (requests.map (DataRequest.map id Profile.pad)) := by
  induction observations with
  | nil => exact .nil
  | cons observed tail ih =>
    obtain ⟨observed⟩ := observed
    exact .cons ⟨observed.pad henv hscoped hTarget⟩ ih

variable {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ left right type}, origin.source.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {levels : List VLevel}
    (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)

include origin henv hscoped earlier hTarget closed in
private theorem FamilyPlanConsumption.origins
    {arguments : List VExpr} {atom : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments atom) :
    FamilyAtomOrigins env U registry target locals σ available arguments atom := by
  match n, atom with
  | _ + 1, .family family =>
    obtain ⟨typeLevel, formation⟩ := origin.typeInstance consumed.seedWF
    obtain ⟨packet⟩ := consumed.familySourceCaptures henv hscoped origin.ordered earlier
      formation hTarget closed
    exact packet.requestObservations
  | _ + 1, .pad atom => exact consumed.unpad.origins
  | 0, atom => trivial
  | _ + 1, .sort _ | _ + 1, .fn _ _ | _ + 1, .pi _ _ _ _ |
      _ + 1, .ctor _ | _ + 1, .record _ => trivial
termination_by n

include origin henv hscoped earlier shape notDefinition notNative hTarget closed fits head scope in
theorem Obs.familyOrigins
    (observation : Obs env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    FamilyProfileOrigins env U registry target locals σ available expression.getAppFnArgs.2 profile := by
  intro atom member
  obtain ⟨consumed⟩ := observation.consumeFamily origin henv hscoped (fun H => earlier H)
    shape notDefinition notNative hTarget fits head scope resources member
  exact consumed.origins origin henv hscoped earlier hTarget closed

include origin henv hscoped earlier shape notDefinition notNative hTarget closed fits head scope in
/-- Every actual source family certificate supplies observers of its exact
parameter requests, including requests created by family-specific padding. -/
theorem CodeCert.familyOrigins
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    FamilyProfileOrigins env U registry target locals σ available expression.getAppFnArgs.2 profile := by
  match certificate with
  | .seed observation _ =>
    exact observation.familyOrigins origin henv hscoped earlier shape notDefinition notNative
      hTarget closed fits head scope resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyOrigins (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyOrigins (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact (source.familyOrigins resources).pad
  | .familyPad source =>
    intro atom member
    cases List.mem_singleton.mp member
    have original := source.familyOrigins resources _ (List.mem_singleton_self _)
    exact familyObservations_pad henv hscoped hTarget original
  | .unpad source =>
    intro atom member
    exact source.familyOrigins resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source =>
    exact (source.familyOrigins resources).down
  | .map change source =>
    exact (source.familyOrigins resources).map change
  | .focusMinimal source _ bound =>
    exact FamilyProfileOrigins.refine bound (source.familyOrigins resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.familyOrigins resources _ member
termination_by sizeOf certificate

end Lean4Lean.AnchoredSource.Adapted
