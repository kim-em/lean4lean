import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyExtraction

/-! Family requests retain their raw parameter equalities independently of
computational input. The complete current certificate grammar preserves
these witnesses, including inner family padding and minimal focusing. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

def FamilySourceRequest (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (request : DataRequest (Profile n)) : Prop :=
  env.IsDefEq U target request.anchor (expression.subst σ) request.domain ∧
    Nonempty (GradedResult env U registry target locals σ available expression request.input)

def FamilyAtomRequests (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) : {n : Nat} → Atom n → Prop
  | _ + 1, .family family => family.name = name ∧ List.Forall₂ (· ≈ ·) family.levels levels ∧
      List.Forall₂ (FamilySourceRequest env U registry target locals σ available) arguments family.arguments
  | _ + 1, .pad atom => FamilyAtomRequests env U registry target locals σ available name levels arguments atom
  | _, _ => True

def FamilyProfileRequests (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, FamilyAtomRequests env U registry target locals σ available name levels arguments atom

theorem ConstructorSourceCaptures.requests
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))}
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available expressions requests) :
    List.Forall₂ (FamilySourceRequest env U registry target locals realization available)
      (expressions.map (·.subst replacement)) requests := by
  induction captures with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons ⟨head.anchor.1.trans head.pair, ⟨head.observation⟩⟩ ih

theorem FamilyConsumedCaptures.requestEvidence
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand)}
    (packet : FamilyConsumedCaptures consumed) :
    FamilyAtomRequests env U registry target locals σ available name levels arguments
      (n := n + 1) (.family demand) := by
  have evidence := packet.sourceCaptures.requests
  rw [consumed.length] at evidence
  have exactArguments :
      (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) =
        arguments := by
    simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
  rw [exactArguments] at evidence
  obtain ⟨rankEq, descriptorEq⟩ := packet.exactDemand
  rcases packet with ⟨rank, level, relevant, resultSort, relevance, requests, bound, adapter,
    footprint, captures, resources, sourceCaptures⟩
  dsimp only at rankEq descriptorEq evidence
  cases rankEq
  have same := eq_of_heq descriptorEq
  rw [← same]
  exact ⟨rfl, consumed.equivalent, evidence⟩

/-- Family refinement retains the entire literal descriptor. Only outer
padding recurses; this does not assert arbitrary code-support restriction. -/
private theorem FamilyProfileRequests.refine {focused profile : Profile n}
    (bound : focused ≤ profile)
    (origins : FamilyProfileRequests env U registry target locals σ available name levels arguments profile) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments focused := by
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

private theorem FamilyProfileRequests.pad
    (origins : FamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile n)) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem FamilyProfileRequests.sort (relevant : Bool) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments (Profile.sort (n := n) relevant) := by
  cases n with
  | zero => exact fun _ _ => True.intro
  | succ n =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial

private theorem FamilyProfileRequests.down
    (origins : FamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile (n + 1))) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact FamilyProfileRequests.sort relevant atom member
  | fn | pi | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem FamilyProfileRequests.rankShift
    (origins : FamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile (n + 1))) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments profile.rankShift := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  have origin := origins old ho
  cases old with
  | pi => trivial
  | sort | fn | pad | family | ctor | record => exact origin

private theorem FamilyProfileRequests.unshift
    (key : Key n)
    (origins : FamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile (n + 2))) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments (profile.unshift key) := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact FamilyProfileRequests.sort relevant atom member
  | fn | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi => cases List.mem_singleton.mp member; trivial

private theorem FamilyProfileRequests.map
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : FamilyProfileRequests env U registry target locals σ available name levels arguments profile) :
    FamilyProfileRequests env U registry target locals σ available name levels arguments (change.mapType profile) := by
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
  | _ + 1, _, _, .pad child => exact (FamilyProfileRequests.map child origins.down).pad
  | _, _, _, .trans first second => exact (origins.map first).map second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem familyRequests_pad
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    {arguments : List VExpr} {requests : List (DataRequest (Profile n))}
    (observations : List.Forall₂ (FamilySourceRequest env U registry target locals σ available)
      arguments requests) :
    List.Forall₂ (FamilySourceRequest env U registry target locals σ available)
      arguments (requests.map (DataRequest.map id Profile.pad)) := by
  induction observations with
  | nil => exact .nil
  | cons observed tail ih =>
    obtain ⟨pair, ⟨observed⟩⟩ := observed
    exact .cons ⟨pair, ⟨observed.pad henv hscoped hTarget⟩⟩ ih

variable {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).Fundamentals env registry)
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

include henv hscoped hTarget closed in
private theorem FamilyPlanConsumption.requestsOriginal
    {arguments : List VExpr} {atom : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments atom) :
    FamilyAtomRequests env U registry target locals σ available name levels arguments atom := by
  match n, atom with
  | _ + 1, .family family =>
    obtain ⟨packet⟩ := consumed.sourceCapturesOriginal henv hscoped
      (consumed.saturated henv hscoped hTarget) hTarget closed
    exact packet.requestEvidence
  | _ + 1, .pad atom => exact consumed.unpad.requestsOriginal
  | 0, atom => trivial
  | _ + 1, .sort _ | _ + 1, .fn _ _ | _ + 1, .pi _ _ _ _ |
      _ + 1, .ctor _ | _ + 1, .record _ => trivial
termination_by n

include origin henv hscoped headers shape notDefinition notNative hTarget closed fits head scope in
theorem Obs.familyRequestsOriginal
    (observation : Obs env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    FamilyProfileRequests env U registry target locals σ available name levels expression.getAppFnArgs.2 profile := by
  intro atom member
  obtain ⟨consumed, _⟩ := observation.consumeFamilyOriginal origin henv hscoped headers
    shape notDefinition notNative hTarget fits head scope resources member
  exact consumed.requestsOriginal henv hscoped hTarget closed

include origin henv hscoped headers shape notDefinition notNative hTarget closed fits head scope in
/-- Every actual source family certificate supplies observers of its exact
parameter requests, including requests created by family-specific padding. -/
theorem CodeCert.familyRequestsOriginal
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    FamilyProfileRequests env U registry target locals σ available name levels expression.getAppFnArgs.2 profile := by
  match certificate with
  | .seed observation _ =>
    exact observation.familyRequestsOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget closed fits head scope resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyRequestsOriginal (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyRequestsOriginal (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact (source.familyRequestsOriginal resources).pad
  | .familyPad source =>
    intro atom member
    cases List.mem_singleton.mp member
    have original := source.familyRequestsOriginal resources _ (List.mem_singleton_self _)
    exact ⟨original.1, original.2.1, familyRequests_pad henv hscoped hTarget original.2.2⟩
  | .unpad source =>
    intro atom member
    exact source.familyRequestsOriginal resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source =>
    exact (source.familyRequestsOriginal resources).down
  | .map change source =>
    exact (source.familyRequestsOriginal resources).map change
  | .focusMinimal source _ bound =>
    exact FamilyProfileRequests.refine bound (source.familyRequestsOriginal resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.familyRequestsOriginal resources _ member
termination_by sizeOf certificate

end Lean4Lean.AnchoredSource.Adapted
