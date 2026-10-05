import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyConsumption

/-! Every frozen family parameter request retains its actual hereditary
source query, raw anchor equation and exact universe packet. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

def SortableFamilySourceRequest (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (request : DataRequest (Profile n)) : Prop :=
  env.IsDefEq U target request.anchor (expression.subst σ) request.domain ∧
    Nonempty (SortableGradedResult env U registry target locals σ available expression request.input)

def SortableFamilyRequestProperty (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr)
    (family : FamilyData (Profile n)) : Prop :=
  family.name = name ∧ List.Forall₂ (· ≈ ·) family.levels levels ∧
    List.Forall₂ (SortableFamilySourceRequest env U registry target locals σ available) arguments family.arguments

def SortableFamilyAtomRequests (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) : {n : Nat} → Atom n → Prop :=
  FamilyAtomProperty (SortableFamilyRequestProperty env U registry target locals σ available name levels arguments)

def SortableFamilyProfileRequests (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, SortableFamilyAtomRequests env U registry target locals σ available name levels arguments atom

def SortableGradedSubstitution (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (replacement : Subst) (prior : Valuation) : Prop :=
  ∀ index need, need ∈ prior index →
    Nonempty (SortableGradedResult env U registry target locals σ available (replacement index) need.profile)

theorem SortableGradedValuation.substitution
    (observed : SortableGradedValuation env U registry target locals σ available arguments prior) :
    SortableGradedSubstitution env U registry target locals σ available (nativeCaptureSubst arguments) prior := by
  intro index need member
  obtain ⟨bound, result⟩ := observed index need member
  simpa only [nativeCaptureSubst, dif_pos bound] using result

theorem SortableGradedSubstitution.supply
    (observed : SortableGradedSubstitution env U registry target locals σ available replacement prior)
    (resources : footprint.Available prior) :
    Nonempty (SortableGradedSupply env U registry target locals σ replacement available footprint) := by
  induction footprint with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨value⟩ := observed entry.1 entry.2 (resources _ _ List.mem_cons_self)
    obtain ⟨tail⟩ := ih (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
    exact ⟨.cons value tail⟩

/-- Family refinement retains the entire literal descriptor. Only outer
padding recurses; this does not assert arbitrary code-support restriction. -/
private theorem SortableFamilyProfileRequests.refine {focused profile : Profile n}
    (bound : focused ≤ profile)
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments profile) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments focused := by
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

private theorem SortableFamilyProfileRequests.pad
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile n)) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem SortableFamilyProfileRequests.sort (relevant : Bool) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (Profile.sort (n := n) relevant) := by
  cases n with
  | zero => exact fun _ _ => True.intro
  | succ n =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial

private theorem SortableFamilyProfileRequests.down
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile (n + 1))) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact SortableFamilyProfileRequests.sort relevant atom member
  | fn | pi | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem SortableFamilyProfileRequests.rankShift
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile (n + 1))) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments profile.rankShift := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  have origin := origins old ho
  cases old with
  | pi => trivial
  | sort | fn | pad | family | ctor | record => exact origin

private theorem SortableFamilyProfileRequests.unshift
    (key : Key n)
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (profile : Profile (n + 2))) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (profile.unshift key) := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact SortableFamilyProfileRequests.sort relevant atom member
  | fn | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi => cases List.mem_singleton.mp member; trivial

private theorem SortableFamilyProfileRequests.map
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments profile) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments (change.mapType profile) := by
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
  | _ + 1, _, _, .pad child => exact (SortableFamilyProfileRequests.map child origins.down).pad
  | _, _, _, .trans first second => exact (origins.map first).map second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem sortableFamilyRequests_pad
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    {arguments : List VExpr} {requests : List (DataRequest (Profile n))}
    (observations : List.Forall₂ (SortableFamilySourceRequest env U registry target locals σ available)
      arguments requests) :
    List.Forall₂ (SortableFamilySourceRequest env U registry target locals σ available)
      arguments (requests.map (DataRequest.map id Profile.pad)) := by
  induction observations with
  | nil => exact .nil
  | cons observed tail ih =>
    obtain ⟨pair, ⟨observed⟩⟩ := observed
    exact .cons ⟨pair, ⟨observed.pad henv hscoped hTarget⟩⟩ ih


private theorem SortableFamilyRequestProperty.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {family : FamilyData (Profile n)}
    (origin : SortableFamilyRequestProperty env U registry target locals σ available name levels arguments family) :
    SortableFamilyRequestProperty env U registry target locals σ available name levels arguments family.pad :=
  ⟨origin.1, origin.2.1, sortableFamilyRequests_pad henv hscoped hTarget origin.2.2⟩

private theorem SortableFamilyProfileRequests.codeAction
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : SortableFamilyProfileRequests env U registry target locals σ available name levels arguments profile) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels arguments nextProfile :=
  action.familyProperty (fun origin => origin.pad henv hscoped hTarget) origins

private theorem SortableFamilyAtomRequests.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {a b : Atom n} (action : AtomAction env U registry target a b)
    (origin : SortableFamilyAtomRequests env U registry target locals σ available name levels arguments a) :
    SortableFamilyAtomRequests env U registry target locals σ available name levels arguments b :=
  GeneralNormalAtomAdapter.familyProperty (action.toGeneralAdapter henv hscoped hTarget)
    (fun origin => origin.pad henv hscoped hTarget) origin

theorem FamilyCaptures.sortableRequests
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {captureLocals callerLocals : List Nat}
    {seed actual replacement realization : Subst}
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))} {footprint : Footprint}
    {captureAvailable callerAvailable : Valuation}
    (captures : FamilyCaptures env U registry target source captureLocals seed expressions requests footprint)
    (hTarget : OnCtx target (env.IsType U)) (callerClosed : callerAvailable.AtomClosed)
    (substitutions : Ctx.SubstEq env U target seed actual source)
    (resources : footprint.Available captureAvailable)
    (observed : SortableGradedSubstitution env U registry target callerLocals realization callerAvailable
      replacement captureAvailable)
    (agree : ∀ index < source.length, actual index = (replacement index).subst realization) :
    List.Forall₂ (SortableFamilySourceRequest env U registry target callerLocals realization callerAvailable)
      (expressions.map (·.subst replacement)) requests := by
  match captures with
  | .nil => exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨supply⟩ := observed.supply (fun i need member =>
      resources i need (List.mem_append_left _ member))
    obtain ⟨reified⟩ := (value.realizeVariable (replacement.comp realization)).substituteSortable
      henv hscoped hTarget replacement realization rfl callerLocals callerAvailable callerClosed supply
    let selected : SortableGradedResult env U registry target callerLocals realization callerAvailable
        (replacement _) _ := {
      rank := reified.rank
      bound := reified.bound
      raw := reified.raw
      footprint := reified.footprint
      observation := reified.observation
      adapter := reified.adapter.comp (adapter.toGeneral.raise henv hscoped hTarget reified.bound)
      resources := reified.resources
      live := reified.live }
    have rest := tail.sortableRequests henv hscoped hTarget callerClosed substitutions
      (fun i need member => resources i need (List.mem_append_right _ member)) observed agree
    refine .cons ⟨?_, ⟨selected⟩⟩ rest
    have pair := alignment.path.symm.cast (substitutions.lookup lookup)
    have pair' := anchor.1.trans pair
    simpa only [subst_bvar, agree _ lookup.lt] using pair'
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

theorem SortableFamilyPlanConsumption.saturated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand)) :
    arguments.length = consumed.signature.domains.length := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature,
    typeClosed, anchors, length, output, footprint, plan, resultAdapter, valuation,
    valuationClosed, originalRaw, originalResources, originalObserved⟩
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  cases front with
  | terminal saturated => exact length.symm.trans saturated
  | binder _ _ _ _ _ _ adapter =>
    exact (GeneralNormalAtomAdapter.fn_not_family demandBound (adapter.toGeneral.comp resultAdapter)).elim

theorem SortableFamilyPlanConsumption.familyRequests
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand)) :
    SortableFamilyAtomRequests env U registry target locals σ available name levels arguments
      (n := n + 1) (.family demand) := by
  have full := consumed.saturated henv hscoped hTarget
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, output, footprint, plan, resultAdapter, valuation, valuationClosed,
    originalRaw, originalResources, originalObserved⟩
  change arguments.length = signature.domains.length at full
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  cases front with
  | terminal saturated shape relevant captures bound adapter =>
    rename_i originRank originLevel originFlag originKeys
    have raw := originalRaw
    rw [full, List.take_length] at raw
    have actual := captures.sortableRequests henv hscoped hTarget closed raw originalResources
      originalObserved.substitution (by
        intro index within
        have bound : index < arguments.length := by simpa only [List.length_reverse, ← full] using within
        simp only [nativeCaptureSubst, List.length_map, dif_pos bound, List.getElem_map])
    rw [length] at actual
    have exactArguments :
        (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) = arguments := by
      simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
    rw [exactArguments] at actual
    have sourceProperty : SortableFamilyRequestProperty env U registry target locals σ available
        name levels arguments ⟨name, seedLevels, originFlag, originKeys⟩ := ⟨rfl, equivalent, actual⟩
    have raisedProperty := (FamilyAtomProperty.raise_iff
      (property := SortableFamilyRequestProperty env U registry target locals σ available name levels arguments) bound
      (AtomData.family ⟨name, seedLevels, originFlag, originKeys⟩)).mpr sourceProperty
    have requestedProperty := GeneralNormalAtomAdapter.familyProperty
      (adapter.toGeneral.comp resultAdapter)
      (property := SortableFamilyRequestProperty env U registry target locals σ available name levels arguments)
      (fun source => source.pad henv hscoped hTarget) raisedProperty
    exact (FamilyAtomProperty.raise_iff demandBound (.family demand)).mp requestedProperty
  | binder origin =>
    have bound := (List.getElem?_eq_some_iff.mp origin).1
    have equal := length.trans full
    omega

theorem SortableFamilyPlanConsumption.requests
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (atom : Atom n)) :
    SortableFamilyAtomRequests env U registry target locals σ available name levels arguments atom := by
  match n, atom with
  | _ + 1, .family family => exact consumed.familyRequests henv hscoped hTarget closed
  | k + 1, .pad atom => exact SortableFamilyPlanConsumption.requests (n := k) henv hscoped hTarget closed consumed.unpad
  | 0, atom => trivial
  | _ + 1, .sort _ | _ + 1, .fn _ _ | _ + 1, .pi _ _ _ _ |
      _ + 1, .ctor _ | _ + 1, .record _ => trivial
termination_by n

private theorem SortableFamilyAtomRequests.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : SortableFamilyAtomRequests env U registry target locals σ available name levels arguments a) :
    SortableFamilyAtomRequests env U registry target locals σ available name levels arguments b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => trivial
  | _ + 1, _, _, .domainRekey _ _ _ _ => trivial
  | _ + 1, _, _, .input _ _ => trivial
  | _ + 2, _, _, .commutePadFn _ _ => trivial
  | _ + 2, _, _, .uncommutePadFn _ _ => trivial
  | _ + 1, _, _, .fn _ _ => trivial
  | k + 1, _, _, .pad child => exact SortableFamilyAtomRequests.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

variable {callerEnv env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).SortableFundamentals env registry)
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (fits : SortableTailFits callerEnv env U registry target source locals σ σ available)
    {expression : VExpr} {levels : List VLevel}
    (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)

include origin henv hscoped headers shape notDefinition notNative hTarget closed fits head scope in
theorem Obs.familyRequestsSortable
    (observation : Obs env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels expression.getAppFnArgs.2 profile := by
  intro atom member
  obtain ⟨consumed, _⟩ := observation.consumeFamilySortable origin henv hscoped headers
    shape notDefinition notNative hTarget fits head scope resources member
  exact consumed.requests henv hscoped hTarget closed

include origin henv hscoped headers shape notDefinition notNative hTarget closed fits head scope in
/-- Every actual source family certificate supplies observers of its exact
parameter requests, including requests created by family-specific padding. -/
theorem CodeCert.familyRequestsSortable
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels expression.getAppFnArgs.2 profile := by
  match certificate with
  | .seed observation _ =>
    exact observation.familyRequestsSortable origin henv hscoped headers shape notDefinition notNative
      hTarget closed fits head scope resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyRequestsSortable (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyRequestsSortable (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact (source.familyRequestsSortable resources).pad
  | .familyPad source =>
    intro atom member
    cases List.mem_singleton.mp member
    have original := source.familyRequestsSortable resources _ (List.mem_singleton_self _)
    exact ⟨original.1, original.2.1, sortableFamilyRequests_pad henv hscoped hTarget original.2.2⟩
  | .unpad source =>
    intro atom member
    exact source.familyRequestsSortable resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source =>
    exact (source.familyRequestsSortable resources).down
  | .map change source =>
    exact (source.familyRequestsSortable resources).map change
  | .focusMinimal source _ bound =>
    exact SortableFamilyProfileRequests.refine bound (source.familyRequestsSortable resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.familyRequestsSortable resources _ member
termination_by sizeOf certificate


include origin henv hscoped headers shape notDefinition notNative hTarget closed fits
omit head scope
mutual
theorem SortableCert.familyRequestsOriginal
    {expression : VExpr}
    (certificate : SortableCert env U registry target locals σ expression relevant profile footprint)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels expression.getAppFnArgs.2 profile := by
  match certificate with
  | .seed observation _ =>
    exact observation.familyRequestsSortable origin henv hscoped headers shape notDefinition notNative
      hTarget closed fits head scope resources
  | .observe observation _ =>
    exact observation.familyRequestsOriginal head scope resources
  | .ofCode source _ =>
    exact source.familyRequestsSortable origin henv hscoped headers shape notDefinition notNative
      hTarget closed fits head scope resources
  | .pi .. => simp only [getAppFnArgs_forallE] at head; cases head
  | .sortPad source => exact SortableFamilyProfileRequests.sort _
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyRequestsOriginal head scope (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyRequestsOriginal head scope (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact (source.familyRequestsOriginal head scope resources).pad
  | .familyPad source =>
    intro atom member
    cases List.mem_singleton.mp member
    have original := source.familyRequestsOriginal head scope resources _ (List.mem_singleton_self _)
    exact ⟨original.1, original.2.1, sortableFamilyRequests_pad henv hscoped hTarget original.2.2⟩
  | .unpad source =>
    intro atom member
    exact source.familyRequestsOriginal head scope resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source =>
    exact (source.familyRequestsOriginal head scope resources).down
  | .map change source =>
    exact (source.familyRequestsOriginal head scope resources).map change
  | .support action source =>
    exact (source.familyRequestsOriginal head scope resources).codeAction henv hscoped hTarget (.support (relevant := relevant) action)
  | .focusMinimal source _ bound =>
    exact SortableFamilyProfileRequests.refine bound (source.familyRequestsOriginal head scope resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.familyRequestsOriginal head scope resources _ member
termination_by sizeOf certificate

theorem SortableObs.familyRequestsOriginal
    {expression : VExpr}
    (observation : SortableObs env U registry target locals σ expression profile footprint)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available) :
    SortableFamilyProfileRequests env U registry target locals σ available name levels expression.getAppFnArgs.2 profile := by
  match observation with
  | .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, packet⟩ := VExpr.const.inj head
    cases sameName
    rw [origin.constant] at found
    cases Option.some.inj found
    cases packet
    intro atom member
    obtain ⟨consumed, _⟩ := tree.initialConsumption origin headers seedWF seedLength equivalent
      signature typeClosed member
    exact consumed.requests henv hscoped hTarget closed
  | .legacy observation =>
    exact observation.familyRequestsSortable origin henv hscoped headers shape notDefinition notNative
      hTarget closed fits head scope resources
  | .code _ certificate => exact certificate.familyRequestsOriginal head scope resources
  | .lam .. => simp only [getAppFnArgs_lam] at head; cases head
  | .app fn arg inputs admitted =>
    intro atom member
    cases List.mem_singleton.mp member
    simp only [getAppFnArgs_app] at head ⊢
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    obtain ⟨prior, ⟨original⟩⟩ := fn.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope.1 first (List.mem_singleton_self _) True.intro
    obtain ⟨next, _⟩ := prior.appOriginal henv hscoped origin.sourceBelow hTarget original
      arg second (arg.live henv hscoped hTarget
        (fits.leavesLive henv hscoped hTarget second (arg.scoped scope.2))) inputs admitted
    exact next.requests henv hscoped hTarget closed
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyRequestsOriginal head scope (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyRequestsOriginal head scope (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.familyRequestsOriginal head scope resources _ (List.mem_singleton_self _)).view change
  | .action source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.familyRequestsOriginal head scope resources _ (List.mem_singleton_self _)).action henv hscoped hTarget change
  | .pad source => exact SortableFamilyProfileRequests.pad (source.familyRequestsOriginal head scope resources)
  | .unpad source =>
    intro atom member
    exact source.familyRequestsOriginal head scope resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial
termination_by sizeOf observation
end

end Lean4Lean.AnchoredSource.Adapted
