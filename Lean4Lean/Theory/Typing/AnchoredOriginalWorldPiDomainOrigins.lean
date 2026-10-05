import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiDomainExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! Pi-domain extraction retains one actual domain certificate together with
its original query sites and uniform bounds for every head policy. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

structure WorldPiDomainBudget (strata : EquationStratification env) where
  worlds : List (World strata.rules.length)
  depth : (Name → Nat → Nat) → Nat

structure ControlledRichDomainCertificate (env : VEnv) {strata : EquationStratification env}
    (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {source : List VExpr} {A : VExpr} {u : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (locals : List Nat) (σ : Subst) (available : Valuation) (support : Profile n)
    extends RichDomainCertificate env U registry target domainNode locals σ available support where
  annotation : WorldCertProvenance strata certificate
  worlds_subset : annotation.worlds ⊆ budget.worlds
  depth_le : ∀ policy, certificate.headDepth policy ≤ budget.depth policy

variable {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
  {domainNode : EndpointState sourceEnv U source A (.sort u)}

namespace ControlledRichDomainCertificate

def pad (value : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support) :
    ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support.pad :=
  ⟨⟨_, .pad value.certificate, value.resources⟩, .pad value.annotation, value.worlds_subset, by intro policy; simpa only [RichCert.headDepth] using value.depth_le policy⟩

def down (value : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available
      (support : Profile (n+1))) :
    ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support.down :=
  ⟨⟨_, .down value.certificate, value.resources⟩, .down value.annotation, value.worlds_subset, by intro policy; simpa only [RichCert.headDepth] using value.depth_le policy⟩

def map (value : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support)
    (change : AtomView env U registry target a b) :
    ControlledRichDomainCertificate env budget U registry target domainNode locals σ available (change.mapType support) :=
  ⟨⟨_, .map change value.certificate, value.resources⟩, .map change value.annotation, value.worlds_subset, by intro policy; simpa only [RichCert.headDepth] using value.depth_le policy⟩

def union (first : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available left)
    (second : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available right) :
    ControlledRichDomainCertificate env budget U registry target domainNode locals σ available (left.union right) := by
  refine ⟨⟨_, .union first.certificate second.certificate, ?_⟩,
    .union first.annotation second.annotation, ?_, ?_⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (first.resources i need) (second.resources i need)
  · intro world member
    exact (List.mem_append.mp member).elim (fun h => first.worlds_subset h) (fun h => second.worlds_subset h)
  · intro policy
    simpa only [RichCert.headDepth] using Nat.max_le.mpr ⟨first.depth_le policy, second.depth_le policy⟩

def empty : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available
    (Profile.empty : Profile n) := by
  refine ⟨⟨[], .legacy (.seed .empty (.empty (.sort true))), ?_⟩,
    .legacy _ (.seed _ _ .empty), ?_, ?_⟩
  · intro _ _ member; cases member
  · intro _ member; cases member
  · intro policy
    simp only [RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
    exact Nat.zero_le _

theorem codeAction (value : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support)
    (action : SortableCodeAction env U registry target true support true output) :
    Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available output) := by
  obtain ⟨fp, certificate, annotation, resources, worlds, depth⟩ :=
    value.certificate.codeAction_worlds_depth value.annotation action value.resources
  exact ⟨⟨⟨fp, certificate, resources⟩, annotation,
    fun _ member => value.worlds_subset (worlds member),
    fun policy => Nat.le_trans (depth policy) (value.depth_le policy)⟩⟩

def mono (value : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support)
    {next : WorldPiDomainBudget strata} (worlds : budget.worlds ⊆ next.worlds)
    (depth : ∀ policy, budget.depth policy ≤ next.depth policy) :
    ControlledRichDomainCertificate env next U registry target domainNode locals σ available support :=
  { value with worlds_subset := fun _ member => worlds (value.worlds_subset member)
               depth_le := fun policy => Nat.le_trans (value.depth_le policy) (depth policy) }
end ControlledRichDomainCertificate
def WorldPiDomainAtomOrigins (env : VEnv) {strata : EquationStratification env} (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A : VExpr} {u : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u)) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi _ _ domain _ =>
      Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available domain)
  | _ + 1, .pad atom => WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode atom
  | _ + 1, _ => False

def WorldPiDomainOrigins (env : VEnv) {strata : EquationStratification env} (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A : VExpr} {u : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode atom

theorem WorldPiDomainAtomOrigins.view {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origin : WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode a) :
    WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact WorldPiDomainAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem WorldPiDomainOrigins.pad
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile.pad := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  exact origins old hm

theorem WorldPiDomainOrigins.down
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode (profile : Profile (n + 1))) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile.down := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

theorem WorldPiDomainOrigins.rankShift
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode (profile : Profile (n + 1))) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile.rankShift := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => exact origin
  | pi protoA protoB domain rows =>
    obtain ⟨result⟩ := origin
    exact ⟨result.pad⟩

theorem WorldPiDomainOrigins.unshift
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode (profile : Profile (n + 2)))
    (key : Key n) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode (profile.unshift key) := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi protoA protoB domain rows =>
    cases List.mem_singleton.mp member
    obtain ⟨result⟩ := origin
    exact ⟨result.down⟩

theorem ControlledRichDomainCertificate.mapProfile
    (result : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support)
    (change : ProfileView env U registry target input output) :
    Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available (change.mapType support)) := by
  match change with
  | .nil => exact ⟨result⟩
  | .cons head tail =>
    obtain ⟨next⟩ := result.mapProfile tail
    exact ⟨(result.map head).union next⟩
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem ControlledRichDomainCertificate.unions (profiles : List (Profile n))
    (certificates : ∀ profile ∈ profiles,
      Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available profile)) :
    Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available (Profile.unions profiles)) := by
  induction profiles with
  | nil => exact ⟨ControlledRichDomainCertificate.empty⟩
  | cons profile profiles ih =>
    obtain ⟨first⟩ := certificates profile List.mem_cons_self
    obtain ⟨rest⟩ := ih (fun other member => certificates other (List.mem_cons_of_mem _ member))
    exact ⟨first.union rest⟩

theorem ControlledRichDomainCertificate.inputDomain
    (result : ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support)
    (backward : ProfileView env U registry target input output) :
    Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available
      (inputDomain input backward.mapType support)) := by
  obtain ⟨extra⟩ := ControlledRichDomainCertificate.unions ((Basis input support).map backward.mapType) (by
    intro profile member
    obtain ⟨focused, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨focus⟩ := result.codeAction
      (.focusMinimal (Basis.minimal selected) (Basis.valid selected).2)
    exact focus.mapProfile backward)
  exact ⟨result.union extra⟩

theorem WorldPiDomainOrigins.map {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode (change.mapType profile) := by
  classical
  match n, a, b, change with
  | _, _, _, .refl _ => exact origins
  | _ + 1, _, _, .reanchor _ =>
    intro atom member
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
    have origin := origins old hm
    cases old <;> exact origin
  | _ + 1, _, _, .domainRekey _ _ _ _ =>
    intro atom member
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
    have origin := origins old hm
    cases old <;> exact origin
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
    have origin := origins old hm
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi protoA protoB domain rows =>
      change WorldPiDomainAtomOrigins _ budget _ _ _ _ _ _ _ (if _ then _ else _)
      split
      · obtain ⟨result⟩ := origin
        exact result.inputDomain backward
      · exact origin
  | _ + 2, _, _, .commutePadFn _ _ => exact origins.down.rankShift
  | _ + 2, _, _, .uncommutePadFn key _ => exact (origins.unshift key).pad
  | _ + 1, _, _, .fn _ _ =>
    intro atom member
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
    have origin := origins old hm
    cases old <;> exact origin
  | _ + 1, _, _, .pad child => exact (origins.down.map child).pad
  | _, _, _, .trans first second => exact (origins.map first).map second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem WorldPiDomainOrigins.focusMinimal
    {value focused : Profile n} (minimal : Minimal value focused)
    {bound : Profile n} (dominated : focused ≤ bound)
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode bound) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ support _ => ∀ {bound}, support ≤ bound →
        WorldPiDomainOrigins env budget U registry target locals σ available domainNode bound →
        WorldPiDomainOrigins env budget U registry target locals σ available domainNode support) with
  | nil => exact fun _ member => nomatch member
  | cons first tail ihfirst ihtail =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact ihfirst (Profile.le_trans (Profile.le_union_left _ _) dominated) origins atom member
    · exact ihtail (Profile.le_trans (Profile.le_union_right _ _) dominated) origins atom member
  | @sort n atom relevant typed =>
    rename_i bound dominated origins
    cases n with
    | zero => exact False.elim (origins _ (Profile.sort_le_mem_zero dominated))
    | succ n => exact False.elim (origins _ (Profile.sort_le_mem dominated))
  | family typed =>
    rename_i bound dominated origins
    exact False.elim (origins _ (Profile.family_le_mem dominated))
  | @fn n domain result protoA protoB key output hi ho formed ihinput ihoutput =>
    rename_i bound dominated origins
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨oldDomain, oldRows, selected, domainBound, _⟩ :=
      Profile.pi_le_inv dominated (List.mem_singleton_self _)
    obtain ⟨source⟩ := origins _ selected
    exact source.codeAction (.focusMinimal hi domainBound)
  | pad lower ih =>
    rename_i bound dominated origins
    apply WorldPiDomainOrigins.pad
    apply ih (bound := bound.down)
    · simpa only [Profile.down_pad] using dominated.down
    · exact origins.down

theorem WorldPiDomainOrigins.sortFlags_nil
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

theorem WorldPiDomainOrigins.support
    (action : SupportAction env U registry target n)
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact WorldPiDomainOrigins.map change origins
  | output wanted child ih =>
    intro atom member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have origin := origins old oldMember
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi protoDomain protoBody domain rows => exact origin
  | pad child ih => exact (ih origins.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)

theorem WorldPiDomainOrigins.not_sort
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

theorem WorldPiDomainOrigins.codeAction
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode nextProfile := by
  induction action with
  | id | retag => exact origins
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)
  | pad => exact origins.pad
  | down => exact origins.down
  | unpad =>
    intro atom member
    exact origins (.pad atom) (List.mem_map_of_mem member)
  | sortPad => exact False.elim origins.not_sort
  | familyPad => exact False.elim (origins _ (List.mem_singleton_self _))
  | map change =>
    exact WorldPiDomainOrigins.map change origins
  | support action =>
    exact WorldPiDomainOrigins.support action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact WorldPiDomainOrigins.focusMinimal minimal bound origins

theorem WorldPiDomainAtomOrigins.action {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode a) :
    WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact WorldPiDomainOrigins.codeAction action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)



theorem WorldPiDomainOrigins.lowerRaised
    {n N : Nat} {profile : Profile n} (bound : n ≤ N)
    (origins : WorldPiDomainOrigins env budget U registry target locals σ available domainNode
      (raiseProfile N bound profile)) :
    WorldPiDomainOrigins env budget U registry target locals σ available domainNode profile := by
  induction N with
  | zero =>
    have same : n = 0 := by omega
    subst n
    exact origins
  | succ N ih =>
    by_cases same : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using origins
    · have previous : n ≤ N := by omega
      apply ih previous
      rw [raiseProfile_step previous] at origins
      simpa only [Profile.down_pad] using origins.down


theorem WorldPiDomainAtomOrigins.outputPath
    (path : GeneralOutputPath env U registry target old atom)
    (origin : WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode old) :
    WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode atom := by
  induction path with
  | refl => exact origin
  | action path change ih => exact ih.action change
  | code path change formed ih =>
    exact WorldPiDomainOrigins.codeAction change
      (fun atom member => by cases List.mem_singleton.mp member; exact ih)
      _ (List.mem_singleton_self _)
  | pad path ih => exact ih
  | unpad path ih => exact ih

/-- A native guard or an unopened charged code leaf. The latter is not
misrepresented as a syntactically aligned native Pi row. -/
inductive WorldPiDomainLeaf (env : VEnv) {strata : EquationStratification env} (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) :
    {n : Nat} → Atom n → Type where
  | native (origin : WorldPiDomainAtomOrigins env budget U registry target locals σ available domainNode atom) :
      WorldPiDomainLeaf env budget U registry target locals σ available domainNode bodyNode atom
  | recipe
      (code : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.singleton atom) footprint)
      (resources : footprint.Available available)
      (annotation : WorldCodeRecipeProvenance strata code)
      (worlds : annotation.worlds ⊆ budget.worlds)
      (depth : ∀ policy, code.headDepth policy ≤ budget.depth policy) :
      WorldPiDomainLeaf env budget U registry target locals σ available domainNode bodyNode atom

structure WorldPiDomainDeferredOrigin (env : VEnv) {strata : EquationStratification env} (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (atom : Atom n) where
  rank : Nat
  original : Atom rank
  leaf : WorldPiDomainLeaf env budget U registry target locals σ available domainNode bodyNode original
  path : GeneralOutputPath env U registry target original atom

def WorldPiDomainDeferredOrigins (env : VEnv) {strata : EquationStratification env} (budget : WorldPiDomainBudget strata) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms,
    Nonempty (WorldPiDomainDeferredOrigin env budget U registry target locals σ available domainNode bodyNode atom)

theorem WorldPiDomainDeferredOrigins.code
    (change : SortableCodeAction env U registry target relevant p next q)
    (typed : p.HasType (.sort relevant))
    (origins : WorldPiDomainDeferredOrigins env budget U registry target locals σ available domainNode bodyNode p) :
    WorldPiDomainDeferredOrigins env budget U registry target locals σ available domainNode bodyNode q := by
  intro atom member
  obtain ⟨old, present, ⟨step⟩⟩ := change.atom member
  obtain ⟨origin⟩ := origins old present
  exact ⟨{ origin with path := .code origin.path step (typed.singleton_of_mem present) }⟩



theorem WorldPiDomainDeferredOrigin.resolve
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (origin : WorldPiDomainDeferredOrigin env budget U registry target locals σ available
      domainNode bodyNode (n := n + 1) (.pi prototypeDomain prototypeBody (support : Profile n) rows)) :
    Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available support) := by
  cases origin.leaf with
  | native native => exact WorldPiDomainAtomOrigins.outputPath origin.path native
  | recipe code resources annotation worlds depth =>
    let action := GeneralOutputPath.codeAtInput origin.path code.formed
    exact ⟨⟨⟨_, .recipe (.domain (.action action code)), resources⟩,
      .recipe (.domain (.action action annotation)), worlds, by
        intro policy
        simpa only [RichCert.headDepth, RichCodeRecipe.headDepth] using depth policy⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
