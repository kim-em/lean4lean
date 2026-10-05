import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction

/-! Exact native Pi domain provenance, including empty row tables. The
certificate retains the actual original domain node and the requested support. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure RichDomainCertificate
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {source : List VExpr} {A : VExpr} {u : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (locals : List Nat) (σ : Subst) (available : Valuation) (support : Profile n) where
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target domainNode locals σ true support footprint
  resources : footprint.Available available

variable {domainNode : EndpointState sourceEnv U source A (.sort u)}

def RichPiDomainAtomOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A : VExpr} {u : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u)) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi _ _ domain _ =>
      Nonempty (RichDomainCertificate env U registry target domainNode locals σ available domain)
  | _ + 1, .pad atom => RichPiDomainAtomOrigins env U registry target locals σ available domainNode atom
  | _ + 1, _ => False

def RichPiDomainOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A : VExpr} {u : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, RichPiDomainAtomOrigins env U registry target locals σ available domainNode atom

private theorem RichPiDomainAtomOrigins.view {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origin : RichPiDomainAtomOrigins env U registry target locals σ available domainNode a) :
    RichPiDomainAtomOrigins env U registry target locals σ available domainNode b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact RichPiDomainAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem RichPiDomainOrigins.pad
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode profile) :
    RichPiDomainOrigins env U registry target locals σ available domainNode profile.pad := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  exact origins old hm

private theorem RichPiDomainOrigins.down
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode (profile : Profile (n + 1))) :
    RichPiDomainOrigins env U registry target locals σ available domainNode profile.down := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem RichPiDomainOrigins.rankShift
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode (profile : Profile (n + 1))) :
    RichPiDomainOrigins env U registry target locals σ available domainNode profile.rankShift := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => exact origin
  | pi protoA protoB domain rows =>
    obtain ⟨result⟩ := origin
    exact ⟨⟨_, .pad result.certificate, result.resources⟩⟩

private theorem RichPiDomainOrigins.unshift
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode (profile : Profile (n + 2)))
    (key : Key n) :
    RichPiDomainOrigins env U registry target locals σ available domainNode (profile.unshift key) := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi protoA protoB domain rows =>
    cases List.mem_singleton.mp member
    obtain ⟨result⟩ := origin
    exact ⟨⟨_, .down result.certificate, result.resources⟩⟩

private theorem RichDomainCertificate.mapProfile
    (result : RichDomainCertificate env U registry target domainNode locals σ available support)
    (change : ProfileView env U registry target input output) :
    Nonempty (RichDomainCertificate env U registry target domainNode locals σ available (change.mapType support)) := by
  match change with
  | .nil => exact ⟨result⟩
  | .cons head tail =>
    obtain ⟨next⟩ := result.mapProfile tail
    exact ⟨⟨_, .union (.map head result.certificate) next.certificate, fun i need hm =>
      (List.mem_append.mp hm).elim (result.resources i need) (next.resources i need)⟩⟩
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem RichDomainCertificate.unions (profiles : List (Profile n))
    (certificates : ∀ profile ∈ profiles,
      Nonempty (RichDomainCertificate env U registry target domainNode locals σ available profile)) :
    Nonempty (RichDomainCertificate env U registry target domainNode locals σ available (Profile.unions profiles)) := by
  induction profiles with
  | nil => exact ⟨⟨[], .legacy (.seed .empty (.empty (Profile.WF.sort true))), by intro _ _ member; cases member⟩⟩
  | cons profile profiles ih =>
    obtain ⟨first⟩ := certificates profile List.mem_cons_self
    obtain ⟨rest⟩ := ih (fun other member => certificates other (List.mem_cons_of_mem _ member))
    exact ⟨⟨_, .union first.certificate rest.certificate, fun i need hm =>
      (List.mem_append.mp hm).elim (first.resources i need) (rest.resources i need)⟩⟩

private theorem RichDomainCertificate.inputDomain
    (result : RichDomainCertificate env U registry target domainNode locals σ available support)
    (backward : ProfileView env U registry target input output) :
    Nonempty (RichDomainCertificate env U registry target domainNode locals σ available
      (inputDomain input backward.mapType support)) := by
  obtain ⟨extra⟩ := RichDomainCertificate.unions ((Basis input support).map backward.mapType) (by
    intro profile member
    obtain ⟨focused, selected, rfl⟩ := List.mem_map.mp member
    obtain ⟨fp, ⟨focusedCode⟩, focusedResources⟩ := result.certificate.codeAction
      (.focusMinimal (Basis.minimal selected) (Basis.valid selected).2) result.resources
    let focus : RichDomainCertificate env U registry target domainNode locals σ available focused :=
      ⟨fp, focusedCode, focusedResources⟩
    exact focus.mapProfile backward)
  exact ⟨⟨_, .union result.certificate extra.certificate, fun i need hm =>
    (List.mem_append.mp hm).elim (result.resources i need) (extra.resources i need)⟩⟩

private theorem RichPiDomainOrigins.map {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode profile) :
    RichPiDomainOrigins env U registry target locals σ available domainNode (change.mapType profile) := by
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
      change RichPiDomainAtomOrigins _ _ _ _ _ _ _ _ (if _ then _ else _)
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

private theorem RichPiDomainOrigins.focusMinimal
    {value focused : Profile n} (minimal : Minimal value focused)
    {bound : Profile n} (dominated : focused ≤ bound)
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode bound) :
    RichPiDomainOrigins env U registry target locals σ available domainNode focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ support _ => ∀ {bound}, support ≤ bound →
        RichPiDomainOrigins env U registry target locals σ available domainNode bound →
        RichPiDomainOrigins env U registry target locals σ available domainNode support) with
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
    obtain ⟨fp, ⟨code⟩, available⟩ := source.certificate.codeAction (.focusMinimal hi domainBound) source.resources
    exact ⟨⟨fp, code, available⟩⟩
  | pad lower ih =>
    rename_i bound dominated origins
    apply RichPiDomainOrigins.pad
    apply ih (bound := bound.down)
    · simpa only [Profile.down_pad] using dominated.down
    · exact origins.down

private theorem RichPiDomainOrigins.sortFlags_nil
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

private theorem RichPiDomainOrigins.support
    (action : SupportAction env U registry target n)
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode profile) :
    RichPiDomainOrigins env U registry target locals σ available domainNode (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact RichPiDomainOrigins.map change origins
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

private theorem RichPiDomainOrigins.not_sort
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

private theorem RichPiDomainOrigins.codeAction
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : RichPiDomainOrigins env U registry target locals σ available domainNode profile) :
    RichPiDomainOrigins env U registry target locals σ available domainNode nextProfile := by
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
    exact RichPiDomainOrigins.map change origins
  | support action =>
    exact RichPiDomainOrigins.support action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact RichPiDomainOrigins.focusMinimal minimal bound origins

private theorem RichPiDomainAtomOrigins.action {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : RichPiDomainAtomOrigins env U registry target locals σ available domainNode a) :
    RichPiDomainAtomOrigins env U registry target locals σ available domainNode b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : RichPiDomainOrigins env U registry target locals σ available domainNode
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact RichPiDomainOrigins.codeAction action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)


private theorem PiDomainOrigins.toRich
    (origins : PiDomainOrigins env U registry target locals σ available A (profile : Profile n)) :
    RichPiDomainOrigins env U registry target locals σ available domainNode profile := by
  induction n with
  | zero => exact origins
  | succ n ih =>
    intro atom member
    have origin := origins atom member
    cases atom with
    | sort | fn | family | ctor | record => exact origin
    | pi protoA protoB support rows =>
      obtain ⟨result⟩ := origin
      exact ⟨⟨result.footprint, .legacy (.ofCode result.certificate result.certificate.formed), result.resources⟩⟩
    | pad atom =>
      exact ih (profile := .singleton atom) (fun other present => by
        cases List.mem_singleton.mp present
        exact origin) atom (List.mem_singleton_self _)

mutual
theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.piDomainOriginsRich
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available) :
    RichPiDomainOrigins env U registry target locals σ available domainNode profile := by
  match certificate with
  | .seed observation _ => exact PiDomainOrigins.toRich (observation.piDomainOrigins resources)
  | .observe observation _ => exact observation.piDomainOriginsRich resources
  | .ofCode source _ =>
    exact PiDomainOrigins.toRich (source.piDomainOrigins resources)
  | .pi domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .legacy domain,
      fun i need hm => resources i need (List.mem_append_left _ hm)⟩⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOriginsRich (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piDomainOriginsRich (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piDomainOriginsRich resources).pad
  | .sortPad source =>
    exact False.elim (RichPiDomainOrigins.not_sort (source.piDomainOriginsRich resources))
  | .familyPad source =>
    exact False.elim (source.piDomainOriginsRich resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piDomainOriginsRich resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piDomainOriginsRich resources).down
  | .support action source =>
    exact RichPiDomainOrigins.support action (source.piDomainOriginsRich resources)
  | .map change source =>
    exact RichPiDomainOrigins.map change (source.piDomainOriginsRich resources)
  | .focusMinimal source minimal bound =>
    exact RichPiDomainOrigins.focusMinimal minimal bound (source.piDomainOriginsRich resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piDomainOriginsRich resources _ member
termination_by sizeOf certificate

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableObs.piDomainOriginsRich
    (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    RichPiDomainOrigins env U registry target locals σ available domainNode profile := by
  match observation with
  | .legacy source => exact PiDomainOrigins.toRich (source.piDomainOrigins resources)
  | .code _ source => exact source.piDomainOriginsRich resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOriginsRich (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piDomainOriginsRich (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .action source action =>
    intro atom member
    cases List.mem_singleton.mp member
    exact RichPiDomainAtomOrigins.action action (source.piDomainOriginsRich resources _ (List.mem_singleton_self _))
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piDomainOriginsRich resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact source.piDomainOriginsRich resources old ho
  | .unpad source =>
    intro atom member
    exact source.piDomainOriginsRich resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piDomainOriginsRich resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
end

variable {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}

private theorem RichCert.domainCertificateAt
    {actualDomain : EndpointState sourceEnv U source A (.sort actualU)}
    {actualBody : EndpointState sourceEnv U (A :: source) B (.sort actualV)}
    (actualHu : actualU.WF U) (actualHv : actualV.WF U) (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B)
      (.pi actualHu actualHv actualDomain actualBody) (.pi hu hv domainNode bodyNode))
    (domain : RichCert sourceEnv env U registry target actualDomain locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target actualDomain actualBody locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    : Nonempty (RichDomainCertificate env U registry target domainNode locals σ available ambient) := by
  have equal := (PrefixRoute.done (.pi actualHu actualHv actualDomain actualBody)).structural_unique
    (by trivial) route (by trivial)
  obtain ⟨_, _, _, _, huEq, _, hvEq, domainEq, bodyEq⟩ :=
    EndpointState.pi.hinj rfl rfl rfl rfl equal.1 equal.2
  cases huEq
  cases hvEq
  have domainEq := eq_of_heq domainEq
  have bodyEq := eq_of_heq bodyEq
  cases domainEq
  cases bodyEq
  exact ⟨⟨_, domain, domainAvailable⟩⟩
private theorem RichPiDomainAtomOrigins.outputPath
    (path : GeneralOutputPath env U registry target old atom)
    (origin : RichPiDomainAtomOrigins env U registry target locals σ available domainNode old) :
    RichPiDomainAtomOrigins env U registry target locals σ available domainNode atom := by
  induction path with
  | refl => exact origin
  | action path change ih => exact ih.action change
  | code path change formed ih =>
    exact RichPiDomainOrigins.codeAction change
      (fun atom member => by cases List.mem_singleton.mp member; exact ih)
      _ (List.mem_singleton_self _)
  | pad path ih => exact ih
  | unpad path ih => exact ih

/-- A native guard or an unopened charged code leaf. The latter is not
misrepresented as a syntactically aligned native Pi row. -/
inductive RichPiDomainLeaf (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) :
    {n : Nat} → Atom n → Type where
  | native (origin : RichPiDomainAtomOrigins env U registry target locals σ available domainNode atom) :
      RichPiDomainLeaf env U registry target locals σ available domainNode bodyNode atom
  | recipe
      (code : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.singleton atom) footprint)
      (resources : footprint.Available available) :
      RichPiDomainLeaf env U registry target locals σ available domainNode bodyNode atom

structure RichPiDomainDeferredOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (atom : Atom n) where
  rank : Nat
  original : Atom rank
  leaf : RichPiDomainLeaf env U registry target locals σ available domainNode bodyNode original
  path : GeneralOutputPath env U registry target original atom

def RichPiDomainDeferredOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms,
    Nonempty (RichPiDomainDeferredOrigin env U registry target locals σ available domainNode bodyNode atom)

private theorem RichPiDomainDeferredOrigins.code
    (change : SortableCodeAction env U registry target relevant p next q)
    (typed : p.HasType (.sort relevant))
    (origins : RichPiDomainDeferredOrigins env U registry target locals σ available domainNode bodyNode p) :
    RichPiDomainDeferredOrigins env U registry target locals σ available domainNode bodyNode q := by
  intro atom member
  obtain ⟨old, present, ⟨step⟩⟩ := change.atom member
  obtain ⟨origin⟩ := origins old present
  exact ⟨{ origin with path := .code origin.path step (typed.singleton_of_mem present) }⟩

mutual
/-- Exhaustive static extraction retains charged leaves and their exact
finite output operations. It does not assert guards for unopened recipes. -/
theorem RichCert.piDomainOrigins
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available) :
    RichPiDomainDeferredOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match certificate with
  | .legacy source =>
    intro atom member
    exact ⟨⟨_, atom, .native (SortableCert.piDomainOriginsRich source resources atom member), .refl⟩⟩
  | .recipe code =>
    intro atom member
    exact ⟨⟨_, atom, .recipe (.action (.select member) code) resources, .refl⟩⟩
  | .observe observation _ => exact observation.piDomainOrigins hu hv route resources
  | .pi actualHu actualHv domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨⟨_, _, .native ?_, .refl⟩⟩
    exact RichCert.domainCertificateAt actualHu actualHv hu hv route domain rows
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.piDomainOrigins hu hv suffix resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins hu hv route (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piDomainOrigins hu hv route (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact RichPiDomainDeferredOrigins.code .pad source.formed (source.piDomainOrigins hu hv route resources)
  | .down source =>
    exact RichPiDomainDeferredOrigins.code .down source.formed (source.piDomainOrigins hu hv route resources)
  | .support action source =>
    exact RichPiDomainDeferredOrigins.code (.support action) source.formed (source.piDomainOrigins hu hv route resources)
  | .map change source =>
    exact RichPiDomainDeferredOrigins.code (.map change) source.formed (source.piDomainOrigins hu hv route resources)
  | .select source member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact source.piDomainOrigins hu hv route resources _ member
termination_by sizeOf certificate

theorem RichObs.piDomainOrigins
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available) :
    RichPiDomainDeferredOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match observation with
  | .legacy source =>
    intro atom member
    exact ⟨⟨_, atom, .native (SortableObs.piDomainOriginsRich source resources atom member), .refl⟩⟩
  | .code source => exact source.piDomainOrigins hu hv route resources
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.piDomainOrigins hu hv suffix resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins hu hv route (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piDomainOrigins hu hv route (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .action source action =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := source.piDomainOrigins hu hv route resources _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path action }⟩
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := source.piDomainOrigins hu hv route resources _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .select source member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact source.piDomainOrigins hu hv route resources _ member
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := source.piDomainOrigins hu hv route resources old ho
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad source =>
    intro atom member
    obtain ⟨origin⟩ := source.piDomainOrigins hu hv route resources (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
termination_by sizeOf observation
end


/-- Extract exactly the requested Pi domain, even when its row table is empty. -/
theorem RichCert.piDomain
    {support : Profile n} {rows : List (Key n × Profile n)}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.pi prototypeDomain prototypeBody support rows) footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available) :
    Nonempty (RichDomainCertificate env U registry target domainNode locals σ available support) :=
by
  obtain ⟨origin⟩ := certificate.piDomainOrigins hu hv route resources _ (List.mem_singleton_self _)
  cases origin.leaf with
  | native native =>
    exact RichPiDomainAtomOrigins.outputPath origin.path native
  | recipe code resources =>
    let selected := RichCodeRecipe.action (GeneralOutputPath.codeAtInput origin.path code.formed) code
    exact ⟨⟨_, .recipe (.domain selected), resources⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
