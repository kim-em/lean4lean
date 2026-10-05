import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePiRowExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiRowCertificate
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiRebind
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

/-! Pi row provenance in the full endpoint-indexed formation grammar. Every
row retains the exposed Pi's actual original domain and codomain occurrences;
local input adaptation is concrete identity-source replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private repeated_available from Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
set_option backward.isDefEq.respectTransparency false


def RichPiAtomOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .sort _ => False
  | _ + 1, .fn _ _ => False
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => False
  | _ + 1, .pi _ _ _ rows =>
      ∀ key result, (key, result) ∈ rows →
        ∃ relevant, Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result)
  | _ + 1, .pad atom => RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode atom

def RichPiProfileOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode atom


variable {domainNode : EndpointState sourceEnv U source A (.sort u)}
  {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}

noncomputable def PiRowCertificate.toRich
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (formed : result.HasType (.sort relevant)) :
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result where
  domainSupport := row.domainSupport
  domainFootprint := row.domainFootprint
  domain := .legacy (.ofCode row.domain row.domain.formed)
  domainAvailable := row.domainAvailable
  inputTyped := row.inputTyped
  alignment := row.alignment
  anchor := row.anchor
  bodyFootprint := row.bodyFootprint
  body := .legacy (.ofCode row.body formed)
  packed := row.packed
  outside := row.outside
  pack := row.pack
  covered := row.covered
  outsideAvailable := row.outsideAvailable

noncomputable def RichPiRowCertificate.atFlag
    (row : RichPiRowCertificate env U registry target locals σ available oldRelevant domainNode bodyNode key result)
    (formed : result.HasType (.sort relevant)) :
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result :=
  { row with body := .observe (.code row.body) formed }

private theorem PiProfileOrigins.toRich
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile n)) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile := by
  induction n with
  | zero => exact origins
  | succ n ih =>
    intro atom member
    have origin := origins atom member
    cases atom with
    | sort | fn | family | ctor | record => exact origin
    | pi protoDomain protoBody support rows =>
      intro key result selected
      obtain ⟨row⟩ := origin key result selected
      exact ⟨true, ⟨PiRowCertificate.toRich row row.body.formed⟩⟩
    | pad atom =>
      exact ih (profile := .singleton atom) (fun other selected => by
        cases List.mem_singleton.mp selected
        exact origin) atom (List.mem_singleton_self _)

private theorem RichPiAtomOrigins.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode a) :
    RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact RichPiAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem RichRows.rowCertificate
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨{ domainSupport := ambient
               domainFootprint := domainFootprint
               domain := domain
               domainAvailable := domainAvailable
               inputTyped := guard.inputTyped
               alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
               anchor := guard.anchor
               bodyFootprint := _
               body := body
               packed := _
               outside := _
               pack := pack
               covered := covered
               outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) }⟩
    · exact tail.rowCertificate domain domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

noncomputable def RichCert.map_profile_view {support input output : Profile n}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant support footprint)
    (change : ProfileView env U registry target input output) :
    RichCert sourceEnv env U registry target node locals σ relevant (change.mapType support)
      (List.replicate (input.length + 1) footprint).flatten := by
  match input, output, change with
  | _, _, .nil => simpa [ProfileView.mapType] using certificate
  | _, _, .cons head tail =>
    simpa only [ProfileView.mapType, List.length_cons, List.replicate_succ,
      List.flatten_cons] using RichCert.union (.map head certificate) (certificate.map_profile_view tail)
termination_by sizeOf change

noncomputable def RichPiRowCertificate.map_output
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result)
    (change : AtomView env U registry target old new) :
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key (change.mapType result) :=
  { row with body := .map change row.body }

noncomputable def RichPiRowCertificate.domainRekey
    (henv : env.Ordered)
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result)
    (path : TypeConversion env U target key.domain newDomain)
    (typed : key.input.HasType support) (formed : support.HasType (.sort true))
    (related : TypeRelated env U registry target key.domain newDomain support) :
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (domainKey key newDomain) result :=
  { row with alignment := .step path.symm typed formed (related.symm henv typed.wf_type) row.alignment
             anchor := row.anchor.rekey henv path typed formed related }

theorem RichPiRowCertificate.input_view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input)
 :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (inputKey key input) result) := by
  obtain ⟨bodyFootprint, outside, packed, ⟨body⟩, pack, covered, outsideAvailable⟩ :=
    row.body.rebind_local
      (variableProfileView forward (Locals.push locals) (σ.cons key.anchor))
      (variableProfileView_available input available) row.pack row.covered
      row.outsideAvailable closed
  exact ⟨{
    domainSupport := backward.mapType row.domainSupport
    domainFootprint := _
    domain := row.domain.map_profile_view backward
    domainAvailable := repeated_available row.domainAvailable _
    inputTyped := backward.mapType_typed row.inputTyped
    alignment := row.alignment.mapInput henv hscoped backward
    anchor := (AdapterSeed.view .same backward).admission henv hscoped hTarget row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable }⟩

noncomputable def RichPiRowCertificate.pad
    (henv : env.Ordered)
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (key : Key n) result) :
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key.pad result.pad where
  domainSupport := row.domainSupport.pad
  domainFootprint := row.domainFootprint
  domain := .pad row.domain
  domainAvailable := row.domainAvailable
  inputTyped := row.inputTyped.pad
  alignment := row.alignment.pad henv
  anchor := Admitted.pad henv row.anchor
  bodyFootprint := row.bodyFootprint
  body := .pad row.body
  packed := row.packed.pad
  outside := row.outside
  pack := by
    simpa only [raiseProfile_step (Nat.le_refl n), raiseProfile_self] using row.pack.raise (Nat.le_succ n)
  covered := by
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨old, row.covered old ho, rfl⟩
  outsideAvailable := row.outsideAvailable

theorem RichPiRowCertificate.unpad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode (key : Key n).pad result)
 :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result.down) := by
  have resources : Footprint.Available [(0, ⟨n, key.input⟩)]
      (Valuation.push (rowInputNeeds key.input) available) := by
    intro i need hm
    cases List.mem_singleton.mp hm
    exact List.mem_append_left _ List.mem_cons_self
  obtain ⟨bodyFootprint, outside, packed, ⟨body⟩, pack, covered, outsideAvailable⟩ :=
    (RichCert.down row.body).rebind_local
      (Obs.pad (.var (Locals.push locals) (σ.cons key.anchor) 0 key.input))
      resources row.pack row.covered row.outsideAvailable closed
  exact ⟨{
    domainSupport := row.domainSupport.down
    domainFootprint := row.domainFootprint
    domain := .down row.domain
    domainAvailable := row.domainAvailable
    inputTyped := row.inputTyped.pad_inv
    alignment := row.alignment.unpad henv
    anchor := Admitted.unpad henv hTarget row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable }⟩


theorem RichPiRowCertificate.codeAction
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result)
    (action : SortableCodeAction env U registry target relevant result next output) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available next domainNode bodyNode key output) := by
  have resources := row.pack.available_atomized_localNeeds row.outsideAvailable
  obtain ⟨footprint, ⟨body⟩, resources⟩ := row.body.codeAction action resources
  obtain ⟨packed, outside, pack, covered, resources⟩ := Footprint.pack_available resources
    (fun need member => (row.pack.atomized_localNeeds need member).1)
    (fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present))
  exact ⟨{ row with
               bodyFootprint := footprint
               body := body
               packed := packed
               outside := outside
               pack := pack
               covered := covered
               outsideAvailable := resources }⟩

private theorem RichPiProfileOrigins.pad
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (profile : Profile n)) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem RichPiProfileOrigins.down
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (profile : Profile (n + 1))) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

/-- Hereditary focusing retains the original row and its domain alignment.
Only the selected codomain support changes, using its finite Minimal child. -/
private theorem RichPiProfileOrigins.focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {profile}, focused ≤ profile →
      RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile →
      RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {profile}, focused ≤ profile →
        RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile →
        RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode focused) with
  | nil => exact fun _ _ _ member => nomatch member
  | cons first tail ihFirst ihTail =>
    intro profile bound origins atom member
    rcases List.mem_append.mp member with member | member
    · exact ihFirst (Profile.le_trans (Profile.le_union_left _ _) bound) origins atom member
    · exact ihTail (Profile.le_trans (Profile.le_union_right _ _) bound) origins atom member
  | @sort n atom relevant typed profile bound origins =>
    intro _ _
    cases n with
    | zero => exact False.elim (origins _ (Profile.sort_le_mem_zero bound))
    | succ n => exact False.elim (origins _ (Profile.sort_le_mem bound))
  | @family n value data typed profile bound origins =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨other, present, covered⟩ := bound _ (List.mem_singleton_self _)
    cases other <;> try contradiction
    exact False.elim (origins _ present)
  | @fn n domain result protoDomain protoBody key output inputMinimal outputMinimal formed _ _ profile bound origins =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨oldDomain, oldRows, present, _, rowsCovered⟩ :=
      Profile.pi_le_inv bound (List.mem_singleton_self _)
    intro selectedKey selectedResult selected
    cases List.mem_singleton.mp selected
    obtain ⟨oldResult, oldMember, resultBound⟩ := rowsCovered key result (List.mem_singleton_self _)
    obtain ⟨relevant, ⟨row⟩⟩ := origins _ present key oldResult oldMember
    exact ⟨relevant, row.codeAction (.focusMinimal outputMinimal resultBound)⟩
  | pad lower ih bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

private theorem RichPiProfileOrigins.not_sort
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

private theorem RichPiProfileOrigins.rankShift
    (henv : env.Ordered)
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (profile : Profile (n + 1))) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile.rankShift := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => exact origin
  | pi protoDomain protoBody domain rows =>
    intro key output member
    obtain ⟨⟨oldKey, oldOutput⟩, hm, he⟩ := List.mem_map.mp member
    cases he
    obtain ⟨relevant, ⟨row⟩⟩ := origin oldKey oldOutput hm
    exact ⟨relevant, ⟨row.pad henv⟩⟩

section
variable
  (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
  (closed : available.AtomClosed)
  (reanchorRow : ∀ {relevant : Bool} {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result →
    Admitted env U registry target key anchor anchor →
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
      (reanchorKey key anchor) result))

include henv hscoped hTarget closed in
private theorem RichPiProfileOrigins.unshift
    (key : Key n)
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (profile : Profile (n + 2))) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (profile.unshift key) := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi protoDomain protoBody domain rows =>
    cases List.mem_singleton.mp member
    intro other result member
    obtain ⟨same, oldResult, oldMember, rfl⟩ := Rows.mem_unshift.mp member
    subst other
    obtain ⟨relevant, ⟨row⟩⟩ := origin key.pad oldResult oldMember
    exact ⟨relevant, row.unpad henv hscoped hTarget closed⟩

include henv hscoped hTarget closed reanchorRow in
private theorem RichPiProfileOrigins.mapWith
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (change.mapType profile) := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origins
  | _ + 1, _, _, .reanchor admitted =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi protoDomain protoBody domain rows =>
      intro key result member
      rcases mem_reanchorRows.mp member with hm | ⟨rfl, hm⟩
      · exact origin key result hm
      · obtain ⟨relevant, ⟨row⟩⟩ := origin _ result hm
        exact ⟨relevant, reanchorRow row admitted⟩
  | _ + 1, _, _, .domainRekey path typed formed related =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi protoDomain protoBody domain rows =>
      simp only [domainRekeyAtom]
      split
      · intro key result member
        rcases mem_reanchorRows.mp member with hm | ⟨rfl, hm⟩
        · exact origin key result hm
        · obtain ⟨relevant, ⟨row⟩⟩ := origin _ result hm
          exact ⟨relevant, ⟨row.domainRekey henv path typed formed related⟩⟩
      · exact origin
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi protoDomain protoBody domain rows =>
      simp only [AtomView.mapType, inputTypes] at *
      split
      · intro key result member
        rcases mem_reanchorRows.mp member with hm | ⟨rfl, hm⟩
        · exact origin key result hm
        · obtain ⟨relevant, ⟨row⟩⟩ := origin _ result hm
          exact ⟨relevant, row.input_view henv hscoped hTarget closed forward backward⟩
      · exact origin
  | _ + 2, _, _, .commutePadFn _ _ =>
    exact origins.down.rankShift henv
  | _ + 2, _, _, .uncommutePadFn key _ =>
    exact (origins.unshift henv hscoped hTarget closed key).pad
  | _ + 1, _, _, .fn _ child =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi protoDomain protoBody domain rows =>
      intro key result member
      rcases mem_outputRows.mp member with hm | ⟨rfl, oldResult, hm, rfl⟩
      · exact origin key result hm
      · obtain ⟨relevant, ⟨row⟩⟩ := origin _ oldResult hm
        exact ⟨relevant, ⟨row.map_output child⟩⟩
  | _ + 1, _, _, .pad child =>
    exact (RichPiProfileOrigins.mapWith child origins.down).pad
  | _, _, _, .trans first second =>
    exact RichPiProfileOrigins.mapWith second (RichPiProfileOrigins.mapWith first origins)
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem RichPiProfileOrigins.sortFlags_nil
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

include henv hscoped hTarget closed reanchorRow in
private theorem RichPiProfileOrigins.supportWith
    (action : SupportAction env U registry target n)
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact RichPiProfileOrigins.mapWith henv hscoped hTarget closed
      reanchorRow change origins
  | output wanted child ih =>
    intro atom member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have origin := origins old oldMember
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi protoDomain protoBody domain rows =>
      intro key result member
      rcases mem_outputRows.mp member with old | ⟨rfl, oldResult, old, rfl⟩
      · exact origin key result old
      · obtain ⟨relevant, ⟨row⟩⟩ := origin _ oldResult old
        exact ⟨relevant, ⟨{ row with body := .support child row.body }⟩⟩
  | pad child ih => exact (ih origins.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)

include henv hscoped hTarget closed reanchorRow in
private theorem RichPiProfileOrigins.codeActionWith
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode nextProfile := by
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
    exact RichPiProfileOrigins.mapWith henv hscoped hTarget closed
      reanchorRow change origins
  | support action =>
    exact RichPiProfileOrigins.supportWith henv hscoped hTarget closed
      reanchorRow action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact RichPiProfileOrigins.focusMinimal minimal bound origins

include henv hscoped hTarget closed reanchorRow in
private theorem RichPiAtomOrigins.actionWith {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode a) :
    RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact RichPiProfileOrigins.codeActionWith henv hscoped hTarget closed
      reanchorRow action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)


theorem SortableRows.richRowCertificate
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (rows : SortableRows env U registry target locals σ A B relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨{ domainSupport := ambient
               domainFootprint := domainFootprint
               domain := .legacy domain
               domainAvailable := domainAvailable
               inputTyped := guard.inputTyped
               alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
               anchor := guard.anchor
               bodyFootprint := _
               body := .legacy body
               packed := _
               outside := _
               pack := pack
               covered := covered
               outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm) }⟩
    · exact SortableRows.richRowCertificate domain tail domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
termination_by sizeOf rows

include henv hscoped hTarget closed reanchorRow in
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem _root_.Lean4Lean.AnchoredSource.Adapted.CodeCert.piOriginsRichWith
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match certificate with
  | .seed observation _ => exact PiProfileOrigins.toRich (observation.piOrigins resources)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsRichWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsRichWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsRichWith resources).pad
  | .familyPad source =>
    exact False.elim (source.piOriginsRichWith resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsRichWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsRichWith resources).down
  | .map change source =>
    exact RichPiProfileOrigins.mapWith henv hscoped hTarget closed
      reanchorRow change (source.piOriginsRichWith resources)
  | .focusMinimal source minimal bound =>
    exact RichPiProfileOrigins.focusMinimal minimal bound (source.piOriginsRichWith resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsRichWith resources _ member
termination_by sizeOf certificate

include henv hscoped hTarget closed reanchorRow
mutual
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.piOriginsRichWith
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match certificate with
  | .seed observation _ => exact PiProfileOrigins.toRich (observation.piOrigins resources)
  | .observe observation _ => exact observation.piOriginsRichWith resources
  | .ofCode source _ =>
    exact source.piOriginsRichWith henv hscoped hTarget closed
      reanchorRow resources
  | .pi domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    intro key result selected
    exact ⟨_, SortableRows.richRowCertificate domain rows
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) selected⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsRichWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsRichWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsRichWith resources).pad
  | .sortPad source =>
    exact False.elim (RichPiProfileOrigins.not_sort (source.piOriginsRichWith resources))
  | .familyPad source =>
    exact False.elim (source.piOriginsRichWith resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsRichWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsRichWith resources).down
  | .support action source =>
    exact RichPiProfileOrigins.supportWith henv hscoped hTarget closed
      reanchorRow action (source.piOriginsRichWith resources)
  | .map change source =>
    exact RichPiProfileOrigins.mapWith henv hscoped hTarget closed
      reanchorRow change (source.piOriginsRichWith resources)
  | .focusMinimal source minimal bound =>
    exact RichPiProfileOrigins.focusMinimal minimal bound (source.piOriginsRichWith resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsRichWith resources _ member
termination_by sizeOf certificate

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableObs.piOriginsRichWith
    (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match observation with
  | .legacy source => exact PiProfileOrigins.toRich (source.piOrigins resources)
  | .code _ source => exact source.piOriginsRichWith resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsRichWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsRichWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .action source action =>
    intro atom member
    cases List.mem_singleton.mp member
    exact RichPiAtomOrigins.actionWith henv hscoped hTarget closed
      reanchorRow action (source.piOriginsRichWith resources _ (List.mem_singleton_self _))
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piOriginsRichWith resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact source.piOriginsRichWith resources old ho
  | .unpad source =>
    intro atom member
    exact source.piOriginsRichWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piOriginsRichWith resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
end

omit henv hscoped hTarget closed reanchorRow in
/-- Strip an actual prefix from a longer route to a structural endpoint.
No source equality or fresh typing endpoint is constructed. -/
theorem PrefixRoute.structuralSuffix
    {first : EndpointState sourceEnv U source expression assigned}
    {middle : EndpointState sourceEnv U source expression intermediate}
    {last : EndpointState sourceEnv U source expression natural}
    (prior : PrefixRoute sourceEnv U source expression first middle)
    (route : PrefixRoute sourceEnv U source expression first last)
    (head : OriginalEndpointFactor.EndpointState.Structural last) :
    Nonempty (PrefixRoute sourceEnv U source expression middle last) := by
  induction prior with
  | done => exact ⟨route⟩
  | expose reference rest ih =>
    cases route with
    | done => cases head
    | expose _ other => exact ih other
  | convert plan term rest ih =>
    cases route with
    | done => cases head
    | convert _ _ other => exact ih other

omit henv hscoped hTarget closed reanchorRow in
private theorem RichRows.rowCertificateAt
    {actualDomain : EndpointState sourceEnv U source A (.sort actualU)}
    {actualBody : EndpointState sourceEnv U (A :: source) B (.sort actualV)}
    (actualHu : actualU.WF U) (actualHv : actualV.WF U) (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B)
      (.pi actualHu actualHv actualDomain actualBody) (.pi hu hv domainNode bodyNode))
    (domain : RichCert sourceEnv env U registry target actualDomain locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target actualDomain actualBody locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) := by
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
  exact rows.rowCertificate domain domainAvailable resources member

/-- A native guard or an unopened charged code leaf. The latter is not
misrepresented as a syntactically aligned native Pi row. -/
inductive RichPiLeaf (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) :
    {n : Nat} → Atom n → Type where
  | native (origin : RichPiAtomOrigins env U registry target locals σ available domainNode bodyNode atom) :
      RichPiLeaf env U registry target locals σ available domainNode bodyNode atom
  | recipe
      (code : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.singleton atom) footprint)
      (resources : footprint.Available available) :
      RichPiLeaf env U registry target locals σ available domainNode bodyNode atom

structure RichPiDeferredOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (atom : Atom n) where
  rank : Nat
  original : Atom rank
  leaf : RichPiLeaf env U registry target locals σ available domainNode bodyNode original
  path : GeneralOutputPath env U registry target original atom

def RichPiDeferredOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms,
    Nonempty (RichPiDeferredOrigin env U registry target locals σ available domainNode bodyNode atom)

omit henv hscoped hTarget closed reanchorRow in
private theorem RichPiDeferredOrigins.code
    (change : SortableCodeAction env U registry target relevant p next q)
    (typed : p.HasType (.sort relevant))
    (origins : RichPiDeferredOrigins env U registry target locals σ available domainNode bodyNode p) :
    RichPiDeferredOrigins env U registry target locals σ available domainNode bodyNode q := by
  intro atom member
  obtain ⟨old, present, ⟨step⟩⟩ := change.atom member
  obtain ⟨origin⟩ := origins old present
  exact ⟨{ origin with path := .code origin.path step (typed.singleton_of_mem present) }⟩

include henv hscoped hTarget closed reanchorRow
mutual
/-- Exhaustive static extraction retains charged leaves and their exact
finite output operations. It does not assert guards for unopened recipes. -/
theorem RichCert.piOriginsWith
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available) :
    RichPiDeferredOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match certificate with
  | .legacy source =>
    intro atom member
    exact ⟨⟨_, atom, .native (SortableCert.piOriginsRichWith henv hscoped hTarget closed reanchorRow source resources atom member), .refl⟩⟩
  | .recipe code =>
    intro atom member
    exact ⟨⟨_, atom, .recipe (.action (.select member) code) resources, .refl⟩⟩
  | .observe observation _ => exact observation.piOriginsWith hu hv route resources
  | .pi actualHu actualHv domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨⟨_, _, .native ?_, .refl⟩⟩
    intro key result selected
    exact ⟨_, rows.rowCertificateAt actualHu actualHv hu hv route domain
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) selected⟩
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.piOriginsWith hu hv suffix resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsWith hu hv route (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsWith hu hv route (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact RichPiDeferredOrigins.code .pad source.formed (source.piOriginsWith hu hv route resources)
  | .down source =>
    exact RichPiDeferredOrigins.code .down source.formed (source.piOriginsWith hu hv route resources)
  | .support action source =>
    exact RichPiDeferredOrigins.code (.support action) source.formed (source.piOriginsWith hu hv route resources)
  | .map change source =>
    exact RichPiDeferredOrigins.code (.map change) source.formed (source.piOriginsWith hu hv route resources)
  | .select source member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact source.piOriginsWith hu hv route resources _ member
termination_by sizeOf certificate

theorem RichObs.piOriginsWith
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available) :
    RichPiDeferredOrigins env U registry target locals σ available domainNode bodyNode profile := by
  match observation with
  | .legacy source =>
    intro atom member
    exact ⟨⟨_, atom, .native (SortableObs.piOriginsRichWith henv hscoped hTarget closed reanchorRow source resources atom member), .refl⟩⟩
  | .code source => exact source.piOriginsWith hu hv route resources
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.piOriginsWith hu hv suffix resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsWith hu hv route (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsWith hu hv route (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .action source action =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := source.piOriginsWith hu hv route resources _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path action }⟩
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := source.piOriginsWith hu hv route resources _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .select source member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact source.piOriginsWith hu hv route resources _ member
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := source.piOriginsWith hu hv route resources old ho
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad source =>
    intro atom member
    obtain ⟨origin⟩ := source.piOriginsWith hu hv route resources (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
termination_by sizeOf observation
end

include henv hscoped hTarget closed reanchorRow in
/-- Resolve a requested deferred row using the actual interpreted Pi and
actual caller admission. Every code action remains under its original charge. -/
 theorem RichPiDeferredOrigin.resolve
    (origin : RichPiDeferredOrigin env U registry target locals σ available domainNode bodyNode (n := n + 1)
      (.pi prototypeDomain prototypeBody (support : Profile n) rows))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      (.forallE C D) (Profile.pi prototypeDomain prototypeBody support rows))
    (sorted : (Profile.pi prototypeDomain prototypeBody support rows).HasType (.sort relevant))
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) := by
  obtain ⟨flag, inputSorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv origin.path sorted
  cases origin.leaf with
  | native native =>
    have origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode
        (.singleton origin.original) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact native
    have next := RichPiProfileOrigins.codeActionWith henv hscoped hTarget closed reanchorRow action origins
    obtain ⟨oldFlag, ⟨row⟩⟩ := next _ (List.mem_singleton_self _) key result selected
    exact ⟨row.atFlag ((Profile.HasType.pi_iff.mp sorted).2 key result selected)⟩
  | recipe code resources =>
    let next := RichCodeRecipe.action action (RichCodeRecipe.action (.retag inputSorted) code)
    obtain ⟨row, _, _⟩ := next.requestedRow henv hscoped hTarget whole rfl selected admitted resources
    exact ⟨row⟩


include henv hscoped hTarget closed reanchorRow in
 theorem RichCert.piRowOfDeferredOrigins
    {n : Nat} {profile : Profile (n + 1)} {support : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (origins : RichPiDeferredOrigins env U registry target locals σ available domainNode bodyNode profile)
    (piMember : (.pi protoDomain protoBody support rows) ∈ profile.atoms)
    (rowMember : (key, result) ∈ rows)
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ) (.forallE C D) profile)
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) := by
  obtain ⟨origin⟩ := origins _ piMember
  exact origin.resolve henv hscoped hTarget closed reanchorRow
    ((SortableCodeAction.select (relevant := relevant) piMember).codeMap henv hscoped whole)
    (certificate.formed.singleton_of_mem piMember) rowMember admitted

end

/-- A selected row keeps the parent query's exact sort flag. -/
theorem RichCert.piRowOfOrigins
    {n : Nat} {profile : Profile (n + 1)} {support : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (origins : RichPiProfileOrigins env U registry target locals σ available domainNode bodyNode profile)
    (piMember : (.pi protoDomain protoBody support rows) ∈ profile.atoms)
    (rowMember : (key, result) ∈ rows) :
    Nonempty (RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) := by
  obtain ⟨oldRelevant, ⟨row⟩⟩ := origins _ piMember key result rowMember
  have formation := (Profile.HasType.pi_iff.mp (certificate.formed.singleton_of_mem piMember)).2 key result rowMember
  exact ⟨row.atFlag formation⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
