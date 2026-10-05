import Lean4Lean.Theory.Typing.AnchoredOriginalSortableContract
import Lean4Lean.Theory.Typing.AnchoredSortablePiRebind
import Lean4Lean.Theory.Typing.AnchoredSortableScope
import Lean4Lean.Theory.Typing.AnchoredOriginalPiReanchor

/-! Exact source Pi rows for either formation flag. Domains and codomain rows retain their hereditary sortable certificates. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private repeated_available from Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
set_option backward.isDefEq.respectTransparency false

structure SortablePiRowCertificate (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (A B : VExpr) (key : Key n) (result : Profile n) where
  domainSupport : Profile n
  domainFootprint : Footprint
  domain : SortableCert env U registry target locals σ A true domainSupport domainFootprint
  domainAvailable : domainFootprint.Available available
  inputTyped : key.input.HasType domainSupport
  alignment : DomainChain env U registry target key.input key.domain (A.subst σ)
  anchor : Admitted env U registry target key key.anchor key.anchor
  bodyFootprint : Footprint
  body : SortableCert env U registry target (Locals.push locals) (σ.cons key.anchor)
    B relevant result bodyFootprint
  packed : Profile n
  outside : Footprint
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms
  outsideAvailable : outside.Available available

def SortablePiAtomOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .sort _ => False
  | _ + 1, .fn _ _ => False
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => False
  | _ + 1, .pi _ _ _ rows =>
      ∀ key result, (key, result) ∈ rows →
        ∃ relevant, Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B key result)
  | _ + 1, .pad atom => SortablePiAtomOrigins env U registry target locals σ available A B atom

def SortablePiProfileOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, SortablePiAtomOrigins env U registry target locals σ available A B atom

noncomputable def PiRowCertificate.toSortable
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (formed : result.HasType (.sort relevant)) :
    SortablePiRowCertificate env U registry target locals σ available relevant A B key result where
  domainSupport := row.domainSupport
  domainFootprint := row.domainFootprint
  domain := .ofCode row.domain row.domain.formed
  domainAvailable := row.domainAvailable
  inputTyped := row.inputTyped
  alignment := row.alignment
  anchor := row.anchor
  bodyFootprint := row.bodyFootprint
  body := .ofCode row.body formed
  packed := row.packed
  outside := row.outside
  pack := row.pack
  covered := row.covered
  outsideAvailable := row.outsideAvailable

noncomputable def SortablePiRowCertificate.atFlag
    (row : SortablePiRowCertificate env U registry target locals σ available oldRelevant A B key result)
    (formed : result.HasType (.sort relevant)) :
    SortablePiRowCertificate env U registry target locals σ available relevant A B key result :=
  { row with body := .observe (.code oldRelevant row.body) formed }

private theorem PiProfileOrigins.toSortable
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile n)) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile := by
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
      exact ⟨true, ⟨row.toSortable row.body.formed⟩⟩
    | pad atom =>
      exact ih (profile := .singleton atom) (fun other selected => by
        cases List.mem_singleton.mp selected
        exact origin) atom (List.mem_singleton_self _)

private theorem SortablePiAtomOrigins.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : SortablePiAtomOrigins env U registry target locals σ available A B a) :
    SortablePiAtomOrigins env U registry target locals σ available A B b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact SortablePiAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem SortableRows.rowCertificate
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (rows : SortableRows env U registry target locals σ A B relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B key result) := by
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

/-- A literal source Pi observation supplies rows from its actual constructor.
Value views cannot invent a Pi atom; all nontrivial function views are excluded
by the source observation's recursively retained Pi origin. -/
noncomputable def SortableCert.map_profile_view {support input output : Profile n}
    (certificate : SortableCert env U registry target locals σ A relevant support footprint)
    (change : ProfileView env U registry target input output) :
    SortableCert env U registry target locals σ A relevant (change.mapType support)
      (List.replicate (input.length + 1) footprint).flatten := by
  match input, output, change with
  | _, _, .nil => simpa [ProfileView.mapType] using certificate
  | _, _, .cons head tail =>
    simpa only [ProfileView.mapType, List.length_cons, List.replicate_succ,
      List.flatten_cons] using SortableCert.union (.map head certificate) (certificate.map_profile_view tail)
termination_by sizeOf change

noncomputable def SortablePiRowCertificate.map_output
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B key result)
    (change : AtomView env U registry target old new) :
    SortablePiRowCertificate env U registry target locals σ available relevant A B key (change.mapType result) :=
  { row with body := .map change row.body }

noncomputable def SortablePiRowCertificate.domainRekey
    (henv : env.Ordered)
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B key result)
    (path : TypeConversion env U target key.domain newDomain)
    (typed : key.input.HasType support) (formed : support.HasType (.sort true))
    (related : TypeRelated env U registry target key.domain newDomain support) :
    SortablePiRowCertificate env U registry target locals σ available relevant A B (domainKey key newDomain) result :=
  { row with alignment := .step path.symm typed formed (related.symm henv typed.wf_type) row.alignment
             anchor := row.anchor.rekey henv path typed formed related }

theorem SortablePiRowCertificate.input_view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B key result)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B (inputKey key input) result) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨bodyFootprint, outside, packed, ⟨body⟩, pack, covered, outsideAvailable⟩ :=
    row.body.rebind_local henv hscoped hTarget
      (variableProfileView forward (Locals.push locals) (σ.cons key.anchor))
      (variableProfileView_available input available) live row.pack row.covered
      row.outsideAvailable externalLive closed
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

noncomputable def SortablePiRowCertificate.pad
    (henv : env.Ordered)
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B (key : Key n) result) :
    SortablePiRowCertificate env U registry target locals σ available relevant A B key.pad result.pad where
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

theorem SortablePiRowCertificate.unpad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B (key : Key n).pad result)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B key result.down) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  have resources : Footprint.Available [(0, ⟨n, key.input⟩)]
      (Valuation.push (rowInputNeeds key.input) available) := by
    intro i need hm
    cases List.mem_singleton.mp hm
    exact List.mem_append_left _ List.mem_cons_self
  obtain ⟨bodyFootprint, outside, packed, ⟨body⟩, pack, covered, outsideAvailable⟩ :=
    (SortableCert.down row.body).rebind_local henv hscoped hTarget
      (Obs.pad (.var (Locals.push locals) (σ.cons key.anchor) 0 key.input))
      resources live row.pack row.covered row.outsideAvailable externalLive closed
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

private theorem SortablePiProfileOrigins.pad
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B (profile : Profile n)) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem SortablePiProfileOrigins.down
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B (profile : Profile (n + 1))) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

/-- Hereditary focusing retains the original row and its domain alignment.
Only the selected codomain support changes, using its finite Minimal child. -/
private theorem SortablePiProfileOrigins.focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {profile}, focused ≤ profile →
      SortablePiProfileOrigins env U registry target locals σ available A B profile →
      SortablePiProfileOrigins env U registry target locals σ available A B focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {profile}, focused ≤ profile →
        SortablePiProfileOrigins env U registry target locals σ available A B profile →
        SortablePiProfileOrigins env U registry target locals σ available A B focused) with
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
    exact ⟨relevant, ⟨{ row with body := .focusMinimal row.body outputMinimal resultBound }⟩⟩
  | pad lower ih bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

private theorem SortablePiProfileOrigins.not_sort
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

private theorem SortablePiProfileOrigins.rankShift
    (henv : env.Ordered)
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B (profile : Profile (n + 1))) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile.rankShift := by
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

theorem OriginalTail.SortableTailFits.leavesLive
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (tail : SortableTailFits sourceEnv env U registry target source locals σ τ available)
    (resources : footprint.Available available)
    (bounded : Footprint.Scoped source.length footprint) :
    Footprint.Live env U registry target footprint := by
  intro index need member
  obtain ⟨sourceType, lookup⟩ := Lookup.ofLt (bounded index need member)
  obtain ⟨entry⟩ := tail.lookup henv hTarget (resources index need member) lookup
  exact Related.live henv hscoped hTarget entry.related

section
variable {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
  {A B : VExpr} {domainLevel bodyLevel : VLevel}
  (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
  (closed : available.AtomClosed)
  (formedA : env.HasType U source A (.sort domainLevel))
  (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
  (substitutions : Ctx.SubstEq env U target σ σ source)
  (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
  (reanchorRow : ∀ {relevant : Bool} {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
    SortablePiRowCertificate env U registry target locals σ available relevant A B key result →
    Admitted env U registry target key anchor anchor →
    Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B
      (reanchorKey key anchor) result))

include henv hscoped hTarget formedA formedB substitutions fits in
private theorem SortablePiRowCertificate.externalLive
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B key result) :
    Footprint.Live env U registry target row.outside := by
  have scope := IsDefEq.closedN henv formedB
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  exact fits.leavesLive henv hscoped hTarget row.outsideAvailable
    (row.pack.scoped (row.body.scoped scope))

include henv hscoped hTarget closed formedA formedB substitutions fits in
private theorem SortablePiProfileOrigins.unshift
    (key : Key n)
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B (profile : Profile (n + 2))) :
    SortablePiProfileOrigins env U registry target locals σ available A B (profile.unshift key) := by
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
    exact ⟨relevant, row.unpad henv hscoped hTarget closed
      (row.externalLive henv hscoped hTarget formedA formedB substitutions fits)⟩

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem SortablePiProfileOrigins.mapWith
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B profile) :
    SortablePiProfileOrigins env U registry target locals σ available A B (change.mapType profile) := by
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
          exact ⟨relevant, row.input_view henv hscoped hTarget closed forward backward
            (row.externalLive henv hscoped hTarget formedA formedB substitutions fits)⟩
      · exact origin
  | _ + 2, _, _, .commutePadFn _ _ =>
    exact origins.down.rankShift henv
  | _ + 2, _, _, .uncommutePadFn key _ =>
    exact (origins.unshift henv hscoped hTarget closed formedA formedB substitutions fits key).pad
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
    exact (SortablePiProfileOrigins.mapWith child origins.down).pad
  | _, _, _, .trans first second =>
    exact SortablePiProfileOrigins.mapWith second (SortablePiProfileOrigins.mapWith first origins)
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem SortablePiProfileOrigins.sortFlags_nil
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem SortablePiProfileOrigins.supportWith
    (action : SupportAction env U registry target n)
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B profile) :
    SortablePiProfileOrigins env U registry target locals σ available A B (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact SortablePiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
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

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem SortablePiProfileOrigins.codeActionWith
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B profile) :
    SortablePiProfileOrigins env U registry target locals σ available A B nextProfile := by
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
    exact SortablePiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change origins
  | support action =>
    exact SortablePiProfileOrigins.supportWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact SortablePiProfileOrigins.focusMinimal minimal bound origins

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem SortablePiAtomOrigins.actionWith {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : SortablePiAtomOrigins env U registry target locals σ available A B a) :
    SortablePiAtomOrigins env U registry target locals σ available A B b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : SortablePiProfileOrigins env U registry target locals σ available A B
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact SortablePiProfileOrigins.codeActionWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem CodeCert.piOriginsSortableWith
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile := by
  match certificate with
  | .seed observation _ => exact (observation.piOrigins resources).toSortable
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsSortableWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsSortableWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsSortableWith resources).pad
  | .familyPad source =>
    exact False.elim (source.piOriginsSortableWith resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsSortableWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsSortableWith resources).down
  | .map change source =>
    exact SortablePiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change (source.piOriginsSortableWith resources)
  | .focusMinimal source minimal bound =>
    exact SortablePiProfileOrigins.focusMinimal minimal bound (source.piOriginsSortableWith resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsSortableWith resources _ member
termination_by sizeOf certificate

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow
mutual
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem SortableCert.piOriginsWith
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile := by
  match certificate with
  | .seed observation _ => exact (observation.piOrigins resources).toSortable
  | .observe observation _ => exact observation.piOriginsWith resources
  | .ofCode source _ =>
    exact source.piOriginsSortableWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow resources
  | .pi domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    intro key result selected
    exact ⟨_, rows.rowCertificate domain
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) selected⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsWith resources).pad
  | .sortPad source =>
    exact False.elim (SortablePiProfileOrigins.not_sort (source.piOriginsWith resources))
  | .familyPad source =>
    exact False.elim (source.piOriginsWith resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsWith resources).down
  | .support action source =>
    exact SortablePiProfileOrigins.supportWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action (source.piOriginsWith resources)
  | .map change source =>
    exact SortablePiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change (source.piOriginsWith resources)
  | .focusMinimal source minimal bound =>
    exact SortablePiProfileOrigins.focusMinimal minimal bound (source.piOriginsWith resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsWith resources _ member
termination_by sizeOf certificate

theorem SortableObs.piOriginsWith
    (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile := by
  match observation with
  | .legacy source => exact (source.piOrigins resources).toSortable
  | .code _ source => exact source.piOriginsWith resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .action source action =>
    intro atom member
    cases List.mem_singleton.mp member
    exact SortablePiAtomOrigins.actionWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action (source.piOriginsWith resources _ (List.mem_singleton_self _))
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piOriginsWith resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact source.piOriginsWith resources old ho
  | .unpad source =>
    intro atom member
    exact source.piOriginsWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piOriginsWith resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
end
end

/-- Reanchor a retained Pi row using just its original domain and body
formation occurrences. Both context entries keep hereditary source certificates. -/
theorem SortablePiRowCertificate.reanchorOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B anchor : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (row : SortablePiRowCertificate env U registry target locals σ available relevant A B (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B
      (reanchorKey key anchor) result) := by
  let frame := SortableTailPairedFits.diagonal context tail
  obtain ⟨domainCode⟩ := domainIH target locals σ σ available closed hTarget substitutions frame
    row.domain row.domainAvailable
  have atA : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := atA
  have arguments := Related.retag henv row.inputTyped domainCode.related first
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom
      ((row.pack.atomized_localNeeds need member).2 atom present)
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: source) :=
    .cons substitutions (originalDomain.sound.defeq.mono hle) raw
  let bodyFrame := frame.pushCertificates originalDomain row.domain row.domain
    row.domainAvailable row.domainAvailable row.inputTyped row.inputTyped arguments
    (arguments.symm henv) needs bounded covered
  obtain ⟨changed⟩ := bodyIH target (Locals.push locals) (σ.cons key.anchor) (σ.cons anchor)
    (Valuation.push needs available) (Valuation.push_atomized_closed closed _)
    hTarget paired bodyFrame row.body
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  obtain ⟨packed, outside, pack, coverage, resources⟩ :=
    Footprint.pack_available changed.available bounded covered
  exact ⟨{ row with
    anchor := admitted.reset_anchor
    bodyFootprint := changed.footprint
    body := changed.certificate
    packed := packed
    outside := outside
    pack := pack
    covered := coverage
    outsideAvailable := resources }⟩

/-- Every Pi row in a hereditary formation query comes from its finite source
syntax, with reanchoring discharged by the two fixed original formation children. -/
theorem SortableCert.piOriginsOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available) :
    SortablePiProfileOrigins env U registry target locals σ available A B profile :=
  certificate.piOriginsWith henv hscoped hTarget closed
    (originalDomain.sound.defeq.mono hle) (originalBody.sound.defeq.mono hle)
    substitutions tail
    (fun row admitted => row.reanchorOriginal henv hle hTarget closed
      context originalDomain originalBody substitutions tail domainIH bodyIH admitted) resources

/-- Selecting a concrete row retains the requested formation flag. The flag
change uses the parent certificate's intrinsic row formation, not downward closure. -/
theorem SortableCert.piRowOfOrigins
    {n : Nat} {profile : Profile (n + 1)} {support : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (origins : SortablePiProfileOrigins env U registry target locals σ available A B profile)
    (piMember : (.pi protoDomain protoBody support rows) ∈ profile.atoms)
    (rowMember : (key, result) ∈ rows) :
    Nonempty (SortablePiRowCertificate env U registry target locals σ available relevant A B key result) := by
  obtain ⟨oldRelevant, ⟨row⟩⟩ := origins _ piMember key result rowMember
  have formation := (Profile.HasType.pi_iff.mp (certificate.formed.singleton_of_mem piMember)).2
    key result rowMember
  exact ⟨row.atFlag formation⟩

end Lean4Lean.AnchoredSource.Adapted
