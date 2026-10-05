import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredDomainChain
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiRebind

/-! Actual source provenance of a finite Pi row. Domain alignment retains
its concrete finite edges; it does not merge unrelated type supports. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure PiRowCertificate (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (key : Key n) (result : Profile n) where
  domainSupport : Profile n
  domainFootprint : Footprint
  domain : CodeCert env U registry target locals σ A domainSupport domainFootprint
  domainAvailable : domainFootprint.Available available
  inputTyped : key.input.HasType domainSupport
  alignment : DomainChain env U registry target key.input key.domain (A.subst σ)
  anchor : Admitted env U registry target key key.anchor key.anchor
  bodyFootprint : Footprint
  body : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor)
    B result bodyFootprint
  packed : Profile n
  outside : Footprint
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms
  outsideAvailable : outside.Available available

def PiAtomOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .sort _ => False
  | _ + 1, .fn _ _ => False
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => False
  | _ + 1, .pi _ _ _ rows =>
      ∀ key result, (key, result) ∈ rows →
        Nonempty (PiRowCertificate env U registry target locals σ available A B key result)
  | _ + 1, .pad atom => PiAtomOrigins env U registry target locals σ available A B atom

def PiProfileOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, PiAtomOrigins env U registry target locals σ available A B atom

private theorem PiAtomOrigins.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : PiAtomOrigins env U registry target locals σ available A B a) :
    PiAtomOrigins env U registry target locals σ available A B b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact PiAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem PiRows.rowCertificate
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (rows : PiRows env U registry target locals σ A B ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (PiRowCertificate env U registry target locals σ available A B key result) := by
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
theorem Obs.piOrigins
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    PiProfileOrigins env U registry target locals σ available A B profile := by
  match observation with
  | .empty => exact fun _ member => nomatch member
  | .pi domain guard bodies =>
    intro atom member
    cases List.mem_singleton.mp member
    intro key result row
    exact bodies.rowCertificate domain
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) row
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOrigins (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOrigins (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piOrigins resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact source.piOrigins resources old ho
  | .unpad source =>
    intro atom member
    exact source.piOrigins resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piOrigins resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

noncomputable def CodeCert.map_profile_view
    (certificate : CodeCert env U registry target locals σ A support footprint)
    (change : ProfileView env U registry target input output) :
    CodeCert env U registry target locals σ A (change.mapType support)
      (List.replicate (input.length + 1) footprint).flatten := by
  match input, output, change with
  | _, _, .nil => simpa [ProfileView.mapType] using certificate
  | _, _, .cons head tail =>
    simpa only [ProfileView.mapType, List.length_cons, List.replicate_succ,
      List.flatten_cons] using CodeCert.union (.map head certificate) (certificate.map_profile_view tail)
termination_by sizeOf change

private theorem repeated_available {footprint : Footprint} (resources : footprint.Available available) (count : Nat) :
    Footprint.Available (List.replicate count footprint).flatten available := by
  intro index need member
  obtain ⟨part, hp, hn⟩ := List.mem_flatten.mp member
  have he := List.eq_of_mem_replicate hp
  subst part
  exact resources index need hn

noncomputable def PiRowCertificate.map_output
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (change : AtomView env U registry target old new) :
    PiRowCertificate env U registry target locals σ available A B key (change.mapType result) :=
  { row with body := .map change row.body }

noncomputable def PiRowCertificate.domainRekey
    (henv : env.Ordered)
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (path : TypeConversion env U target key.domain newDomain)
    (typed : key.input.HasType support) (formed : support.HasType (.sort true))
    (related : TypeRelated env U registry target key.domain newDomain support) :
    PiRowCertificate env U registry target locals σ available A B (domainKey key newDomain) result :=
  { row with alignment := .step path.symm typed formed (related.symm henv typed.wf_type) row.alignment
             anchor := row.anchor.rekey henv path typed formed related }

theorem PiRowCertificate.input_view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (PiRowCertificate env U registry target locals σ available A B (inputKey key input) result) := by
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

noncomputable def PiRowCertificate.pad
    (henv : env.Ordered)
    (row : PiRowCertificate env U registry target locals σ available A B (key : Key n) result) :
    PiRowCertificate env U registry target locals σ available A B key.pad result.pad where
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

theorem PiRowCertificate.unpad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : PiRowCertificate env U registry target locals σ available A B (key : Key n).pad result)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (PiRowCertificate env U registry target locals σ available A B key result.down) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  have resources : Footprint.Available [(0, ⟨n, key.input⟩)]
      (Valuation.push (rowInputNeeds key.input) available) := by
    intro i need hm
    cases List.mem_singleton.mp hm
    exact List.mem_append_left _ List.mem_cons_self
  obtain ⟨bodyFootprint, outside, packed, ⟨body⟩, pack, covered, outsideAvailable⟩ :=
    (CodeCert.down row.body).rebind_local henv hscoped hTarget
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

/-- Reanchoring uses the actual original codomain child at the paired source
substitutions. No new interpretation of a derived typing proof is requested. -/
theorem PiRowCertificate.reanchor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {σ : Subst} {available : Valuation} {anchor : VExpr}
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalBody : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (row : PiRowCertificate env U registry target locals σ available A B (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (PiRowCertificate env U registry target locals σ available A B
      (reanchorKey key anchor) result) := by
  have domainChild : GradedTransfer env U registry target locals σ σ available A A (.sort domainLevel) := (originalDomain target locals σ σ available closed hTarget substitutions fits).1
  obtain ⟨domainCode⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    domainChild row.domainAvailable
  have atA : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := atA
  have arguments := Related.retag henv row.inputTyped domainCode.related first
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need hm => (row.pack.atomized_localNeeds need hm).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need hm atom ha => row.covered atom ((row.pack.atomized_localNeeds need hm).2 atom ha)
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: source) :=
    .cons substitutions formedA raw
  have bodyFits := fits.pushCertificates henv hTarget row.domain row.domain
    row.domainAvailable row.domainAvailable row.inputTyped row.inputTyped arguments
    (arguments.symm henv) needs bounded covered
  have bodyChild : GradedTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons anchor) (Valuation.push needs available) B B (.sort bodyLevel) := (originalBody target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons anchor) (Valuation.push needs available) (Valuation.push_atomized_closed closed _)
    hTarget paired bodyFits).1
  obtain ⟨changed⟩ := row.body.transfer_graded henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) bodyChild
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  obtain ⟨packed, outside, pack, coverage, resources⟩ :=
    Footprint.pack_available changed.available bounded covered
  exact ⟨{
    domainSupport := row.domainSupport
    domainFootprint := row.domainFootprint
    domain := row.domain
    domainAvailable := row.domainAvailable
    inputTyped := row.inputTyped
    alignment := row.alignment
    anchor := admitted.reset_anchor
    bodyFootprint := changed.footprint
    body := changed.certificate
    packed := packed
    outside := outside
    pack := pack
    covered := coverage
    outsideAvailable := resources }⟩

private theorem PiProfileOrigins.pad
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile n)) :
    PiProfileOrigins env U registry target locals σ available A B profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem PiProfileOrigins.down
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile (n + 1))) :
    PiProfileOrigins env U registry target locals σ available A B profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

/-- Hereditary focusing retains the original row and its domain alignment.
Only the selected codomain support changes, using its finite Minimal child. -/
private theorem PiProfileOrigins.focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {profile}, focused ≤ profile →
      PiProfileOrigins env U registry target locals σ available A B profile →
      PiProfileOrigins env U registry target locals σ available A B focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {profile}, focused ≤ profile →
        PiProfileOrigins env U registry target locals σ available A B profile →
        PiProfileOrigins env U registry target locals σ available A B focused) with
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
    obtain ⟨row⟩ := origins _ present key oldResult oldMember
    exact ⟨{ row with body := .focusMinimal row.body outputMinimal resultBound }⟩
  | pad lower ih bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

private theorem PiProfileOrigins.rankShift
    (henv : env.Ordered)
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile (n + 1))) :
    PiProfileOrigins env U registry target locals σ available A B profile.rankShift := by
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
    obtain ⟨row⟩ := origin oldKey oldOutput hm
    exact ⟨row.pad henv⟩

section
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
  {A B : VExpr} {domainLevel bodyLevel : VLevel}
  (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
  (closed : available.AtomClosed)
  (formedA : env.HasType U source A (.sort domainLevel))
  (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
  (substitutions : Ctx.SubstEq env U target σ σ source)
  (fits : PairedFits env U registry source target locals σ σ available)
  (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
  (originalBody : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
  (reanchorRow : ∀ {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
    PiRowCertificate env U registry target locals σ available A B key result →
    Admitted env U registry target key anchor anchor →
    Nonempty (PiRowCertificate env U registry target locals σ available A B
      (reanchorKey key anchor) result))

include henv hscoped hTarget formedA formedB substitutions fits in
private theorem PiRowCertificate.externalLive
    (row : PiRowCertificate env U registry target locals σ available A B key result) :
    Footprint.Live env U registry target row.outside := by
  have scope := IsDefEq.closedN henv formedB
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  exact fits.forward.leavesLive henv hscoped hTarget row.outsideAvailable
    (row.pack.scoped (row.body.scoped scope))

include henv hscoped hTarget closed formedA formedB substitutions fits in
private theorem PiProfileOrigins.unshift
    (key : Key n)
    (origins : PiProfileOrigins env U registry target locals σ available A B (profile : Profile (n + 2))) :
    PiProfileOrigins env U registry target locals σ available A B (profile.unshift key) := by
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
    obtain ⟨row⟩ := origin key.pad oldResult oldMember
    exact row.unpad henv hscoped hTarget closed
      (row.externalLive henv hscoped hTarget formedA formedB substitutions fits)

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem PiProfileOrigins.mapWith
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : PiProfileOrigins env U registry target locals σ available A B profile) :
    PiProfileOrigins env U registry target locals σ available A B (change.mapType profile) := by
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
      · obtain ⟨row⟩ := origin _ result hm
        exact reanchorRow row admitted
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
        · obtain ⟨row⟩ := origin _ result hm
          exact ⟨row.domainRekey henv path typed formed related⟩
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
        · obtain ⟨row⟩ := origin _ result hm
          exact row.input_view henv hscoped hTarget closed forward backward
            (row.externalLive henv hscoped hTarget formedA formedB substitutions fits)
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
      · obtain ⟨row⟩ := origin _ oldResult hm
        exact ⟨row.map_output child⟩
  | _ + 1, _, _, .pad child =>
    exact (PiProfileOrigins.mapWith child origins.down).pad
  | _, _, _, .trans first second =>
    exact PiProfileOrigins.mapWith second (PiProfileOrigins.mapWith first origins)
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem CodeCert.piOriginsWith
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    PiProfileOrigins env U registry target locals σ available A B profile := by
  match certificate with
  | .seed observation _ => exact observation.piOrigins resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsWith (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsWith (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsWith resources).pad
  | .familyPad source =>
    exact False.elim (source.piOriginsWith resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsWith resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsWith resources).down
  | .map change source =>
    exact PiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change (source.piOriginsWith resources)
  | .focusMinimal source minimal bound =>
    exact PiProfileOrigins.focusMinimal minimal bound (source.piOriginsWith resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsWith resources _ member
termination_by sizeOf certificate

include henv hscoped hTarget closed formedA formedB substitutions fits originalDomain originalBody in
/-- Compatibility interface for callers already carrying unrestricted joints.
Original-tail callers instead use `piOriginsWith` and construct each frame. -/
theorem CodeCert.piOrigins
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    PiProfileOrigins env U registry target locals σ available A B profile :=
  certificate.piOriginsWith henv hscoped hTarget closed formedA formedB substitutions fits
    (fun row admitted => row.reanchor henv hscoped hTarget closed formedA substitutions fits
      originalDomain originalBody admitted) resources

include henv hscoped hTarget closed formedA formedB substitutions fits originalDomain originalBody in
/-- The selected function cover yields actual source domain and codomain
certificates at its exact key. Its alignment is a finite chain of supported
raw type paths, so domain rekeying need not invent a common guard support. -/
theorem CodeCert.piRow
    {profile : Profile (n + 1)}
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available)
    (typed : (Profile.fn (key : Key n) output).HasType profile) :
    ∃ result, Nonempty (PiRowCertificate env U registry target locals σ available A B key result) ∧
      (Profile.singleton output).HasType result := by
  obtain ⟨protoDomain, protoBody, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have origins := certificate.piOrigins henv hscoped hTarget closed formedA formedB
    substitutions fits originalDomain originalBody resources
  exact ⟨result, origins _ member key result row, resultTyped⟩

end

end Lean4Lean.AnchoredSource.Adapted
