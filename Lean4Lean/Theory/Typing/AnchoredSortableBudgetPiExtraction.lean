import Lean4Lean.Theory.Typing.AnchoredSortablePiExtraction
import Lean4Lean.Theory.Typing.AnchoredSortableDepthPiRebind
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetJoint
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private repeated_available from Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

private theorem SortableCert.map_profile_view_allDepth
    {support : Profile n}
    (certificate : SortableCert env U registry target locals σ A relevant support footprint)
    (resources : footprint.Available available)
    (change : ProfileView env U registry target input output) :
    ∃ nextFootprint, ∃ result : SortableCert env U registry target locals σ A relevant (change.mapType support) nextFootprint,
      nextFootprint.Available available ∧ ∀ current, result.nativeDepth current ≤ certificate.nativeDepth current := by
  match change with
  | .nil => exact ⟨_, certificate, resources, fun _ => Nat.le_refl _⟩
  | .cons head tail =>
    obtain ⟨fp, last, lastAvailable, lastDepth⟩ := certificate.map_profile_view_allDepth resources tail
    exact ⟨_, .union (.map head certificate) last,
      (fun i need hm => (List.mem_append.mp hm).elim (resources i need) (lastAvailable i need)), by
        intro current
        simp only [SortableCert.nativeDepth]
        exact Nat.max_le.mpr ⟨Nat.le_refl _, lastDepth current⟩⟩
termination_by sizeOf change

private theorem variableProfileView_depth (current : Name → Bool)
    (view : ProfileView env U registry Γ input output) (locals : List Nat) (σ : Subst) :
    (variableProfileView view locals σ).nativeDepth current = 0 := by
  match view with
  | .nil => simp only [variableProfileView, Obs.nativeDepth]
  | .cons head tail => simp only [variableProfileView, Obs.nativeDepth, variableProfileView_depth current tail, Nat.max_self]
termination_by sizeOf view

structure BudgetPiRowCertificate (budgets : HereditaryBudgeted.Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (A B : VExpr) (key : Key n) (result : Profile n) extends SortablePiRowCertificate env U registry target locals σ available relevant A B key result where
  domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth
  bodyBound : HereditaryBudgeted.Within budgets body.nativeDepth

def BudgetPiAtomOrigins (budgets : HereditaryBudgeted.Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .sort _ => False
  | _ + 1, .fn _ _ => False
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => False
  | _ + 1, .pi _ _ _ rows =>
      ∀ key result, (key, result) ∈ rows →
        ∃ relevant, Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result)
  | _ + 1, .pad atom => BudgetPiAtomOrigins budgets env U registry target locals σ available A B atom

def BudgetPiProfileOrigins (budgets : HereditaryBudgeted.Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, BudgetPiAtomOrigins budgets env U registry target locals σ available A B atom

noncomputable def BudgetPiRowCertificate.atFlag
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available oldRelevant A B key result)
    (formed : result.HasType (.sort relevant)) :
    BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result :=
  { row with body := .observe (.code oldRelevant row.body) formed
             bodyBound := by simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using row.bodyBound }

private theorem BudgetPiAtomOrigins.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : BudgetPiAtomOrigins budgets env U registry target locals σ available A B a) :
    BudgetPiAtomOrigins budgets env U registry target locals σ available A B b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact BudgetPiAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem SortableRows.rowCertificateBudgeted
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (rows : SortableRows env U registry target locals σ A B relevant ambient table footprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (rowsBound : HereditaryBudgeted.Within budgets rows.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result) := by
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
               outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm)
               domainBound := domainBound
               bodyBound := by intro current fuel member; have := rowsBound current fuel member; simp only [SortableRows.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this }⟩
    · exact tail.rowCertificateBudgeted domain domainBound
        (by intro current fuel member; have := rowsBound current fuel member; simp only [SortableRows.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this) domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

theorem PiRows.rowCertificateBudgeted
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (rows : PiRows env U registry target locals σ A B ambient table footprint)
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (rowsBound : HereditaryBudgeted.Within budgets rows.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available true A B key result) := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨{ domainSupport := ambient
               domainFootprint := domainFootprint
               domain := .ofCode domain domain.formed
               domainAvailable := domainAvailable
               inputTyped := guard.inputTyped
               alignment := .step guard.path guard.inputTyped guard.formed guard.domains (.refl _)
               anchor := guard.anchor
               bodyFootprint := _
               body := .ofCode body body.formed
               packed := _
               outside := _
               pack := pack
               covered := covered
               outsideAvailable := fun i need hm => resources i need (List.mem_append_left _ hm)
               domainBound := by simpa only [SortableCert.nativeDepth] using domainBound
               bodyBound := by intro current fuel member; have := rowsBound current fuel member; simp only [PiRows.nativeDepth] at this; simpa only [SortableCert.nativeDepth] using Nat.le_trans (Nat.le_max_left _ _) this }⟩
    · exact tail.rowCertificateBudgeted domain domainBound
        (by intro current fuel member; have := rowsBound current fuel member; simp only [PiRows.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this) domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

theorem Obs.piOriginsBudgeted
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint)
    (queryBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile := by
  match observation with
  | .empty => exact fun _ member => nomatch member
  | .pi domain guard bodies =>
    intro atom member
    cases List.mem_singleton.mp member
    intro key result row
    exact ⟨true, bodies.rowCertificateBudgeted domain
      (by intro c f h; have := queryBound c f h; simp only [Obs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this)
      (by intro c f h; have := queryBound c f h; simp only [Obs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this)
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) row⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsBudgeted (by intro c f h; have := queryBound c f h; simp only [Obs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this) (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsBudgeted (by intro c f h; have := queryBound c f h; simp only [Obs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this) (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piOriginsBudgeted (by simpa only [Obs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact source.piOriginsBudgeted (by simpa only [Obs.nativeDepth] using queryBound) resources old ho
  | .unpad source =>
    intro atom member
    exact source.piOriginsBudgeted (by simpa only [Obs.nativeDepth] using queryBound) resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piOriginsBudgeted (by simpa only [Obs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

/-- A literal source Pi observation supplies rows from its actual constructor.
Value views cannot invent a Pi atom; all nontrivial function views are excluded
by the source observation's recursively retained Pi origin. -/
noncomputable def BudgetPiRowCertificate.map_output
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result)
    (change : AtomView env U registry target old new) :
    BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key (change.mapType result) :=
  { row with body := .map change row.body
             bodyBound := by intro current fuel member; simpa only [SortableCert.nativeDepth] using row.bodyBound current fuel member }

noncomputable def BudgetPiRowCertificate.domainRekey
    (henv : env.Ordered)
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result)
    (path : TypeConversion env U target key.domain newDomain)
    (typed : key.input.HasType support) (formed : support.HasType (.sort true))
    (related : TypeRelated env U registry target key.domain newDomain support) :
    BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B (domainKey key newDomain) result :=
  { row with alignment := .step path.symm typed formed (related.symm henv typed.wf_type) row.alignment
             anchor := row.anchor.rekey henv path typed formed related }

theorem BudgetPiRowCertificate.input_view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B (inputKey key input) result) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨bodyFootprint, outside, packed, body, pack, covered, outsideAvailable, bodyDepth⟩ :=
    row.body.rebind_local_allDepth henv hscoped hTarget
      (variableProfileView forward (Locals.push locals) (σ.cons key.anchor))
      (variableProfileView_available input available) (fun current => variableProfileView_depth current forward _ _) live row.pack row.covered
      row.outsideAvailable externalLive closed
  obtain ⟨domainFootprint, domain, domainAvailable, domainDepth⟩ := row.domain.map_profile_view_allDepth row.domainAvailable backward
  exact ⟨{
    domainSupport := backward.mapType row.domainSupport
    domainFootprint := _
    domain := domain
    domainAvailable := domainAvailable
    inputTyped := backward.mapType_typed row.inputTyped
    alignment := row.alignment.mapInput henv hscoped backward
    anchor := (AdapterSeed.view .same backward).admission henv hscoped hTarget row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable
    domainBound := fun current fuel member => Nat.le_trans (domainDepth current) (row.domainBound current fuel member)
    bodyBound := fun current fuel member => Nat.le_trans (bodyDepth current) (row.bodyBound current fuel member) }⟩

noncomputable def BudgetPiRowCertificate.pad
    (henv : env.Ordered)
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B (key : Key n) result) :
    BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key.pad result.pad where
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
  domainBound := by simpa only [SortableCert.nativeDepth] using row.domainBound
  bodyBound := by simpa only [SortableCert.nativeDepth] using row.bodyBound

theorem BudgetPiRowCertificate.unpad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B (key : Key n).pad result)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result.down) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  have resources : Footprint.Available [(0, ⟨n, key.input⟩)]
      (Valuation.push (rowInputNeeds key.input) available) := by
    intro i need hm
    cases List.mem_singleton.mp hm
    exact List.mem_append_left _ List.mem_cons_self
  obtain ⟨bodyFootprint, outside, packed, body, pack, covered, outsideAvailable, bodyDepth⟩ :=
    (SortableCert.down row.body).rebind_local_allDepth henv hscoped hTarget
      (Obs.pad (.var (Locals.push locals) (σ.cons key.anchor) 0 key.input))
      resources (by
        intro current
        change (Obs.pad (.var (Locals.push locals) (σ.cons key.anchor) 0 key.input)).nativeDepth current = 0
        simp only [Obs.nativeDepth]) live row.pack row.covered row.outsideAvailable externalLive closed
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
    outsideAvailable := outsideAvailable
    domainBound := by simpa only [SortableCert.nativeDepth] using row.domainBound
    bodyBound := by intro current fuel member; have h := bodyDepth current; simp only [SortableCert.nativeDepth] at h; exact Nat.le_trans h (row.bodyBound current fuel member) }⟩

private theorem BudgetPiProfileOrigins.pad
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile : Profile n)) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem BudgetPiProfileOrigins.down
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile : Profile (n + 1))) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

/-- Hereditary focusing retains the original row and its domain alignment.
Only the selected codomain support changes, using its finite Minimal child. -/
private theorem BudgetPiProfileOrigins.focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {profile}, focused ≤ profile →
      BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile →
      BudgetPiProfileOrigins budgets env U registry target locals σ available A B focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {profile}, focused ≤ profile →
        BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile →
        BudgetPiProfileOrigins budgets env U registry target locals σ available A B focused) with
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
    exact ⟨relevant, ⟨{ row with
      body := .focusMinimal row.body outputMinimal resultBound
      bodyBound := by intro current fuel member; simpa only [SortableCert.nativeDepth] using row.bodyBound current fuel member }⟩⟩
  | pad lower ih bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

private theorem BudgetPiProfileOrigins.not_sort
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

private theorem BudgetPiProfileOrigins.rankShift
    (henv : env.Ordered)
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile : Profile (n + 1))) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile.rankShift := by
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
    BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result →
    Admitted env U registry target key anchor anchor →
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B
      (reanchorKey key anchor) result))

include henv hscoped hTarget formedA formedB substitutions fits in
private theorem BudgetPiRowCertificate.externalLive
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result) :
    Footprint.Live env U registry target row.outside := by
  have scope := IsDefEq.closedN henv formedB
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  exact fits.leavesLive henv hscoped hTarget row.outsideAvailable
    (row.pack.scoped (row.body.scoped scope))

include henv hscoped hTarget closed formedA formedB substitutions fits in
private theorem BudgetPiProfileOrigins.unshift
    (key : Key n)
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile : Profile (n + 2))) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile.unshift key) := by
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
private theorem BudgetPiProfileOrigins.mapWith
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B (change.mapType profile) := by
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
    exact (BudgetPiProfileOrigins.mapWith child origins.down).pad
  | _, _, _, .trans first second =>
    exact BudgetPiProfileOrigins.mapWith second (BudgetPiProfileOrigins.mapWith first origins)
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem BudgetPiProfileOrigins.sortFlags_nil
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem BudgetPiProfileOrigins.supportWith
    (action : SupportAction env U registry target n)
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact BudgetPiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
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
        exact ⟨relevant, ⟨{ row with
          body := .support child row.body
          bodyBound := by intro current fuel member; simpa only [SortableCert.nativeDepth] using row.bodyBound current fuel member }⟩⟩
  | pad child ih => exact (ih origins.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem BudgetPiProfileOrigins.codeActionWith
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B nextProfile := by
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
    exact BudgetPiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change origins
  | support action =>
    exact BudgetPiProfileOrigins.supportWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact BudgetPiProfileOrigins.focusMinimal minimal bound origins

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
private theorem BudgetPiAtomOrigins.actionWith {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : BudgetPiAtomOrigins budgets env U registry target locals σ available A B a) :
    BudgetPiAtomOrigins budgets env U registry target locals σ available A B b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact BudgetPiProfileOrigins.codeActionWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow in
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem CodeCert.piOriginsBudgetedWith
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (queryBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile := by
  match certificate with
  | .seed observation _ => exact observation.piOriginsBudgeted (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth] using queryBound) resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsBudgetedWith (by intro c f h; have := queryBound c f h; simp only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this) (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsBudgetedWith (by intro c f h; have := queryBound c f h; simp only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this) (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources).pad
  | .familyPad source =>
    exact False.elim (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources).down
  | .map change source =>
    exact BudgetPiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources)
  | .focusMinimal source minimal bound =>
    exact BudgetPiProfileOrigins.focusMinimal minimal bound (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ member
termination_by sizeOf certificate

include henv hscoped hTarget closed formedA formedB substitutions fits reanchorRow
mutual
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. Only the reanchor
case calls the original body semantics; callers supply that operation with
their own exact source-context invariant. -/
theorem SortableCert.piOriginsBudgetedWith
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (queryBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile := by
  match certificate with
  | .seed observation _ => exact observation.piOriginsBudgeted (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth] using queryBound) resources
  | .observe observation _ => exact observation.piOriginsBudgetedWith (by simpa only [SortableCert.nativeDepth] using queryBound) resources
  | .ofCode source _ =>
    exact source.piOriginsBudgetedWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow (by simpa only [SortableCert.nativeDepth] using queryBound) resources
  | .pi domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    intro key result selected
    exact ⟨_, rows.rowCertificateBudgeted domain
      (by intro c f h; have := queryBound c f h; simp only [SortableCert.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this)
      (by intro c f h; have := queryBound c f h; simp only [SortableCert.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this)
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) selected⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsBudgetedWith (by intro c f h; have := queryBound c f h; simp only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this) (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsBudgetedWith (by intro c f h; have := queryBound c f h; simp only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this) (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources).pad
  | .sortPad source =>
    exact False.elim (BudgetPiProfileOrigins.not_sort (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources))
  | .familyPad source =>
    exact False.elim (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources).down
  | .support action source =>
    exact BudgetPiProfileOrigins.supportWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources)
  | .map change source =>
    exact BudgetPiProfileOrigins.mapWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow change (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources)
  | .focusMinimal source minimal bound =>
    exact BudgetPiProfileOrigins.focusMinimal minimal bound (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ member
termination_by sizeOf certificate

theorem SortableObs.piOriginsBudgetedWith
    (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
    (queryBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile := by
  match observation with
  | .legacy source => exact source.piOriginsBudgeted (by simpa only [SortableObs.nativeDepth] using queryBound) resources
  | .code _ source => exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piOriginsBudgetedWith (by intro c f h; have := queryBound c f h; simp only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_left _ _) this) (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.piOriginsBudgetedWith (by intro c f h; have := queryBound c f h; simp only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] at this; exact Nat.le_trans (Nat.le_max_right _ _) this) (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .action source action =>
    intro atom member
    cases List.mem_singleton.mp member
    exact BudgetPiAtomOrigins.actionWith henv hscoped hTarget closed formedA formedB substitutions fits
      reanchorRow action (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _))
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources old ho
  | .unpad source =>
    intro atom member
    exact source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piOriginsBudgetedWith (by simpa only [CodeCert.nativeDepth, SortableCert.nativeDepth, SortableObs.nativeDepth] using queryBound) resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
end
end
/-- Reanchor a retained Pi row using just its original domain and body
formation occurrences. Both context entries keep hereditary source certificates. -/
theorem BudgetPiRowCertificate.reanchorBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B anchor : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (tailBound : HereditaryBudgeted.Within budgets tail.nativeDepth)
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B
      (reanchorKey key anchor) result) := by
  let frame := SortableTailPairedFits.diagonal context tail
  have frameBound : HereditaryBudgeted.Within budgets frame.nativeDepth := by
    intro current fuel member
    simpa only [frame, SortableTailPairedFits.diagonal, SortableTailPairedFits.nativeDepth,
      SortableTailFits.nativeDepth_reorigin, Nat.max_self] using tailBound current fuel member
  obtain ⟨domainCode⟩ := HereditaryBudgeted.Transfer.sortable henv hscoped hTarget closed
    (domainIH target locals σ σ available closed hTarget substitutions frame frameBound)
    row.domain row.domainBound row.domainAvailable
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
  have bodyFrameBound : HereditaryBudgeted.Within budgets bodyFrame.nativeDepth := by
    intro current fuel member
    simp only [bodyFrame, SortableTailPairedFits.pushCertificates, SortableTailPairedFits.nativeDepth,
      SortableTailFits.nativeDepth]
    have original := Nat.max_le.mp (frameBound current fuel member)
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨row.domainBound current fuel member, original.1⟩,
      Nat.max_le.mpr ⟨row.domainBound current fuel member, original.2⟩⟩
  obtain ⟨changed⟩ := HereditaryBudgeted.Transfer.sortable henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) (bodyIH target (Locals.push locals) (σ.cons key.anchor) (σ.cons anchor)
    (Valuation.push needs available) (Valuation.push_atomized_closed closed _)
    hTarget paired bodyFrame bodyFrameBound) row.body row.bodyBound
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
    outsideAvailable := resources
    bodyBound := changed.valueBound }⟩

/-- Every Pi row in a hereditary formation query comes from its finite source
syntax, with reanchoring discharged by the two fixed original formation children. -/
theorem SortableCert.piOriginsBudgetedOriginal
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
    (tailBound : HereditaryBudgeted.Within budgets tail.nativeDepth)
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (queryBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile :=
  certificate.piOriginsBudgetedWith henv hscoped hTarget closed
    (originalDomain.sound.defeq.mono hle) (originalBody.sound.defeq.mono hle)
    substitutions tail
    (fun row admitted => row.reanchorBudgeted henv hscoped hle hTarget closed
      context originalDomain originalBody substitutions tail tailBound domainIH bodyIH admitted) queryBound resources

/-- Selecting a concrete row retains the requested formation flag. The flag
change uses the parent certificate's intrinsic row formation, not downward closure. -/
theorem SortableCert.piRowOfBudgetOrigins
    {n : Nat} {profile : Profile (n + 1)} {support : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B profile)
    (piMember : (.pi protoDomain protoBody support rows) ∈ profile.atoms)
    (rowMember : (key, result) ∈ rows) :
    Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result) := by
  obtain ⟨oldRelevant, ⟨row⟩⟩ := origins _ piMember key result rowMember
  have formation := (Profile.HasType.pi_iff.mp (certificate.formed.singleton_of_mem piMember)).2
    key result rowMember
  exact ⟨row.atFlag formation⟩

theorem SortableCert.piRowBudgetedOriginal
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
    (tailBound : HereditaryBudgeted.Within budgets tail.nativeDepth)
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    {profile : Profile (n + 1)}
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (queryBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available)
    (typed : (Profile.fn (key : Key n) output).HasType profile) :
    ∃ result, Nonempty (BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result) ∧
      (Profile.singleton output).HasType result := by
  obtain ⟨protoDomain, protoBody, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have origins := certificate.piOriginsBudgetedOriginal henv hscoped hle hTarget closed context
    originalDomain originalBody substitutions tail tailBound domainIH bodyIH queryBound resources
  exact ⟨result, certificate.piRowOfBudgetOrigins origins member row, resultTyped⟩


theorem BudgetPiProfileOrigins.forget
    (origins : BudgetPiProfileOrigins budgets env U registry target locals σ available A B (profile : Profile n)) :
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
      obtain ⟨relevant, ⟨row⟩⟩ := origin key result selected
      exact ⟨relevant, ⟨row.toSortablePiRowCertificate⟩⟩
    | pad atom =>
      exact ih (profile := .singleton atom) (fun other selected => by
        cases List.mem_singleton.mp selected
        exact origin) atom (List.mem_singleton_self _)

end Lean4Lean.AnchoredSource.Adapted
