import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowReplayOperations

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def WorldPiAtomOrigins
    (env : VEnv) {strata : EquationStratification env} (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (U : Nat) (registry : CanonicalHead.Registry)
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
        ∃ relevant, ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
          Nonempty (row.Controlled controls frontier)
  | _ + 1, .pad atom => WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode atom

def WorldPiProfileOrigins
    (env : VEnv) {strata : EquationStratification env} (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode atom

variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}
  {domainNode : EndpointState sourceEnv U source A (.sort u)}
  {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
theorem WorldPiAtomOrigins.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode a) :
    WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact WorldPiAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem WorldPiProfileOrigins.pad
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (profile : Profile n)) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

theorem WorldPiProfileOrigins.down
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (profile : Profile (n + 1))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

/-- Hereditary focusing retains the original row and its domain alignment.
Only the selected codomain support changes, using its finite Minimal child. -/
theorem WorldPiProfileOrigins.focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {profile}, focused ≤ profile →
      WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile →
      WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {profile}, focused ≤ profile →
        WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile →
        WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode focused) with
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
    obtain ⟨relevant, row, ⟨ready⟩⟩ := origins _ present key oldResult oldMember
    obtain ⟨next, nextReady⟩ := ready.codeAction (.focusMinimal outputMinimal resultBound)
    exact ⟨relevant, next, nextReady⟩
  | pad lower ih bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

theorem WorldPiProfileOrigins.not_sort
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

theorem WorldPiProfileOrigins.rankShift
    (henv : env.Ordered)
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (profile : Profile (n + 1))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile.rankShift := by
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
    obtain ⟨relevant, row, ⟨ready⟩⟩ := origin oldKey oldOutput hm
    exact ⟨relevant, row.pad henv, ⟨ready.pad henv⟩⟩

theorem WorldPiProfileOrigins.lowerRaised
    {n N : Nat} {profile : Profile n} (bound : n ≤ N)
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode
      (raiseProfile N bound profile)) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
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

section
variable
  (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
  (closed : available.AtomClosed)
  (reanchorRow : ∀ {relevant : Bool} {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) →
    row.Controlled controls frontier →
    Admitted env U registry target key anchor anchor →
    ∃ next : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
      (reanchorKey key anchor) result, Nonempty (next.Controlled controls frontier))

include henv hscoped hTarget closed in
theorem WorldPiProfileOrigins.unshift
    (key : Key n)
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (profile : Profile (n + 2))) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (profile.unshift key) := by
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
    obtain ⟨relevant, row, ⟨ready⟩⟩ := origin key.pad oldResult oldMember
    obtain ⟨next, nextReady⟩ := ready.unpad henv hscoped hTarget closed
    exact ⟨relevant, next, nextReady⟩

include henv hscoped hTarget closed reanchorRow in
theorem WorldPiProfileOrigins.mapWith
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (change.mapType profile) := by
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
      · obtain ⟨relevant, row, ⟨ready⟩⟩ := origin _ result hm
        obtain ⟨next, nextReady⟩ := reanchorRow row ready admitted
        exact ⟨relevant, next, nextReady⟩
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
        · obtain ⟨relevant, row, ⟨ready⟩⟩ := origin _ result hm
          exact ⟨relevant, row.domainRekey henv path typed formed related, ⟨ready.domainRekey henv path typed formed related⟩⟩
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
        · obtain ⟨relevant, row, ⟨ready⟩⟩ := origin _ result hm
          obtain ⟨next, nextReady⟩ := ready.inputView henv hscoped hTarget closed forward backward
          exact ⟨relevant, next, nextReady⟩
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
      · obtain ⟨relevant, row, ⟨ready⟩⟩ := origin _ oldResult hm
        exact ⟨relevant, row.map_output child, ⟨ready.mapOutput child⟩⟩
  | _ + 1, _, _, .pad child =>
    exact (WorldPiProfileOrigins.mapWith child origins.down).pad
  | _, _, _, .trans first second =>
    exact WorldPiProfileOrigins.mapWith second (WorldPiProfileOrigins.mapWith first origins)
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem WorldPiProfileOrigins.sortFlags_nil
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

include henv hscoped hTarget closed reanchorRow in
theorem WorldPiProfileOrigins.supportWith
    (action : SupportAction env U registry target n)
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact WorldPiProfileOrigins.mapWith henv hscoped hTarget closed
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
      · obtain ⟨relevant, row, ⟨ready⟩⟩ := origin _ oldResult old
        exact ⟨relevant, { row with body := .support child row.body }, ⟨⟨ready.domain, ready.body.certSupport child⟩⟩⟩
  | pad child ih => exact (ih origins.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)

include henv hscoped hTarget closed reanchorRow in
theorem WorldPiProfileOrigins.codeActionWith
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile) :
    WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode nextProfile := by
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
    exact WorldPiProfileOrigins.mapWith henv hscoped hTarget closed
      reanchorRow change origins
  | support action =>
    exact WorldPiProfileOrigins.supportWith henv hscoped hTarget closed
      reanchorRow action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact WorldPiProfileOrigins.focusMinimal minimal bound origins

include henv hscoped hTarget closed reanchorRow in
theorem WorldPiAtomOrigins.actionWith {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode a) :
    WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact WorldPiProfileOrigins.codeActionWith henv hscoped hTarget closed
      reanchorRow action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)


end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
