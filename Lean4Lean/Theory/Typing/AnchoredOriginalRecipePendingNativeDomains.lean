import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedRowActions
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionAtoms

/-! Pending native-domain elimination keeps the literal original domain
certificate as recursive input. Only finite code actions are accumulated. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

abbrev PendingDomain (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : Profile k) (support : Profile n) :=
  SortableCodeAction env U registry target true original true support

def PendingPiDomainAtom (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : Profile k) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi _ _ domain _ => Nonempty (PendingDomain env U registry target original domain)
  | _ + 1, .pad atom => PendingPiDomainAtom env U registry target original atom
  | _ + 1, _ => False

def PendingPiDomainProfile (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : Profile k) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, PendingPiDomainAtom env U registry target original atom

private theorem PendingPiDomainAtom.view {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origin : PendingPiDomainAtom env U registry target original a) :
    PendingPiDomainAtom env U registry target original b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact PendingPiDomainAtom.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem PendingPiDomainProfile.pad
    (origins : PendingPiDomainProfile env U registry target original profile) :
    PendingPiDomainProfile env U registry target original profile.pad := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  exact origins old hm

private theorem PendingPiDomainProfile.down
    (origins : PendingPiDomainProfile env U registry target original (profile : Profile (n + 1))) :
    PendingPiDomainProfile env U registry target original profile.down := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem PendingPiDomainProfile.rankShift
    (origins : PendingPiDomainProfile env U registry target original (profile : Profile (n + 1))) :
    PendingPiDomainProfile env U registry target original profile.rankShift := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => exact origin
  | pi protoA protoB domain rows =>
    obtain ⟨result⟩ := origin
    exact ⟨.comp result .pad⟩

private theorem PendingPiDomainProfile.unshift
    (origins : PendingPiDomainProfile env U registry target original (profile : Profile (n + 2)))
    (key : Key n) :
    PendingPiDomainProfile env U registry target original (profile.unshift key) := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi protoA protoB domain rows =>
    cases List.mem_singleton.mp member
    obtain ⟨result⟩ := origin
    exact ⟨.comp result .down⟩

private theorem PendingDomain.mapProfile
    (result : PendingDomain env U registry target original support)
    (change : ProfileView env U registry target input output) :
    Nonempty (PendingDomain env U registry target original (change.mapType support)) := by
  match change with
  | .nil => exact ⟨result⟩
  | .cons head tail =>
    obtain ⟨next⟩ := result.mapProfile tail
    exact ⟨.union (.comp result (.map head)) next⟩
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem PendingDomain.unions (seed : PendingDomain env U registry target original (seedProfile : Profile n))
    (profiles : List (Profile n))
    (certificates : ∀ profile ∈ profiles,
      Nonempty (PendingDomain env U registry target original profile)) :
    Nonempty (PendingDomain env U registry target original (Profile.unions profiles)) := by
  induction profiles with
  | nil => exact ⟨.comp seed (.focusMinimal .nil (by cases n <;> exact fun _ h => nomatch h))⟩
  | cons profile profiles ih =>
    obtain ⟨first⟩ := certificates profile List.mem_cons_self
    obtain ⟨rest⟩ := ih (fun other member => certificates other (List.mem_cons_of_mem _ member))
    exact ⟨.union first rest⟩

private theorem PendingDomain.inputDomain
    (result : PendingDomain env U registry target original support)
    (backward : ProfileView env U registry target input output) :
    Nonempty (PendingDomain env U registry target original
      (inputDomain input backward.mapType support)) := by
  obtain ⟨extra⟩ := PendingDomain.unions result ((Basis input support).map backward.mapType) (by
    intro profile member
    obtain ⟨focused, selected, rfl⟩ := List.mem_map.mp member
    let focus : PendingDomain env U registry target original focused :=
      .comp result (.focusMinimal (Basis.minimal selected) (Basis.valid selected).2)
    exact focus.mapProfile backward)
  exact ⟨.union result extra⟩

private theorem PendingPiDomainProfile.map {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origins : PendingPiDomainProfile env U registry target original profile) :
    PendingPiDomainProfile env U registry target original (change.mapType profile) := by
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
      change PendingPiDomainAtom _ _ _ _ _ (if _ then _ else _)
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

private theorem PendingPiDomainProfile.focusMinimal
    {value focused : Profile n} (minimal : Minimal value focused)
    {bound : Profile n} (dominated : focused ≤ bound)
    (origins : PendingPiDomainProfile env U registry target original bound) :
    PendingPiDomainProfile env U registry target original focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ support _ => ∀ {bound}, support ≤ bound →
        PendingPiDomainProfile env U registry target original bound →
        PendingPiDomainProfile env U registry target original support) with
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
    exact ⟨.comp source (.focusMinimal hi domainBound)⟩
  | pad lower ih =>
    rename_i bound dominated origins
    apply PendingPiDomainProfile.pad
    apply ih (bound := bound.down)
    · simpa only [Profile.down_pad] using dominated.down
    · exact origins.down

private theorem PendingPiDomainProfile.sortFlags_nil
    (origins : PendingPiDomainProfile env U registry target original (profile : Profile n)) :
    profile.sortFlags = [] := by
  induction n with
  | zero =>
    cases profile with
    | nil => rfl
    | cons atom rest => exact False.elim (origins atom List.mem_cons_self)
  | succ n ih => exact ih origins.down

private theorem PendingPiDomainProfile.support
    (action : SupportAction env U registry target n)
    (origins : PendingPiDomainProfile env U registry target original profile) :
    PendingPiDomainProfile env U registry target original (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change =>
    exact PendingPiDomainProfile.map change origins
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

private theorem PendingPiDomainProfile.not_sort
    (origins : PendingPiDomainProfile env U registry target original
      (Profile.sort (n := n) relevant)) : False := by
  cases n with
  | zero => exact origins _ (List.mem_singleton_self _)
  | succ n => exact origins _ (List.mem_singleton_self _)

private theorem PendingPiDomainProfile.codeAction
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (origins : PendingPiDomainProfile env U registry target original profile) :
    PendingPiDomainProfile env U registry target original nextProfile := by
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
    exact PendingPiDomainProfile.map change origins
  | support action =>
    exact PendingPiDomainProfile.support action origins
  | select member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact origins _ member
  | focusMinimal minimal bound => exact PendingPiDomainProfile.focusMinimal minimal bound origins

private theorem PendingPiDomainAtom.action {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : PendingPiDomainAtom env U registry target original a) :
    PendingPiDomainAtom env U registry target original b := by
  induction action with
  | view change => exact origin.view change
  | @code relevant rank input next output action formed =>
    have origins : PendingPiDomainProfile env U registry target original
        (Profile.singleton input) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact PendingPiDomainProfile.codeAction action origins _ (List.mem_singleton_self _)
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)



theorem PendingPiDomainProfile.outputPath
    (path : GeneralOutputPath env U registry target a b)
    (origin : PendingPiDomainAtom env U registry target original a) :
    PendingPiDomainAtom env U registry target original b := by
  induction path with
  | refl => exact origin
  | action path change ih => exact PendingPiDomainAtom.action change ih
  | code path change formed ih =>
    apply PendingPiDomainProfile.codeAction change (profile := .singleton _) ?_ _ List.mem_cons_self
    intro atom member
    cases List.mem_singleton.mp member
    exact ih
  | pad path ih => exact ih
  | unpad path ih => exact ih

/-- Execute every mixed-grade output wrapper while preserving the original
native domain as the sole recursive input. Empty requested supports are allowed. -/
theorem GeneralOutputPath.pendingNativeDomain
    {rows : List (Key k × Profile k)} {nextRows : List (Key n × Profile n)}
    (path : GeneralOutputPath env U registry target (r := k + 1) (n := n + 1)
      (AtomData.pi A B (original : Profile k) rows)
      (AtomData.pi C D (support : Profile n) nextRows)) :
    Nonempty (PendingDomain env U registry target original support) :=
  PendingPiDomainProfile.outputPath path ⟨.id⟩

/-- Select one literal source atom and retain its exact finite output path. -/
theorem PendingDomain.selectOriginal
    (pending : PendingDomain env U registry target original support)
    (formed : original.HasType (.sort true)) (member : atom ∈ support.atoms) :
    ∃ old ∈ original.atoms, Nonempty (GeneralOutputPath env U registry target old atom) := by
  obtain ⟨old, oldMember, ⟨action⟩⟩ := pending.atom member
  exact ⟨old, oldMember, ⟨.code .refl action (formed.singleton_of_mem oldMember)⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
