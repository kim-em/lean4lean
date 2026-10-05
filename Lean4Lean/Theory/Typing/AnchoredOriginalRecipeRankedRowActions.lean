import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedPendingRows
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyActions

/-! Finite action execution retains the literal original native row. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

def RankedPiAtom (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : List (Key k × Profile k)) (relevant : Bool) :
    {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi _ _ _ rows => ∀ key result, (key, result) ∈ rows →
      Nonempty (RankedPendingNativeRow env U registry target original relevant key result)
  | _ + 1, .pad atom => RankedPiAtom env U registry target original relevant atom
  | _ + 1, _ => False

abbrev RankedPiProfile (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : List (Key k × Profile k)) (relevant : Bool)
    (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, RankedPiAtom env U registry target original relevant atom

namespace RankedPiProfile
variable {original : List (Key k × Profile k)}

theorem empty : RankedPiProfile env U registry target original relevant (Profile.empty : Profile n) :=
  fun _ member => nomatch member

theorem union
    (left : RankedPiProfile env U registry target original relevant p)
    (right : RankedPiProfile env U registry target original relevant q) :
    RankedPiProfile env U registry target original relevant (p.union q) :=
  fun atom member => (List.mem_append.mp member).elim (left atom) (right atom)

theorem pad (origins : RankedPiProfile env U registry target original relevant p) :
    RankedPiProfile env U registry target original relevant p.pad := by
  intro atom member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  exact origins old present

theorem unpad (origins : RankedPiProfile env U registry target original relevant p.pad) :
    RankedPiProfile env U registry target original relevant p :=
  fun atom member => origins (.pad atom) (List.mem_map_of_mem member)

theorem down (origins : RankedPiProfile env U registry target original relevant (p : Profile (n+1))) :
    RankedPiProfile env U registry target original relevant p.down := by
  intro atom member
  obtain ⟨old, present, member⟩ := List.mem_flatMap.mp member
  have origin := origins old present
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad old => cases List.mem_singleton.mp member; exact origin

theorem select (origins : RankedPiProfile env U registry target original relevant p)
    (member : atom ∈ p.atoms) :
    RankedPiProfile env U registry target original relevant (.singleton atom) := by
  intro selected present
  cases List.mem_singleton.mp present
  exact origins _ member

theorem not_sort (origins : RankedPiProfile env U registry target original relevant
    (Profile.sort (n := n) flag)) : False := by
  cases n <;> exact origins _ List.mem_cons_self

theorem sortFlags_nil (origins : RankedPiProfile env U registry target original relevant (p : Profile n)) :
    p.sortFlags = [] := by
  induction n with
  | zero =>
    cases p with
    | nil => rfl
    | cons a rest => exact False.elim (origins a List.mem_cons_self)
  | succ n ih => exact ih origins.down

theorem rankShift (origins : RankedPiProfile env U registry target original relevant (p : Profile (n+1))) :
    RankedPiProfile env U registry target original relevant p.rankShift := by
  intro atom member
  obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
  have origin := origins old present
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad => exact origin
  | pi A B support rows => exact fun _ _ member => RankedPendingNativeRow.rankShiftRows origin member

theorem unshift (key : Key n)
    (origins : RankedPiProfile env U registry target original relevant (p : Profile (n+2))) :
    RankedPiProfile env U registry target original relevant (p.unshift key) := by
  intro atom member
  obtain ⟨old, present, member⟩ := List.mem_flatMap.mp member
  have origin := origins old present
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi A B support rows =>
    cases List.mem_singleton.mp member
    exact fun _ _ member => RankedPendingNativeRow.unshiftRows origin member

theorem map
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : RankedPiProfile env U registry target original relevant profile) :
    RankedPiProfile env U registry target original relevant (change.mapType profile) := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origins
  | _ + 1, _, _, .reanchor admitted =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := origins old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows => exact fun _ _ member => RankedPendingNativeRow.anchorRows origin admitted member
  | j + 1, _, _, .domainRekey (key := oldKey) path typed supportFormed related =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := origins old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      simp only [domainRekeyAtom]
      split
      · intro key result member
        rcases mem_reanchorRows.mp member with oldMember | ⟨rfl, oldMember⟩
        · exact origin _ _ oldMember
        · obtain ⟨row⟩ := origin oldKey result oldMember
          let witness : Atom j := match j with | 0 => true | _ + 1 => .sort true
          exact ⟨.change row (witness := witness) (.domainRekey path typed supportFormed related) .id⟩
      · exact origin
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := origins old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      simp only [AtomView.mapType, inputTypes] at *
      split
      · exact fun _ _ member => RankedPendingNativeRow.inputRows origin forward backward member
      · exact origin
  | _ + 2, _, _, .commutePadFn _ _ => exact origins.down.rankShift
  | _ + 2, _, _, .uncommutePadFn key _ => exact (origins.unshift key).pad
  | j + 1, _, _, .fn wanted child =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := origins old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows =>
      intro key result member
      rcases mem_outputRows.mp member with oldMember | ⟨rfl, oldResult, oldMember, rfl⟩
      · exact origin key result oldMember
      · obtain ⟨row⟩ := origin _ oldResult oldMember
        let witness : Atom j := match j with | 0 => true | _ + 1 => .sort true
        exact ⟨.change row (witness := witness) (.refl _) (.map child)⟩
  | _ + 1, _, _, .pad child => exact (RankedPiProfile.map child origins.down).pad
  | _, _, _, .trans first second => exact RankedPiProfile.map second (RankedPiProfile.map first origins)
termination_by sizeOf change

theorem support
    (action : SupportAction env U registry target n)
    (origins : RankedPiProfile env U registry target original relevant profile) :
    RankedPiProfile env U registry target original relevant (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    simp only [SupportAction.apply, Profile.flatSorts, origins.sortFlags_nil,
      List.flatMap_nil, Profile.atoms, List.not_mem_nil] at member
  | view change => exact map change origins
  | output wanted child ih =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have origin := origins old present
    cases old with
    | sort | fn | family | ctor | record => cases origin
    | pad => exact origin
    | pi A B support rows => exact fun _ _ member => RankedPendingNativeRow.outputRows origin child member
  | pad child ih => exact (ih origins.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH => exact union (firstIH origins) (secondIH origins)

theorem focusMinimal {value focused : Profile n}
    (minimal : Minimal value focused) :
    ∀ {p}, focused ≤ p → RankedPiProfile env U registry target original relevant p →
      RankedPiProfile env U registry target original relevant focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {p}, focused ≤ p →
        RankedPiProfile env U registry target original relevant p →
        RankedPiProfile env U registry target original relevant focused) with
  | nil => exact fun _ _ => empty
  | cons first tail ihFirst ihTail =>
    intro p bound origins
    exact union (ihFirst (Profile.le_trans (Profile.le_union_left _ _) bound) origins)
      (ihTail (Profile.le_trans (Profile.le_union_right _ _) bound) origins)
  | @sort n atom flag typed p bound origins =>
    cases n with
    | zero => exact False.elim (origins _ (Profile.sort_le_mem_zero bound))
    | succ n => exact False.elim (origins _ (Profile.sort_le_mem bound))
  | @family n value data typed p bound origins =>
    obtain ⟨other, present, covered⟩ := bound _ List.mem_cons_self
    cases other <;> try contradiction
    exact False.elim (origins _ present)
  | @fn n support result A B key output inputMinimal outputMinimal supportFormed _ _ p bound origins =>
    obtain ⟨oldSupport, oldRows, present, supportBound, rowsBound⟩ :=
      Profile.pi_le_inv bound List.mem_cons_self
    have old := origins _ present
    intro atom member
    cases List.mem_singleton.mp member
    intro selected result member
    cases List.mem_singleton.mp member
    obtain ⟨oldResult, oldMember, resultBound⟩ := rowsBound key _ List.mem_cons_self
    obtain ⟨row⟩ := old key oldResult oldMember
    let witness : Atom n := match n with | 0 => true | _ + 1 => .sort true
    exact ⟨.change row (witness := witness) (.refl _) (.focusMinimal outputMinimal resultBound)⟩
  | @pad n atom support lower ih p bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

theorem code
    (action : SortableCodeAction env U registry target flag profile next nextProfile)
    (origins : RankedPiProfile env U registry target original relevant profile) :
    RankedPiProfile env U registry target original relevant nextProfile := by
  induction action with
  | id | retag => exact origins
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH => exact union (firstIH origins) (secondIH origins)
  | pad => exact origins.pad
  | down => exact origins.down
  | unpad => exact origins.unpad
  | sortPad => exact False.elim origins.not_sort
  | familyPad => exact False.elim (origins _ List.mem_cons_self)
  | map change => exact map change origins
  | support action => exact support action origins
  | select member => exact origins.select member
  | focusMinimal minimal bound => exact focusMinimal minimal bound origins

private theorem atomView
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : RankedPiAtom env U registry target original relevant a) :
    RankedPiAtom env U registry target original relevant b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | j + 1, _, _, .pad child => exact atomView (n := j) child origin
  | _, _, _, .trans first second => exact atomView second (atomView first origin)
termination_by sizeOf change

theorem atomAction {a b : Atom n}
    (action : AtomAction env U registry target a b)
    (origin : RankedPiAtom env U registry target original relevant a) :
    RankedPiAtom env U registry target original relevant b := by
  induction action with
  | view change => exact atomView change origin
  | @code flag rank a next b action formed =>
    have input : RankedPiProfile env U registry target original relevant (.singleton a) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact origin
    exact code action input _ List.mem_cons_self
  | fn => cases origin
  | pad child ih => exact ih origin
  | comp first second firstIH secondIH => exact secondIH (firstIH origin)

/-- Exhaustive execution of the real mixed-grade output path. No body
certificate is synthesized while traversing the path. -/
theorem outputPath
    (path : GeneralOutputPath env U registry target a b)
    (origin : RankedPiAtom env U registry target original relevant a) :
    RankedPiAtom env U registry target original relevant b := by
  induction path with
  | refl => exact origin
  | action path change ih => exact atomAction change ih
  | code path change formed ih =>
    apply code change (profile := .singleton _) ?_ _ List.mem_cons_self
    intro atom member
    cases List.mem_singleton.mp member
    exact ih
  | pad path ih => exact ih
  | unpad path ih => exact ih

/-- Literal native input initializes the path interpreter without a supplier. -/
theorem nativePath
    {table : List (Key k × Profile k)}
    (path : GeneralOutputPath env U registry target (r := k + 1)
      (AtomData.pi A B domain table) atom) :
    RankedPiAtom env U registry target table relevant atom := by
  apply outputPath path
  intro key result member
  exact ⟨.fixed (.direct member)⟩

end RankedPiProfile

/-- Connect exhaustive path execution to the actual old body/BinderPack.
This is the native alternative of RichPiProgramOrigin, including all code,
view, focus, padding, and unpadding actions. -/
theorem RichRows.pathNativeCursor
    {k m : Nat} {ambient : Profile k} {result : Profile m} {key : Key m}
    {selectedSupport : Profile m} {selectedRows : List (Key m × Profile m)}
    {table : List (Key k × Profile k)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (path : GeneralOutputPath env U registry target (r := k + 1) (n := m + 1)
      (AtomData.pi prototypeDomain prototypeBody ambient table)
      (AtomData.pi selectedDomain selectedBody selectedSupport selectedRows))
    (member : (key, result) ∈ selectedRows) :
    ∃ pending : RankedPendingNativeRow env U registry target table relevant key result,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy) := by
  obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result member
  obtain ⟨row, same, smaller, depth⟩ := rows.rankedPendingCursor domain domainAvailable resources pending
  exact ⟨pending, row, same, smaller, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
