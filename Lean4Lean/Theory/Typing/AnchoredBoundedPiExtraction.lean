import Lean4Lean.Theory.Typing.AnchoredBoundedPiRows

/-! Actual Pi certificates retain bounded domain/codomain provenance through
all finite code maps. This is the source-certificate seam used by bounded eta. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

def PiAtomOrigins (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .sort _ => False
  | _ + 1, .fn _ _ => False
  | _ + 1, .family _ | _ + 1, .ctor _ | _ + 1, .record _ => False
  | _ + 1, .pi _ _ _ rows =>
      ∀ key result, (key, result) ∈ rows →
        Nonempty (PiRowCertificate current fuel env U registry target locals σ available A B key result)
  | _ + 1, .pad atom => PiAtomOrigins current fuel env U registry target locals σ available A B atom

def PiProfileOrigins (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, PiAtomOrigins current fuel env U registry target locals σ available A B atom

private theorem PiAtomOrigins.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origin : PiAtomOrigins current fuel env U registry target locals σ available A B a) :
    PiAtomOrigins current fuel env U registry target locals σ available A B b := by
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
    (domainBound : domain.nativeDepth current ≤ fuel)
    (rowsBound : rows.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, result) ∈ table) :
    Nonempty (PiRowCertificate current fuel env U registry target locals σ available A B key result) := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [PiRows.nativeDepth] using rowsBound)
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
               bodyBound := bounds.1 }⟩
    · exact PiRows.rowCertificate domain tail domainBound bounds.2 domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

/-- A literal source Pi observation supplies rows from its actual constructor.
Value views cannot invent a Pi atom; all nontrivial function views are excluded
by the source observation's recursively retained Pi origin. -/
theorem Obs.piOrigins
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    PiProfileOrigins current fuel env U registry target locals σ available A B profile := by
  match observation with
  | .empty => exact fun _ member => nomatch member
  | .pi domain guard bodies =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    intro atom member
    cases List.mem_singleton.mp member
    intro key result row
    exact PiRows.rowCertificate domain bodies bounds.1 bounds.2
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) row
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact Obs.piOrigins left bounds.1 (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact Obs.piOrigins right bounds.2 (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (Obs.piOrigins source (by simpa only [Obs.nativeDepth] using bound) resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact Obs.piOrigins source (by simpa only [Obs.nativeDepth] using bound) resources old ho
  | .unpad source =>
    intro atom member
    exact Obs.piOrigins source (by simpa only [Obs.nativeDepth] using bound) resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := Obs.piOrigins source (by simpa only [Obs.nativeDepth] using bound) resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

private theorem PiProfileOrigins.pad
    (origins : PiProfileOrigins current fuel env U registry target locals σ available A B (profile : Profile n)) :
    PiProfileOrigins current fuel env U registry target locals σ available A B profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

private theorem PiProfileOrigins.down
    (origins : PiProfileOrigins current fuel env U registry target locals σ available A B (profile : Profile (n + 1))) :
    PiProfileOrigins current fuel env U registry target locals σ available A B profile.down := by
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
      PiProfileOrigins current fuel env U registry target locals σ available A B profile →
      PiProfileOrigins current fuel env U registry target locals σ available A B focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ focused _ => ∀ {profile}, focused ≤ profile →
        PiProfileOrigins current fuel env U registry target locals σ available A B profile →
        PiProfileOrigins current fuel env U registry target locals σ available A B focused) with
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
    exact ⟨{ row with body := .focusMinimal row.body outputMinimal resultBound,
                       bodyBound := by simpa only [CodeCert.nativeDepth] using row.bodyBound }⟩
  | pad lower ih bound origins =>
    exact (ih (by simpa only [Profile.down_pad] using bound.down) origins.down).pad

private theorem PiProfileOrigins.rankShift
    (henv : env.Ordered)
    (origins : PiProfileOrigins current fuel env U registry target locals σ available A B (profile : Profile (n + 1))) :
    PiProfileOrigins current fuel env U registry target locals σ available A B profile.rankShift := by
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
  (fits : PairedFits current fuel env U registry source target locals σ σ available)
  (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
  (originalBody : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))

include henv hscoped hTarget formedA formedB substitutions fits in
private theorem PiRowCertificate.externalLive
    (row : PiRowCertificate current fuel env U registry target locals σ available A B key result) :
    Footprint.Live env U registry target row.outside := by
  have scope := IsDefEq.closedN henv formedB
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  exact fits.forward.forget.leavesLive henv hscoped hTarget row.outsideAvailable
    (row.pack.scoped (row.body.scoped scope))

include henv hscoped hTarget closed formedA formedB substitutions fits in
private theorem PiProfileOrigins.unshift
    (key : Key n)
    (origins : PiProfileOrigins current fuel env U registry target locals σ available A B (profile : Profile (n + 2))) :
    PiProfileOrigins current fuel env U registry target locals σ available A B (profile.unshift key) := by
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

include henv hscoped hTarget closed formedA formedB substitutions fits originalDomain originalBody in
private theorem PiProfileOrigins.map
    {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : PiProfileOrigins current fuel env U registry target locals σ available A B profile) :
    PiProfileOrigins current fuel env U registry target locals σ available A B (change.mapType profile) := by
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
        exact row.reanchor henv hscoped hTarget closed formedA substitutions fits
          originalDomain originalBody admitted
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
    exact (PiProfileOrigins.map child origins.down).pad
  | _, _, _, .trans first second =>
    exact PiProfileOrigins.map second (PiProfileOrigins.map first origins)
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

include henv hscoped hTarget closed formedA formedB substitutions fits originalDomain originalBody in
/-- Complete row provenance for the actual source Pi certificate, including
all grade changes and all concrete computed code maps. -/
theorem CodeCert.piOrigins
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (bound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    PiProfileOrigins current fuel env U registry target locals σ available A B profile := by
  match certificate with
  | .seed observation _ => exact Obs.piOrigins observation (by simpa only [CodeCert.nativeDepth] using bound) resources
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [CodeCert.nativeDepth] using bound)
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact CodeCert.piOrigins left bounds.1 (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact CodeCert.piOrigins right bounds.2 (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source => exact (CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources).pad
  | .familyPad source =>
    exact False.elim (CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources).down
  | .map change source =>
    exact PiProfileOrigins.map henv hscoped hTarget closed formedA formedB substitutions fits
      originalDomain originalBody change (CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources)
  | .focusMinimal source minimal focusedBound =>
    exact PiProfileOrigins.focusMinimal minimal focusedBound
      (CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact CodeCert.piOrigins source (by simpa only [CodeCert.nativeDepth] using bound) resources _ member
termination_by sizeOf certificate

include henv hscoped hTarget closed formedA formedB substitutions fits originalDomain originalBody in
/-- The selected function cover yields actual source domain and codomain
certificates at its exact key. Its alignment is a finite chain of supported
raw type paths, so domain rekeying need not invent a common guard support. -/
theorem CodeCert.piRow
    {profile : Profile (n + 1)}
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (bound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available)
    (typed : (Profile.fn (key : Key n) output).HasType profile) :
    ∃ result, Nonempty (PiRowCertificate current fuel env U registry target locals σ available A B key result) ∧
      (Profile.singleton output).HasType result := by
  obtain ⟨protoDomain, protoBody, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have origins := CodeCert.piOrigins henv hscoped hTarget closed formedA formedB
    substitutions fits originalDomain originalBody certificate bound resources
  exact ⟨result, origins _ member key result row, resultTyped⟩

end

def NormalFunction : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, atom => ∃ key output, AdapterNormal.atom atom = AtomData.fn key output

theorem PiProfileOrigins.value_shape
    {value : Profile n} {atom : Atom n}
    (origins : PiProfileOrigins current fuel env U registry target locals σ available A B (profile : Profile n))
    (typed : value.HasType profile)
    (member : atom ∈ value.atoms) : NormalFunction atom := by
  induction n with
  | zero =>
    obtain ⟨cover, hm, _⟩ := typed atom member
    exact (origins cover hm).elim
  | succ n ih =>
    obtain ⟨cover, hm, ht⟩ := typed.2.2 atom member
    have origin := origins cover hm
    cases cover with
    | sort | fn | family | ctor | record => exact origin.elim
    | pi protoDomain protoBody domain rows =>
      cases atom with
      | sort | pi | pad | family | ctor | record => contradiction
      | fn key output => exact ⟨AdapterNormal.key key, AdapterNormal.atom output, rfl⟩
    | pad cover =>
      cases atom with
      | sort | fn | pi | family | ctor | record => contradiction
      | pad atom =>
        have smaller : PiProfileOrigins current fuel env U registry target locals σ available A B
            (Profile.singleton cover) := by
          intro a hm
          cases List.mem_singleton.mp hm
          exact origin
        have shape := ih smaller ht (List.mem_singleton_self _)
        cases n with
        | zero => exact shape.elim
        | succ n =>
          obtain ⟨key, output, he⟩ := shape
          refine ⟨AdapterNormal.shiftKey key, AdapterNormal.shiftAtom output, ?_⟩
          rw [AdapterNormal.atom_pad, he]
          rfl

end Lean4Lean.AnchoredSource.Adapted.Staged
