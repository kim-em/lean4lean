import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainRequest

/-! Exact domain provenance for literal source Pis. Domain-only queries
survive every certificate wrapper. Hereditary input maps use the finite
focusMinimal constructor, preserving the caller's available valuation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def PiDomainAtomOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A : VExpr) : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi _ _ domain _ =>
      Nonempty (CertificateResult env U registry target locals σ available A domain)
  | _ + 1, .pad atom => PiDomainAtomOrigins env U registry target locals σ available A atom
  | _ + 1, _ => False

def PiDomainOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A : VExpr) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, PiDomainAtomOrigins env U registry target locals σ available A atom

private theorem PiDomainAtomOrigins.view {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origin : PiDomainAtomOrigins env U registry target locals σ available A a) :
    PiDomainAtomOrigins env U registry target locals σ available A b := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origin
  | _ + 1, _, _, .reanchor _ => cases origin
  | _ + 1, _, _, .domainRekey _ _ _ _ => cases origin
  | _ + 1, _, _, .input _ _ => cases origin
  | _ + 2, _, _, .commutePadFn _ _ => cases origin
  | _ + 2, _, _, .uncommutePadFn _ _ => cases origin
  | _ + 1, _, _, .fn _ _ => cases origin
  | k + 1, _, _, .pad child => exact PiDomainAtomOrigins.view (n := k) child origin
  | _, _, _, .trans first second => exact (origin.view first).view second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem Obs.piDomainOrigins
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    PiDomainOrigins env U registry target locals σ available A profile := by
  match observation with
  | .empty => exact fun _ member => nomatch member
  | .pi domain _ _ =>
    intro atom member
    cases List.mem_singleton.mp member
    exact ⟨⟨_, domain, fun i need hm => resources i need (List.mem_append_left _ hm)⟩⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins (fun i need hm => resources i need
        (List.mem_append_left _ hm)) atom member
    · exact right.piDomainOrigins (fun i need hm => resources i need
        (List.mem_append_right _ hm)) atom member
  | .view source change =>
    intro atom member
    cases List.mem_singleton.mp member
    exact (source.piDomainOrigins resources _ (List.mem_singleton_self _)).view change
  | .pad source =>
    intro atom member
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
    exact source.piDomainOrigins resources old hm
  | .unpad source =>
    intro atom member
    exact source.piDomainOrigins resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .rowShift source =>
    have impossible := source.piDomainOrigins resources _ (List.mem_singleton_self _)
    cases impossible
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

private theorem PiDomainOrigins.pad
    (origins : PiDomainOrigins env U registry target locals σ available A profile) :
    PiDomainOrigins env U registry target locals σ available A profile.pad := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  exact origins old hm

private theorem PiDomainOrigins.down
    (origins : PiDomainOrigins env U registry target locals σ available A (profile : Profile (n + 1))) :
    PiDomainOrigins env U registry target locals σ available A profile.down := by
  intro atom member
  obtain ⟨old, hm, member⟩ := List.mem_flatMap.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pi => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

private theorem PiDomainOrigins.rankShift
    (origins : PiDomainOrigins env U registry target locals σ available A (profile : Profile (n + 1))) :
    PiDomainOrigins env U registry target locals σ available A profile.rankShift := by
  intro atom member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  have origin := origins old hm
  cases old with
  | sort | fn | family | ctor | record => cases origin
  | pad a => exact origin
  | pi protoA protoB domain rows =>
    obtain ⟨result⟩ := origin
    exact ⟨⟨_, .pad result.certificate, result.resources⟩⟩

private theorem PiDomainOrigins.unshift
    (origins : PiDomainOrigins env U registry target locals σ available A (profile : Profile (n + 2)))
    (key : Key n) :
    PiDomainOrigins env U registry target locals σ available A (profile.unshift key) := by
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

private theorem CertificateResult.mapProfile
    (result : CertificateResult env U registry target locals σ available A support)
    (change : ProfileView env U registry target input output) :
    Nonempty (CertificateResult env U registry target locals σ available A (change.mapType support)) := by
  match change with
  | .nil => exact ⟨result⟩
  | .cons head tail =>
    obtain ⟨next⟩ := result.mapProfile tail
    exact ⟨⟨_, .union (.map head result.certificate) next.certificate, fun i need hm =>
      (List.mem_append.mp hm).elim (result.resources i need) (next.resources i need)⟩⟩
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem CertificateResult.unions (profiles : List (Profile n))
    (certificates : ∀ profile ∈ profiles,
      Nonempty (CertificateResult env U registry target locals σ available A profile)) :
    Nonempty (CertificateResult env U registry target locals σ available A (Profile.unions profiles)) := by
  induction profiles with
  | nil => exact ⟨⟨[], .seed .empty (.empty (Profile.WF.sort true)), by intro _ _ member; cases member⟩⟩
  | cons profile profiles ih =>
    obtain ⟨first⟩ := certificates profile List.mem_cons_self
    obtain ⟨rest⟩ := ih (fun other member => certificates other (List.mem_cons_of_mem _ member))
    exact ⟨⟨_, .union first.certificate rest.certificate, fun i need hm =>
      (List.mem_append.mp hm).elim (first.resources i need) (rest.resources i need)⟩⟩

private theorem CertificateResult.inputDomain
    (result : CertificateResult env U registry target locals σ available A support)
    (backward : ProfileView env U registry target input output) :
    Nonempty (CertificateResult env U registry target locals σ available A
      (inputDomain input backward.mapType support)) := by
  obtain ⟨extra⟩ := CertificateResult.unions ((Basis input support).map backward.mapType) (by
    intro profile member
    obtain ⟨focused, selected, rfl⟩ := List.mem_map.mp member
    let focus : CertificateResult env U registry target locals σ available A focused :=
      ⟨_, .focusMinimal result.certificate (Basis.minimal selected) (Basis.valid selected).2,
        result.resources⟩
    exact focus.mapProfile backward)
  exact ⟨⟨_, .union result.certificate extra.certificate, fun i need hm =>
    (List.mem_append.mp hm).elim (result.resources i need) (extra.resources i need)⟩⟩

private theorem PiDomainOrigins.map {a b : Atom n}
    (change : AtomView env U registry target a b)
    (origins : PiDomainOrigins env U registry target locals σ available A profile) :
    PiDomainOrigins env U registry target locals σ available A (change.mapType profile) := by
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
      change PiDomainAtomOrigins _ _ _ _ _ _ _ _ (if _ then _ else _)
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

private theorem PiDomainOrigins.focusMinimal
    {value focused : Profile n} (minimal : Minimal value focused)
    {bound : Profile n} (dominated : focused ≤ bound)
    (origins : PiDomainOrigins env U registry target locals σ available A bound) :
    PiDomainOrigins env U registry target locals σ available A focused := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ support _ => ∀ {bound}, support ≤ bound →
        PiDomainOrigins env U registry target locals σ available A bound →
        PiDomainOrigins env U registry target locals σ available A support) with
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
    exact ⟨⟨_, .focusMinimal source.certificate hi domainBound, source.resources⟩⟩
  | pad lower ih =>
    rename_i bound dominated origins
    apply PiDomainOrigins.pad
    apply ih (bound := bound.down)
    · simpa only [Profile.down_pad] using dominated.down
    · exact origins.down

/-- Exact ambient domain extraction, including empty Pi row tables. No
original domain/codomain interpretation, inhabitant, or argument is needed. -/
theorem CodeCert.piDomainOrigins
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    PiDomainOrigins env U registry target locals σ available A profile := by
  match certificate with
  | .seed observation _ => exact observation.piDomainOrigins resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins (fun i need hm => resources i need
        (List.mem_append_left _ hm)) atom member
    · exact right.piDomainOrigins (fun i need hm => resources i need
        (List.mem_append_right _ hm)) atom member
  | .pad source => exact (source.piDomainOrigins resources).pad
  | .familyPad source => exact False.elim (source.piDomainOrigins resources _ (List.mem_singleton_self _))
  | .unpad source =>
    intro atom member
    exact source.piDomainOrigins resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source => exact (source.piDomainOrigins resources).down
  | .map change source => exact (source.piDomainOrigins resources).map change
  | .select source selected =>
    intro atom member
    cases List.mem_singleton.mp member
    exact source.piDomainOrigins resources _ selected
  | .focusMinimal source minimal dominated =>
    exact (source.piDomainOrigins resources).focusMinimal minimal dominated
termination_by sizeOf certificate

theorem CodeCert.piDomain
    (certificate : CodeCert env U registry target locals σ (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody domain rows) footprint)
    (resources : footprint.Available available) :
    Nonempty (CertificateResult env U registry target locals σ available A domain) :=
  certificate.piDomainOrigins resources _ (List.mem_singleton_self _)

namespace OriginalFactorCut

/-- Exact source-domain code and a raw target-domain path are recovered from
the same transported Pi query. The path remains available at empty support;
no source typing at a reconstructed declared domain is assumed. -/
theorem CodeCoherence.piDomainAlignment
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B C D : VExpr} {support : Profile n} {footprint : Footprint}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (coherence : CodeCoherence env U registry target locals σ available
      (.forallE A B) (.forallE C D))
    (certificate : CodeCert env U registry target locals σ A support footprint)
    (resources : footprint.Available available) :
    ∃ _result : CodeTransferResult env U registry target locals σ σ available A C support,
      TypeConversion env U target (A.subst σ) (C.subst σ) := by
  obtain ⟨result, domains⟩ := coherence.domainQuery henv hscoped hTarget certificate resources
  obtain ⟨domain⟩ := result.certificate.piDomain result.available
  exact ⟨⟨domain.footprint, domain.certificate, domain.resources, domains⟩,
    TypeRelated.literalPiDomainPath henv hTarget (by simpa only [subst] using result.related)⟩

/-- The smaller original function comparison transports an arbitrary domain
query exactly. Source-domain extraction keeps all wrappers and preserves the
same available valuation. -/
theorem CodeCoherence.piDomains
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B C D : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (coherence : CodeCoherence env U registry target locals σ available
      (.forallE A B) (.forallE C D)) :
    CodeCoherence env U registry target locals σ available A C := by
  intro n support footprint certificate resources
  obtain ⟨result, _⟩ := coherence.piDomainAlignment henv hscoped hTarget certificate resources
  exact ⟨result⟩

end OriginalFactorCut
end Lean4Lean.AnchoredSource.Adapted
