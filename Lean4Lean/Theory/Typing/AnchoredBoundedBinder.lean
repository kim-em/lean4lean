import Lean4Lean.Theory.Typing.AnchoredBoundedCode
import Lean4Lean.Theory.Typing.AnchoredNativeDepthRenaming

/-! Dependent paired substitution extension at unchanged native fuel. Each
local entry retains an actual lowered and source-lifted domain certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem available_shift
    (h : Footprint.Available footprint available) :
    Footprint.Available (footprint.sourceLift (.skip .refl)) (Valuation.push head available) := by
  intro i need hm
  obtain ⟨⟨j, original⟩, hj, he⟩ := List.mem_map.mp hm
  cases he
  exact h _ _ hj

private noncomputable def liftCertificate
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (anchor : VExpr) :
    CodeCert env U registry target (Locals.push locals) (σ.cons anchor) expression.lift
      profile (footprint.sourceLift (.skip .refl)) :=
  (lift_eq_lift' (e := expression)).symm ▸
    certificate.renameSource (.skip .refl) (σ.cons anchor) rfl (Locals.push locals)

private theorem liftCertificate_depth (current : Name → Bool)
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (anchor : VExpr) :
    (liftCertificate certificate anchor).nativeDepth current = certificate.nativeDepth current := by
  unfold liftCertificate
  rw [CodeCert.nativeDepth_rec current (lift_eq_lift' (e := expression)).symm
    (fun _ => Locals.push locals) (fun _ => σ.cons anchor) (fun e => e)
    (fun _ => profile) (fun _ => footprint.sourceLift (.skip .refl))]
  exact certificate.nativeDepth_renameSource current _ _ _ _

private theorem typed_subset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom hm => typed atom (subset atom hm)
  | succ n => exact ⟨fun atom hm => typed.1 atom (subset atom hm), typed.2.1,
      fun atom hm => typed.2.2 atom (subset atom hm)⟩

/-- A paired argument at the full packed input supplies precisely the fixed
list of local leaf demands. The grade bounds also cover empty leaf demands;
no new source observation is inferred from target relatedness. -/
theorem Fits.push
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {left right : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (fits : Fits current fuel env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A support domainFootprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst left) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Fits current fuel env U registry (A :: source) target (Locals.push locals)
      (left.cons x) (right.cons y) (Valuation.push localNeeds available) := by
  constructor
  intro index need hm sourceType lookup
  cases lookup with
  | zero =>
    have hn := bounded need hm
    have hc := covered need hm
    simp only [Need.atGrade, dif_pos hn] at hc
    have ht := lowerProfile.hasType hn (typed_subset hc typed)
    have hr : Related env U registry target x y (A.subst left)
        (raiseProfile N hn need.profile) support :=
      Related.of_singletons (fun atom hatom => arguments.singleton_of_mem (hc atom hatom))
    have hl := lowerProfile.related hn henv hTarget hr
    refine ⟨⟨_, _, liftCertificate (domain.lower need.rank hn) x, available_shift domainAvailable, ht, ?_⟩, ?_⟩
    · simpa only [Subst.cons, lift_subst_cons] using hl
    · simpa only [liftCertificate_depth, CodeCert.nativeDepth_lower] using domainBound
  | succ lookup =>
    obtain ⟨entry, entryBound⟩ := fits.entry _ need hm _ lookup
    refine ⟨⟨entry.support, _, liftCertificate entry.certificate x, available_shift entry.available, entry.typed, ?_⟩, ?_⟩
    · simpa only [Subst.cons, lift_subst_cons] using entry.related
    · simpa only [liftCertificate_depth] using entryBound

section
variable {current : Name → Bool} {fuel : Nat} {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation}

theorem PairedFits.pushCertificates (henv : env.Ordered)
    (hTarget : OnCtx target (env.IsType U))
    {A x y : VExpr} {input leftSupport rightSupport : Profile N}
    {leftFootprint rightFootprint : Footprint}
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (leftDomain : CodeCert env U registry target locals σ A leftSupport leftFootprint)
    (rightDomain : CodeCert env U registry target locals τ A rightSupport rightFootprint)
    (leftBound : leftDomain.nativeDepth current ≤ fuel)
    (rightBound : rightDomain.nativeDepth current ≤ fuel)
    (leftAvailable : leftFootprint.Available available)
    (rightAvailable : rightFootprint.Available available)
    (leftTyped : input.HasType leftSupport) (rightTyped : input.HasType rightSupport)
    (forward : Related env U registry target x y (A.subst σ) input leftSupport)
    (backward : Related env U registry target y x (A.subst τ) input rightSupport)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits current fuel env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available) :=
  ⟨fits.forward.push henv hTarget leftDomain leftBound leftAvailable leftTyped forward
      localNeeds bounded covered,
    fits.backward.push henv hTarget rightDomain rightBound rightAvailable rightTyped backward
      localNeeds bounded covered⟩

end

theorem PairedFits.pushGraded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (closed : available.AtomClosed)
    (originalDomain : Transfer current fuel env U registry target locals σ τ
      available A A (.sort level))
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits current fuel env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available) := by
  obtain ⟨rightDomain⟩ := originalDomain.codeCertificate henv hscoped hTarget closed domain domainBound domainAvailable
  exact fits.pushCertificates henv hTarget domain rightDomain.certificate
    domainBound rightDomain.certificateBound domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered

end Lean4Lean.AnchoredSource.Adapted.Staged
