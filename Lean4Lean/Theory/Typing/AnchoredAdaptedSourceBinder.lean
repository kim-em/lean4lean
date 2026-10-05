import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFundamental
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRenaming
import Lean4Lean.Theory.Typing.AnchoredVariableTransfer

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem available_shift
    (h : Footprint.Available footprint available) :
    Footprint.Available (footprint.sourceLift (.skip .refl)) (Valuation.push head available) := by
  intro i need hm
  obtain ⟨⟨j, original⟩, hj, he⟩ := List.mem_map.mp hm
  cases he
  exact h _ _ hj

noncomputable def CodeCert.lower {N : Nat}
    {profile : Profile N}
    (cert : CodeCert env U registry target locals realization expression profile footprint)
    (n : Nat) (bound : n ≤ N) :
    CodeCert env U registry target locals realization expression (lowerProfile n bound profile) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact cert
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self] using cert
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      exact ih cert.down hn

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
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {left right : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (fits : Fits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst left) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Fits env U registry (A :: source) target (Locals.push locals)
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
    have certificate := (domain.lower need.rank hn).renameSource (.skip .refl)
      (left.cons x) rfl (Locals.push locals)
    refine ⟨⟨_, _, ?_, available_shift domainAvailable, ht, ?_⟩⟩
    · simpa only [← lift_eq_lift'] using certificate
    · simpa only [Subst.cons, lift_subst_cons] using hl
  | succ lookup =>
    obtain ⟨entry⟩ := fits.entry _ need hm _ lookup
    have certificate := entry.certificate.renameSource (.skip .refl)
      (left.cons x) rfl (Locals.push locals)
    refine ⟨⟨entry.support, _, ?_, available_shift entry.available, entry.typed, ?_⟩⟩
    · simpa only [← lift_eq_lift'] using certificate
    · simpa only [Subst.cons, lift_subst_cons] using entry.related

section
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation}

theorem PairedFits.pushCertificates (henv : env.Ordered)
    (hTarget : OnCtx target (env.IsType U))
    {A x y : VExpr} {input leftSupport rightSupport : Profile N}
    {leftFootprint rightFootprint : Footprint}
    (fits : PairedFits env U registry source target locals σ τ available)
    (leftDomain : CodeCert env U registry target locals σ A leftSupport leftFootprint)
    (rightDomain : CodeCert env U registry target locals τ A rightSupport rightFootprint)
    (leftAvailable : leftFootprint.Available available)
    (rightAvailable : rightFootprint.Available available)
    (leftTyped : input.HasType leftSupport) (rightTyped : input.HasType rightSupport)
    (forward : Related env U registry target x y (A.subst σ) input leftSupport)
    (backward : Related env U registry target y x (A.subst τ) input rightSupport)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available) :=
  ⟨fits.forward.push henv hTarget leftDomain leftAvailable leftTyped forward
      localNeeds bounded covered,
    fits.backward.push henv hTarget rightDomain rightAvailable rightTyped backward
      localNeeds bounded covered⟩

end

theorem PairedFits.push
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (closed : available.AtomClosed)
    (originalDomain : Transfer env U registry target locals σ τ
      available A A (.sort level))
    (fits : PairedFits env U registry source target locals σ τ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available) := by
  obtain ⟨rightDomain⟩ := domain.transfer henv hscoped hTarget closed
    originalDomain domainAvailable
  exact fits.pushCertificates henv hTarget domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered

theorem PairedFits.pushDiagonal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    {A x : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (fits : PairedFits env U registry source target locals σ σ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (argument : Related env U registry target x x (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (σ.cons x) (Valuation.push localNeeds available) :=
  .diagonal (fits.forward.push henv hTarget domain domainAvailable typed argument
    localNeeds bounded covered)

end Lean4Lean.AnchoredSource.Adapted
