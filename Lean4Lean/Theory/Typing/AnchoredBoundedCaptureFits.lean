import Lean4Lean.Theory.Typing.AnchoredBoundedBinder
import Lean4Lean.Theory.Typing.AnchoredBoundedReflection
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture
import Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay

/-! The actual common-prefix and inhabited-proof steps of native replay
preserve the same source-certificate fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The full native lookup type is literally the lifted prefix lookup type.
Reflecting that source certificate retains exactly its original leaves. -/
theorem Fits.nativeTail
    (fits : Fits current fuel env U registry (A :: source) target locals σ τ available)
    (prefixLocals : List Nat) :
    Fits current fuel env U registry source target prefixLocals σ.tail τ.tail
      (fun index => available (index + 1)) := by
  constructor
  intro index need member type lookup
  obtain ⟨entry, entryBound⟩ := fits.entry (index + 1) need member type.lift (.succ lookup)
  obtain ⟨footprint, certificate, hf, certificateBound⟩ := entry.certificate.reflectSourceBounded (.skip .refl)
    lift_eq_lift' prefixLocals entryBound
  refine ⟨{
    support := entry.support
    footprint := footprint
    certificate := certificate
    available := ?_
    typed := entry.typed
    related := ?_ }, certificateBound⟩
  · intro i needed hm
    apply entry.available (i + 1) needed
    rw [hf]
    exact List.mem_map.mpr ⟨(i, needed), hm, rfl⟩
  · have he : Subst.lift_l (.skip .refl) σ = σ.tail := rfl
    simpa only [lift_eq_lift', subst_lift', he, Subst.tail] using entry.related

theorem PairedFits.nativeTail
    (fits : PairedFits current fuel env U registry (A :: source) target locals σ τ available)
    (prefixLocals : List Nat) :
    PairedFits current fuel env U registry source target prefixLocals σ.tail τ.tail
      (fun index => available (index + 1)) :=
  ⟨fits.forward.nativeTail prefixLocals, fits.backward.nativeTail prefixLocals⟩

/-- Drop the later formal arguments in one finite pass. This is the exact
prefix restriction required by a natural-domain native guard. -/
theorem PairedFits.nativePrefix
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {later source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation}
    (fits : PairedFits current fuel env U registry (later ++ source) target locals σ τ available)
    (prefixLocals : List Nat) :
    PairedFits current fuel env U registry source target prefixLocals
      (Subst.lift_l (.skipN .refl later.length) σ)
      (Subst.lift_l (.skipN .refl later.length) τ)
      (fun index => available (index + later.length)) := by
  induction later generalizing locals σ τ available with
  | nil =>
    change PairedFits current fuel env U registry source target prefixLocals σ τ available
    constructor <;> constructor
    · intro index need member type lookup
      obtain ⟨entry, bound⟩ := fits.forward.entry index need member type lookup
      obtain ⟨footprint, certificate, same, certificateBound⟩ :=
        entry.certificate.reflectSourceBounded .refl (lift'_refl (e := type)).symm prefixLocals bound
      refine ⟨⟨entry.support, footprint, certificate, ?_, entry.typed, entry.related⟩, certificateBound⟩
      intro i need hm
      apply entry.available i need
      rw [same]
      exact List.mem_map.mpr ⟨(i, need), hm, rfl⟩
    · intro index need member type lookup
      obtain ⟨entry, bound⟩ := fits.backward.entry index need member type lookup
      obtain ⟨footprint, certificate, same, certificateBound⟩ :=
        entry.certificate.reflectSourceBounded .refl (lift'_refl (e := type)).symm prefixLocals bound
      refine ⟨⟨entry.support, footprint, certificate, ?_, entry.typed, entry.related⟩, certificateBound⟩
      intro i need hm
      apply entry.available i need
      rw [same]
      exact List.mem_map.mpr ⟨(i, need), hm, rfl⟩
  | cons A later ih =>
    have restricted := ih (fits.nativeTail prefixLocals)
    have shift (ρ : Subst) : Subst.lift_l (.skipN .refl later.length) ρ.tail =
        Subst.lift_l (.skipN .refl (later.length + 1)) ρ := by
      funext i
      simp [Subst.lift_l, Subst.tail, Lift.liftVar_skipN, Lift.liftVar, Nat.add_assoc]
    simpa only [List.length_cons, shift, Nat.add_assoc] using restricted

/-- Source proposition formation is essential here: target-only proposition
typing at the witnessed endpoint would not transport across arbitrary
predecessor captures without a type-uniqueness theorem. -/
theorem PairedFits.openNativeProof
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {domain witness : VExpr}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (formation : env.HasType U source domain (.sort .zero))
    (inhabitant : env.HasType U target witness (domain.subst σ))
    (localNeeds : List Need) (n : Nat)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (empty : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade n).atoms, False) :
    ProofInsertion env U target (domain.subst τ :: target) (.skip .refl) ∧
    Ctx.SubstEq env U (domain.subst τ :: target)
      ((σ.lift_r (.skip .refl)).cons witness.lift)
      ((τ.lift_r (.skip .refl)).cons (.bvar 0)) (domain :: source) ∧
    PairedFits current fuel env U registry (domain :: source) (domain.subst τ :: target)
      (Locals.push locals)
      ((σ.lift_r (.skip .refl)).cons witness.lift)
      ((τ.lift_r (.skip .refl)).cons (.bvar 0))
      (Valuation.push localNeeds (Valuation.rename (.skip .refl) available)) := by
  have domains := formation.substDF henv substitutions.wf hTarget substitutions
  have canonicalWitness := IsDefEq.defeqDF domains inhabitant
  have insertion : ProofInsertion env U target (domain.subst τ :: target) (.skip .refl) :=
    .skip (.refl hTarget) domains.hasType.2 canonicalWitness
  have newTarget := insertion.targetWF henv
  have previous := substitutions.future henv insertion.toFuture
  have rawPair : env.IsDefEq U (domain.subst τ :: target) witness.lift (.bvar 0)
      (domain.subst (σ.lift_r (.skip .refl))) := by
    have proofDomain := domains.hasType.1.weak (B := domain.subst τ) henv
    have oldWitness := inhabitant.weak (B := domain.subst τ) henv
    have newWitness : env.HasType U (domain.subst τ :: target) (.bvar 0)
        (domain.subst σ).lift :=
      .defeqDF (domains.symm.weak henv) (.bvar .zero)
    simpa only [← lift'_subst, ← lift_eq_lift'] using
      IsDefEq.proofIrrel proofDomain oldWitness newWitness
  refine ⟨insertion, .cons previous formation rawPair, ?_⟩
  have previousFits := fits.future henv insertion.toFuture
  let leftCert : CodeCert env U registry (domain.subst τ :: target) locals
      (σ.lift_r (.skip .refl)) domain (Profile.empty (n := n)) [] :=
    .seed .empty (.empty (.sort true))
  let rightCert : CodeCert env U registry (domain.subst τ :: target) locals
      (τ.lift_r (.skip .refl)) domain (Profile.empty (n := n)) [] :=
    .seed .empty (.empty (.sort true))
  have leftRelated : Related env U registry (domain.subst τ :: target) witness.lift (.bvar 0)
      (domain.subst (σ.lift_r (.skip .refl))) (Profile.empty (n := n)) .empty := by
    apply Related.of_singletons
    intro atom member
    cases member
  have rightRelated : Related env U registry (domain.subst τ :: target) (.bvar 0) witness.lift
      (domain.subst (τ.lift_r (.skip .refl))) (Profile.empty (n := n)) .empty := by
    apply Related.of_singletons
    intro atom member
    cases member
  exact previousFits.pushCertificates henv newTarget leftCert rightCert
    (by simp only [leftCert, CodeCert.nativeDepth, Obs.nativeDepth]; omega)
    (by simp only [rightCert, CodeCert.nativeDepth, Obs.nativeDepth]; omega)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (.empty .empty) (.empty .empty) leftRelated rightRelated localNeeds bounded
    (fun need member atom atomMember => (empty need member atom atomMember).elim)


end Lean4Lean.AnchoredSource.Adapted.Staged
