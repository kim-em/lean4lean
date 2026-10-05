import Lean4Lean.Theory.Typing.AnchoredNativeCaptureGuard
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBinder

/-! The proof-field step of witnessed-to-canonical native replay. A fresh
proof is opened only after obtaining an actual inhabitant of its exact
canonical domain. Both raw substitutions and finite fitting entries move
through that same generated proof insertion. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Source proposition formation is essential here: target-only proposition
typing at the witnessed endpoint would not transport across arbitrary
predecessor captures without a type-uniqueness theorem. -/
theorem PairedFits.openNativeProof
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {domain witness : VExpr}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (formation : env.HasType U source domain (.sort .zero))
    (inhabitant : env.HasType U target witness (domain.subst σ))
    (localNeeds : List Need) (n : Nat)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (empty : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade n).atoms, False) :
    ProofInsertion env U target (domain.subst τ :: target) (.skip .refl) ∧
    Ctx.SubstEq env U (domain.subst τ :: target)
      ((σ.lift_r (.skip .refl)).cons witness.lift)
      ((τ.lift_r (.skip .refl)).cons (.bvar 0)) (domain :: source) ∧
    PairedFits env U registry (domain :: source) (domain.subst τ :: target)
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
  have leftCert : CodeCert env U registry (domain.subst τ :: target) locals
      (σ.lift_r (.skip .refl)) domain (Profile.empty (n := n)) [] :=
    .seed .empty (.empty (.sort true))
  have rightCert : CodeCert env U registry (domain.subst τ :: target) locals
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
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (.empty .empty) (.empty .empty) leftRelated rightRelated localNeeds bounded
    (fun need member atom atomMember => (empty need member atom atomMember).elim)

end Lean4Lean.AnchoredSource.Adapted
