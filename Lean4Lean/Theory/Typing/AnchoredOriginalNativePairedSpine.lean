import Lean4Lean.Theory.Typing.AnchoredOriginalNativeCertificateSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameFuture
import Lean4Lean.Theory.Typing.AnchoredNativeProofCapture

/-! Paired native replay retains the finite certificates through the SAME
actual proof insertion. Source proposition formation is used only for raw
substitution and proof irrelevance, never as an unrestricted semantic call. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
open private renamedBound renamedCoverage from Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFuture
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def NativeCertificateSpine.future
    {future : List VExpr}
    (henv : env.Ordered) (insertion : FutureInsertion env U target future ρ)
    (spine : NativeCertificateSpine env U registry target source σ τ available) :
    NativeCertificateSpine env U registry future source
      (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available) := by
  induction spine with
  | nil => exact .nil
  | cons previous certificate resources typed arguments needs bounded covered ih =>
    simpa only [subst_cons_future, Valuation.rename_push, lift'_subst] using
      NativeCertificateSpine.cons ih (certificate.future henv insertion) (resources.rename ρ)
        (Profile.rename_hasType_iff.mpr typed) (by
          simpa only [lift'_subst] using arguments.future henv insertion)
        (needs.map (Need.rename ρ)) (renamedBound needs ρ bounded) (renamedCoverage needs ρ covered)

structure NativeProofSpineResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (σ τ : Subst) (available : Valuation)
    (domain witness : VExpr) (needs : List Need) where
  insertion : ProofInsertion env U target (domain.subst τ :: target) (.skip .refl)
  substitutions : Ctx.SubstEq env U (domain.subst τ :: target)
    ((σ.lift_r (.skip .refl)).cons witness.lift)
    ((τ.lift_r (.skip .refl)).cons (.bvar 0)) (domain :: source)
  spine : NativeCertificateSpine env U registry (domain.subst τ :: target) (domain :: source)
    ((σ.lift_r (.skip .refl)).cons witness.lift)
    ((τ.lift_r (.skip .refl)).cons (.bvar 0))
    (Valuation.push needs (Valuation.rename (.skip .refl) available))

noncomputable def NativeCertificateSpine.openProof
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (spine : NativeCertificateSpine env U registry target source σ τ available)
    (formation : env.HasType U source domain (.sort .zero))
    (inhabitant : env.HasType U target witness (domain.subst σ))
    (needs : List Need) (n : Nat) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (empty : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, False) :
    NativeProofSpineResult env U registry source target σ τ available domain witness needs := by
  have domains := formation.substDF henv substitutions.wf formed substitutions
  have canonicalWitness := IsDefEq.defeqDF domains inhabitant
  let insertion : ProofInsertion env U target (domain.subst τ :: target) (.skip .refl) :=
    .skip (.refl formed) domains.hasType.2 canonicalWitness
  have rawPair : env.IsDefEq U (domain.subst τ :: target) witness.lift (.bvar 0)
      (domain.subst (σ.lift_r (.skip .refl))) := by
    have proofDomain := domains.hasType.1.weak (B := domain.subst τ) henv
    have oldWitness := inhabitant.weak (B := domain.subst τ) henv
    have newWitness : env.HasType U (domain.subst τ :: target) (.bvar 0)
        (domain.subst σ).lift := .defeqDF (domains.symm.weak henv) (.bvar .zero)
    simpa only [← lift'_subst, ← lift_eq_lift'] using
      IsDefEq.proofIrrel proofDomain oldWitness newWitness
  have certificate : CodeCert env U registry (domain.subst τ :: target) (List.range source.length)
      (σ.lift_r (.skip .refl)) domain (Profile.empty (n := n)) [] :=
    .seed .empty (.empty (.sort true))
  have related : Related env U registry (domain.subst τ :: target) witness.lift (.bvar 0)
      (domain.subst (σ.lift_r (.skip .refl))) (Profile.empty (n := n)) .empty := by
    apply Related.of_singletons
    intro atom member
    cases member
  exact ⟨insertion, .cons (substitutions.future henv insertion.toFuture) formation rawPair,
    .cons (spine.future henv insertion.toFuture) certificate (fun _ _ h => nomatch h)
      (.empty .empty) related needs bounded (fun need hm atom ha => (empty need hm atom ha).elim)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
