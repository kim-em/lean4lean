import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGrades
import Lean4Lean.Theory.Typing.AnchoredGradedAdapters

/-! Graded computational transfer restores code demands at their exact
original grade before extending a paired source substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem CodeCert.transfer_graded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {leftSubst rightSubst : Subst} {available : Valuation}
    {left right sourceType : VExpr}
    (closed : available.AtomClosed)
    (original : GradedTransfer env U registry target locals leftSubst rightSubst
      available left right sourceType)
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry target locals leftSubst left profile footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst rightSubst
      available left right profile) := by
  match cert with
  | .seed observation formed =>
    obtain ⟨result⟩ := original observation resources
    obtain ⟨footprint, ⟨certificate⟩, _, available⟩ :=
      result.observation.codeCert_of_adapter henv result.adapter
        (AnchoredSemantics.Profile.HasType.raise_sort result.bound formed) result.resultAvailable closed
    exact ⟨⟨footprint, certificate.lowerRaised result.bound, available,
      (result.requestedRelated henv hTarget).code_of_sortable henv hscoped hTarget formed⟩⟩
  | .union left right =>
    obtain ⟨hl⟩ := left.transfer_graded henv hscoped hTarget closed original
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := right.transfer_graded henv hscoped hTarget closed original
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨⟨hl.footprint ++ hr.footprint, .union hl.certificate hr.certificate, ?_, ?_⟩⟩
    · intro i need hm
      exact (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
    · apply TypeRelated.of_singletons
      intro atom hm
      exact (List.mem_append.mp hm).elim
        (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .pad result.certificate, result.available,
      result.related.pad henv⟩⟩
  | .familyPad source =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .familyPad result.certificate, result.available,
      result.related.familyPad henv⟩⟩
  | .unpad source =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .unpad result.certificate, result.available,
      (TypeRelated.pad_iff henv).mp result.related⟩⟩
  | .down source =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .down result.certificate, result.available,
      result.related.down henv⟩⟩
  | .map view source =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .map view result.certificate, result.available,
      view.codeMap henv hscoped result.related⟩⟩
  | .select source member =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .select result.certificate member, result.available,
      result.related.singleton member⟩⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨result⟩ := source.transfer_graded henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .focusMinimal result.certificate minimal focusedBound, result.available,
      result.related.focusMinimal henv minimal focusedBound⟩⟩
termination_by sizeOf cert

theorem PairedFits.pushGraded
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (closed : available.AtomClosed)
    (originalDomain : GradedTransfer env U registry target locals σ τ
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
  obtain ⟨rightDomain⟩ := domain.transfer_graded henv hscoped hTarget closed
    originalDomain domainAvailable
  exact fits.pushCertificates henv hTarget domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered

end Lean4Lean.AnchoredSource.Adapted
