import Lean4Lean.Theory.Typing.AnchoredBoundedVariable
import Lean4Lean.Theory.Typing.AnchoredBoundedPruning

/-! Actual certificate transfer at the same declaration-stage fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure CodeResult (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right : VExpr) (profile : Profile n)
    extends CodeTransferResult env U registry target locals leftSubst rightSubst available left right profile where
  certificateBound : certificate.nativeDepth current ≤ fuel

theorem Transfer.codeCertificate
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {leftSubst rightSubst : Subst} {available : Valuation}
    {left right sourceType : VExpr}
    (closed : available.AtomClosed)
    (original : Transfer current fuel env U registry target locals leftSubst rightSubst
      available left right sourceType)
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry target locals leftSubst left profile footprint)
    (bound : cert.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (CodeResult current fuel env U registry target locals leftSubst rightSubst
      available left right profile) := by
  match cert with
  | .seed observation formed =>
    obtain ⟨result⟩ := original observation (by simpa only [CodeCert.nativeDepth] using bound) resources
    obtain ⟨footprint, certificate, _, available, certificateBound⟩ :=
      result.observation.codeCert_of_adapter_bounded (current := current) henv result.adapter
        (AnchoredSemantics.Profile.HasType.raise_sort result.bound formed) result.resultAvailable closed
    exact ⟨{
      footprint := footprint
      certificate := certificate.lowerRaised result.bound
      available := available
      related := (result.toGradedTransferResult.requestedRelated henv hTarget).code_of_sortable henv hscoped hTarget formed
      certificateBound := by simpa only [CodeCert.nativeDepth_lowerRaised] using Nat.le_trans certificateBound result.observationBound }⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max (left.nativeDepth current) (right.nativeDepth current) ≤ fuel by simpa only [CodeCert.nativeDepth] using bound)
    obtain ⟨hl⟩ := original.codeCertificate henv hscoped hTarget closed left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := original.codeCertificate henv hscoped hTarget closed right bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨{footprint := hl.footprint ++ hr.footprint, certificate := .union hl.certificate hr.certificate, available := ?_, related := ?_, certificateBound := ?_}⟩
    · intro i need hm
      exact (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
    · apply TypeRelated.of_singletons
      intro atom hm
      exact (List.mem_append.mp hm).elim
        (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
    · simpa only [CodeCert.nativeDepth] using Nat.max_le.mpr ⟨hl.certificateBound, hr.certificateBound⟩
  | .pad source =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .pad result.certificate, result.available,
      result.related.pad henv⟩, by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
  | .familyPad source =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source
      (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .familyPad result.certificate, result.available,
      result.related.familyPad henv⟩,
      by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
  | .unpad source =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .unpad result.certificate, result.available,
      (TypeRelated.pad_iff henv).mp result.related⟩, by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
  | .down source =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .down result.certificate, result.available,
      result.related.down henv⟩, by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
  | .map view source =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .map view result.certificate, result.available,
      view.codeMap henv hscoped result.related⟩, by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
  | .select source member =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .select result.certificate member, result.available,
      result.related.singleton member⟩, by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨result⟩ := original.codeCertificate henv hscoped hTarget closed source (by simpa only [CodeCert.nativeDepth] using bound) resources
    exact ⟨⟨⟨result.footprint, .focusMinimal result.certificate minimal focusedBound, result.available,
      result.related.focusMinimal henv minimal focusedBound⟩, by simpa only [CodeCert.nativeDepth] using result.certificateBound⟩⟩
termination_by sizeOf cert

end Lean4Lean.AnchoredSource.Adapted.Staged
