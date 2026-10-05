import Lean4Lean.Theory.Typing.AnchoredBoundedPiRowTransfer
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair
import Lean4Lean.Theory.Typing.AnchoredCodeIntroduction
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule

/-! Literal source Pi observations transfer from the original domain and
codomain children. Their frozen prototype and finite row demands are retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

/-- The primitive Pi observation case, before its outer observation closures. -/
theorem Obs.pi_transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B B' protoA protoB : VExpr} {domainLevel bodyLevel : VLevel}
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    {domainFootprint rowFootprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (guard : PiGuard env U target σ A B protoA protoB)
    (body : PiRows env U registry target locals σ A B ambient rows rowFootprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (resources : rowFootprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel))
      (Profile.pi protoA protoB ambient rows)) := by
  have domainChild : Transfer current fuel env U registry target locals σ τ available A A' (.sort domainLevel) :=
    (originalDomain target locals σ τ available closed hTarget substitutions fits).1
  obtain ⟨newDomain⟩ := domainChild.codeCertificate henv hscoped hTarget closed domain domainBound domainAvailable
  obtain ⟨newRows⟩ := PiRows.transferBounded henv hscoped originalDomain originalBody domains closed hTarget
    substitutions fits domain body domainBound domainAvailable bodyBound resources
  have caps := PiRows.capabilitiesBounded henv hscoped originalDomain originalBody domains closed hTarget
    substitutions fits domain body domainBound domainAvailable bodyBound resources
  have hA := domains.hasType.1.subst henv substitutions.left hTarget
  have hA' := domains.hasType.2.subst henv (substitutions.right henv hTarget) hTarget
  have contextA : OnCtx (A.subst σ :: target) (env.IsType U) := ⟨hTarget, _, hA⟩
  have contextA' : OnCtx (A'.subst τ :: target) (env.IsType U) := ⟨hTarget, _, hA'⟩
  have sourceA : OnCtx (A :: source) (env.IsType U) := ⟨substitutions.wf, _, domains.hasType.1⟩
  have rawDomains := domains.substDF henv substitutions.wf hTarget substitutions
  have rawBodies := bodies.substDF henv sourceA contextA (substitutions.lift henv domains.hasType.1)
  have rawRight := rightBody.subst henv
    ((substitutions.right henv hTarget).lift henv domains.hasType.2) contextA'
  have guard' : PiGuard env U target τ A' B' protoA protoB := {
    domainPath := (TypeConversion.single rawDomains.symm).trans guard.domainPath
    bodyPath := TypeConversion.changeDomain henv hTarget hA' hA (.single rawDomains.symm)
      ((TypeConversion.single rawBodies.symm).trans guard.bodyPath) }
  have valueCode : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A' B').subst τ) (Profile.pi protoA protoB ambient rows) := by
    apply TypeRelated.literalPiPair henv hTarget ⟨_, hA⟩ ⟨_, hA'⟩
      ⟨_, rawBodies.hasType.1⟩ ⟨_, rawRight⟩ (.single rawDomains) (.single rawBodies)
      guard.domainPath guard.bodyPath newDomain.related
    · intro key result member
      have cap := caps key result member
      exact ⟨ambient, cap.1, domain.formed, Profile.le_refl _, cap.2.2.2.1, cap.2.2.2.2.1⟩
    · intro key result member
      exact (caps key result member).2.2.2.2.2
  have wf : (Profile.pi protoA protoB ambient rows).WF := Profile.WF.pi_iff.mpr
    ⟨domain.formed, fun key result member => ⟨(caps key result member).1, (caps key result member).2.1.wf_value⟩⟩
  have sortable : (Profile.pi protoA protoB ambient rows).HasType (.sort true) :=
    Profile.HasType.pi_iff.mpr ⟨wf, fun key result member => (caps key result member).2.1⟩
  obtain ⟨relevant, flag⟩ : ∃ relevant, Relevant bodyLevel relevant := by
    by_cases h : bodyLevel ≈ .zero
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have typed : (Profile.pi protoA protoB ambient rows).HasType (.sort relevant) :=
    Profile.HasType.pi_iff.mpr ⟨wf, fun key result member => (caps key result member).2.2.1 relevant flag⟩
  have imaxFlag : Relevant (.imax domainLevel bodyLevel) relevant := by
    cases relevant <;> simpa only [Relevant, Bool.false_eq_true, if_false, if_true,
      VLevel.imax_eq_zero] using flag
  have levelWF : (VLevel.imax domainLevel bodyLevel).WF U :=
    ⟨domains.sort_r henv substitutions.wf, bodies.sort_r henv sourceA⟩
  have typeCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n + 1) henv levelWF levelWF rfl imaxFlag
  have related := Related.of_code henv sortable typed valueCode typeCode
  exact ⟨{
    rank := n + 1, bound := Nat.le_refl _, rawDemand := Profile.pi protoA protoB ambient rows,
    resultFootprint := newDomain.footprint ++ newRows.footprint,
    observation := .pi newDomain.certificate guard' newRows.bodies,
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (newDomain.available i need) (newRows.resources i need),
    support := .sort relevant, typeFootprint := [],
    certificate := .seed (.sort imaxFlag) (Profile.HasType.sort relevant),
    typeAvailable := fun _ _ hm => (nomatch hm),
    typed := by simpa only [raiseProfile_self] using typed,
    rawTyped := typed, typeCode := typeCode,
    related := by simpa only [raiseProfile_self, subst_sort] using related,
    rawRelated := (Related.symm henv related).left_diagonal,
    observationBound := by simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨newDomain.certificateBound, newRows.bodiesBound⟩,
    certificateBound := by simp only [CodeCert.nativeDepth, Obs.nativeDepth]; omega }⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
