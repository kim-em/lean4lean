import Lean4Lean.Theory.Typing.AnchoredOriginalRichAssignedFirstFamily
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionParameters
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterSchedules

/-! Replay the retained family normalization without asserting that its
original assigned expression is a sort. Both the expression-R source and
the equality-F source are fixed original roots. The normalized Pi query is
constructed from their concrete answers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private def castCertificate
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (same : expression = other) :
    RichCert sourceEnv env U registry target (node.cast same rfl) locals σ relevant profile footprint := by
  cases same
  exact certificate

/-- The two expression endpoints of an actual equality F call. In
particular, its original assigned expression is not restricted to a sort. -/
structure OriginalEqualityQueryResult
    (original : Derivation sourceEnv U source left right assigned)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (profile : Profile n) where
  support : Profile n
  related : Related env U registry target (left.subst σ) (right.subst τ)
    (assigned.subst σ) profile support
  rightQuery : RichGradedResult sourceEnv env U registry target (.ref (.right original))
    locals τ available profile

theorem OriginalEqualityQueryResult.code
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {original : Derivation sourceEnv U source left right assigned}
    (answer : OriginalEqualityQueryResult original env registry target locals σ τ available profile)
    (sorted : profile.HasType (.sort relevant)) :
    ∃ footprint,
      Nonempty (RichCert sourceEnv env U registry target (.ref (.right original))
        locals τ relevant profile footprint) ∧
      footprint.Available available ∧
      TypeRelated env U registry target (left.subst σ) (right.subst τ) profile := by
  obtain ⟨footprint, certificate, resources⟩ := answer.rightQuery.code henv sorted
  exact ⟨footprint, certificate, resources, answer.related.code_of_sortable henv hscoped formed sorted⟩

/-- The actual right endpoint supplies the Pi route; no normalized source
certificate, domain derivation, or type uniqueness premise is provided. -/
structure NormalizedFamilyPrefix
    (packet : OriginalProjectionParameters sourceEnv U name info levels) where
  domainExpression : VExpr
  bodyExpression : VExpr
  shape : packet.shape.normalized.instL levels = .forallE domainExpression bodyExpression
  selected : PiPrefix ((Located.here (root := .right packet.instantiated.normalization)).castExpression shape)

noncomputable def normalizedFamilyPrefix
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (nonempty : 0 < info.nparams) : NormalizedFamilyPrefix packet := by
  have existsPi : ∃ A B, packet.shape.normalized = .forallE A B := by
    have take := packet.shape.familyTake
    obtain ⟨count, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt nonempty)
    rw [countEq] at take
    cases normalizedEq : packet.shape.normalized <;> simp only [normalizedEq, takeForalls] at take
    all_goals try cases take
    case forallE A B => exact ⟨A, B, rfl⟩
  let A := Classical.choose existsPi
  let B := Classical.choose (Classical.choose_spec existsPi)
  have shape : packet.shape.normalized.instL levels = .forallE (A.instL levels) (B.instL levels) := by
    rw [Classical.choose_spec (Classical.choose_spec existsPi)]
    rfl
  exact ⟨A.instL levels, B.instL levels, shape,
    piPrefix ((Located.here (root := .right packet.instantiated.normalization)).castExpression shape)⟩

noncomputable def NormalizedFamilyPrefix.domainOriginal
    {packet : OriginalProjectionParameters sourceEnv U name info levels}
    (selectedPi : NormalizedFamilyPrefix packet) :
    EndpointRef packet.origin.base U [] selectedPi.domainExpression (.sort selectedPi.selected.view.domainLevel) :=
  Classical.choose selectedPi.selected.view.location.originalDomains.1

theorem NormalizedFamilyPrefix.domain_eq
    {packet : OriginalProjectionParameters sourceEnv U name info levels}
    (selectedPi : NormalizedFamilyPrefix packet) :
    selectedPi.selected.view.domain = .ref selectedPi.domainOriginal :=
  Classical.choose_spec selectedPi.selected.view.location.originalDomains.1

noncomputable def NormalizedFamilyPrefix.domainLocation
    {packet : OriginalProjectionParameters sourceEnv U name info levels}
    (selectedPi : NormalizedFamilyPrefix packet) :
    Located (.right packet.instantiated.normalization) (.ref selectedPi.domainOriginal) :=
  selectedPi.domain_eq ▸ Located.piDomain selectedPi.selected.view.location

/-- Only one fixed original observation-R edge, with literal equal source
expressions, followed by the actual retained normalization equality. -/
theorem RichCodeTransferResult.normalizedDomainAnswer
    {left : EndpointState leftEnv U leftSource (.forallE A B) (.sort leftLevel)}
    {header : EndpointState headerEnv U [] headerExpression (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (nonempty : 0 < info.nparams)
    (sameSource : headerExpression = packet.origin.family.type.instL levels)
    (answer : RichCodeTransferResult env U registry target left header [] σ seed (fun _ => []) true
      (Profile.pi (A.subst σ) (B.subst σ.lift) (support : Profile n) []))
    (reindex : RichObs headerEnv env U registry target header [] seed
      (Profile.pi (A.subst σ) (B.subst σ.lift) support []) answer.footprint →
      answer.footprint.Available (fun _ => []) → Nonempty (RichGradedResult packet.origin.base env U registry target
      (.ref (.left packet.instantiated.normalization)) [] seed (fun _ => [])
      (Profile.pi (A.subst σ) (B.subst σ.lift) support [])))
    (normalizationF : ∀ {footprint : Footprint},
      RichObs packet.origin.base env U registry target (.ref (.left packet.instantiated.normalization))
        [] seed (Profile.pi (A.subst σ) (B.subst σ.lift) support []) footprint →
      footprint.Available (fun _ => []) →
      Nonempty (OriginalEqualityQueryResult packet.instantiated.normalization env registry target
        [] seed seed (fun _ => []) (Profile.pi (A.subst σ) (B.subst σ.lift) support []))) :
    let selectedPi := normalizedFamilyPrefix packet nonempty
    ∃ footprint,
      Nonempty (RichCert packet.origin.base env U registry target selectedPi.selected.view.domain
        [] seed true support footprint) ∧
      footprint.Available (fun _ => []) ∧
      TypeRelated env U registry target (A.subst σ) (selectedPi.domainExpression.subst seed) support ∧
      TypeConversion env U target (A.subst σ) (selectedPi.domainExpression.subst seed) := by
  dsimp only
  obtain ⟨reindexed⟩ := reindex (.code answer.certificate) answer.resources
  obtain ⟨fp, ⟨input⟩, resources⟩ := reindexed.code henv answer.certificate.formed
  obtain ⟨normalized⟩ := normalizationF (.code input) resources
  obtain ⟨fp, ⟨certificate⟩, resources, code⟩ := normalized.code henv hscoped formed input.formed
  let selectedPi := normalizedFamilyPrefix packet nonempty
  have combined : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE selectedPi.domainExpression selectedPi.bodyExpression).subst seed)
      (Profile.pi (A.subst σ) (B.subst σ.lift) support []) := by
    rw [← selectedPi.shape]
    apply answer.related.trans henv
    simpa only [sameSource] using code
  obtain ⟨domain⟩ := (castCertificate certificate selectedPi.shape).piDomain
    selectedPi.selected.view.domainWF selectedPi.selected.view.bodyWF selectedPi.selected.route resources
  exact ⟨domain.footprint, ⟨domain.certificate⟩, domain.resources,
    TypeRelated.literalPiDomain henv hscoped formed (by simpa only [subst] using combined),
    TypeRelated.literalPiDomainPath henv formed (by simpa only [subst] using combined)⟩

/-- The normalization calls are paid by the actual primitive constant,
using its seed instance even when the displayed endpoint uses equivalent
universes. Neither callback receives an arbitrary original derivation. -/
theorem primitiveFamilyNormalization
    {left : EndpointState leftEnv U leftSource (.forallE A B) (.sort leftLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (lookup : sourceEnv.constants name = some constInfo)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
    (leftWF : ∀ level ∈ levels, level.WF U) (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = constInfo.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (constInfo.type.instL levels) (constInfo.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (constInfo.type.instL levels) (constInfo.type.instL otherLevels) (.sort level))
    (captured : List Closure) :
    let packet := selectProjectionParameters ordered registered leftWF
    let header := selectOriginalHeader ordered lookup leftWF
    let normalizationCost := (Closure.close
      (packet.instantiated.normalization.dependencyOrigin packet.origin.baseOrdered) []).cost
    let limit := richSchedule .fundamental (Closure.close
      ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
      captured).cost
    ∀ answer : RichCodeTransferResult env U registry target left (.ref (.left header.original))
      [] σ seed (fun _ => []) true (Profile.pi (A.subst σ) (B.subst σ.lift) (support : Profile n) []),
    (richSchedule .expressionReindex
      ((Closure.close (header.original.dependencyOrigin header.ordered) []).cost + normalizationCost) < limit →
      RichObs header.source env U registry target (.ref (.left header.original)) [] seed
        (Profile.pi (A.subst σ) (B.subst σ.lift) support []) answer.footprint →
      answer.footprint.Available (fun _ => []) →
      Nonempty (RichGradedResult packet.origin.base env U registry target
        (.ref (.left packet.instantiated.normalization)) [] seed (fun _ => [])
        (Profile.pi (A.subst σ) (B.subst σ.lift) support []))) →
    (richSchedule .fundamental normalizationCost < limit →
      ∀ {footprint : Footprint},
      RichObs packet.origin.base env U registry target (.ref (.left packet.instantiated.normalization))
        [] seed (Profile.pi (A.subst σ) (B.subst σ.lift) support []) footprint →
      footprint.Available (fun _ => []) →
      Nonempty (OriginalEqualityQueryResult packet.instantiated.normalization env registry target
        [] seed seed (fun _ => []) (Profile.pi (A.subst σ) (B.subst σ.lift) support []))) →
    let selectedPi := normalizedFamilyPrefix packet nonempty
    ∃ footprint,
      Nonempty (RichCert packet.origin.base env U registry target selectedPi.selected.view.domain
        [] seed true support footprint) ∧
      footprint.Available (fun _ => []) ∧
      TypeRelated env U registry target (A.subst σ) (selectedPi.domainExpression.subst seed) support ∧
      TypeConversion env U target (A.subst σ) (selectedPi.domainExpression.subst seed) := by
  dsimp only
  intro answer reindex normalizationF
  have pair := Derivation.constantNormalization_pair_lt ordered lookup registered leftWF rightWF count
    equivalent levelWF closed ambient captured
  have single : (Closure.close
      ((selectProjectionParameters ordered registered leftWF).instantiated.normalization.dependencyOrigin
        (selectProjectionParameters ordered registered leftWF).origin.baseOrdered) []).cost <
      (Closure.close ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
        captured).cost := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) pair
  have infoEq : constInfo = (selectProjectionParameters ordered registered leftWF).origin.family.toVConstant :=
    Option.some.inj (lookup.symm.trans (selectProjectionParameters ordered registered leftWF).origin.familyPresent)
  have same : constInfo.type.instL levels =
      (selectProjectionParameters ordered registered leftWF).origin.family.type.instL levels := by
    rw [infoEq]
  exact answer.normalizedDomainAnswer henv hscoped formed
    (selectProjectionParameters ordered registered leftWF) nonempty same
    (reindex (richSchedule_strict pair _ _)) (normalizationF (richSchedule_strict single _ _))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
