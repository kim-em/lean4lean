import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableLambda
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableTransferConversion

/-! The complete original lambda equality for hereditary observations. The
mutual traversal covers both legacy and rich computational/certificate
wrappers; reverse typing is transported through the actual Pi equality. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
mutual
theorem Obs.lamHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryTailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A body) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    exact SortableObs.graded_lam_transferOriginal henv hscoped (.ofCode domain domain.formed) guard (.legacy body) pack covered
      context domainRef originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.lamHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryTailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : SortableObs env U registry target locals σ (.lam A body) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .legacy source =>
    exact Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
  | .code relevant certificate =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits certificate resources
    exact ⟨answer.computational henv⟩
  | .lam domain guard body pack covered =>
    exact SortableObs.graded_lam_transferOriginal henv hscoped domain guard body pack covered
      context domainRef originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    obtain ⟨a⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    obtain ⟨a⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.lamHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryTailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (certificate : CodeCert env U registry target locals σ (.lam A body) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) true demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .map view source =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.lamHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryTailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (certificate : SortableCert env U registry target locals σ (.lam A body) relevant demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨answer⟩ := CodeCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.retag formed⟩
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .observe observation formed =>
    obtain ⟨answer⟩ := SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .support action source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.supportAction henv hscoped action⟩
  | .map view source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
  | .sortPad source =>
    obtain ⟨answer⟩ := SortableCert.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact answer.sortPad henv
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

theorem SortableComputationalTransfer.lamDFOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryTailJoint env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available) :
    SortableComputationalTransfer env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
  SortableObs.lamHereditary henv hscoped context domainRef originalDomain originalBody originalCodomain
    domains codomain bodies rightBody closed hTarget substitutions fits

/-- The two lambda annotations use their own actual formation references.
The reverse Pi conversion is constructed from the original formation
children, not supplied as a recursive call on a synthesized derivation. -/
theorem OriginalTail.DerivationHereditaryFundamental.lamDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (codomain' : Derivation sourceEnv U (A' :: source) B B (.sort bodyLevel))
    (bodies : Derivation sourceEnv U (A :: source) body other B)
    (bodies' : Derivation sourceEnv U (A' :: source) body other B)
    (domainIH : DerivationHereditaryFundamental env registry context domain)
    (codomainIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) codomain)
    (codomainIH' : DerivationHereditaryFundamental env registry (.cons context (.right domain)) codomain')
    (bodyIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) bodies)
    (bodyIH' : DerivationHereditaryFundamental env registry (.cons context (.right domain)) bodies') :
    DerivationHereditaryFundamental env registry context
      (.lamDF domainWF bodyWF domain codomain codomain' bodies bodies') := by
  intro target locals σ τ available closed hTarget substitutions fits
  have domainJoint : HereditaryTailJoint env registry context A A' (.sort domainLevel) := domainIH
  have bodyJoint : HereditaryTailJoint env registry (.cons context (.left domain)) body other B := bodyIH
  have otherJoint : HereditaryTailJoint env registry (.cons context (.right domain)) body other B := bodyIH'
  have forward : SortableComputationalTransfer env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
    SortableComputationalTransfer.lamDFOriginal henv hscoped context (.left domain) domainJoint bodyJoint codomainIH
      (domain.forget.defeq.mono hle) (codomain.forget.defeq.mono hle)
      (bodies.forget.defeq.mono hle) (bodies'.forget.defeq.mono hle).hasType.2
      closed hTarget substitutions fits
  have backwardNatural : SortableComputationalTransfer env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A' B) :=
    SortableComputationalTransfer.lamDFOriginal henv hscoped context (.right domain) domainJoint.symm otherJoint.symm codomainIH'
      (domain.forget.defeq.mono hle).symm (codomain'.forget.defeq.mono hle)
      (bodies'.forget.defeq.mono hle).symm (bodies.forget.defeq.mono hle).hasType.1
      closed hTarget substitutions fits
  have pi := OriginalTail.DerivationHereditaryFundamental.forallEDF henv hscoped hle context domainWF bodyWF
    domain codomain codomain' domainIH codomainIH codomainIH'
  have code : SortableComputationalTransfer env U registry target locals σ σ available
      (.forallE A' B) (.forallE A B) (.sort (.imax domainLevel bodyLevel)) :=
    (pi target locals σ σ available closed hTarget substitutions.left fits.left).2
  have backward : SortableComputationalTransfer env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A B) :=
    SortableComputationalTransfer.convertAnswer henv hscoped closed hTarget code backwardNatural
  exact ⟨forward, backward⟩

end Lean4Lean.AnchoredSource.Adapted
