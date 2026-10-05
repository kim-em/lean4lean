import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaIntroduction

/-! Raw right-hand lambda evidence is transported through the original
codomain child at its retained finite support. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

theorem LambdaTypeResult.gradedCodomainTransfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult current fuel env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits current fuel env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (admitted : Admitted env U registry target key argument argument) :
    Nonempty (CodeResult current fuel env U registry target (Locals.push locals)
      (left.cons key.anchor) (right.cons argument)
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
      B B fixed.resultSupport) := by
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains first
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons argument) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have domainChild : Transfer current fuel env U registry target locals left right available A A (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  have localFits := fits.pushGraded henv hscoped hTarget closed domainChild domain domainBound domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits
  exact Transfer.codeCertificate henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) codomains.1 fixed.bodyCertificate fixed.bodyBound fixed.bodyAvailable


/-- Move only the fixed actual codomain certificate to the other realization.
The original codomain child supplies the transfer; the literal Pi certificate
is rebuilt from its returned leaves and the already available domain. -/
theorem LambdaTypeResult.gradedChangeBase
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint newDomainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult current fuel env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B body other key output domainSupport)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits current fuel env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (newDomain : CodeCert env U registry target locals right A domainSupport newDomainFootprint)
    (newGuard : LambdaGuard env U registry target right A key domainSupport)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (newDomainBound : newDomain.nativeDepth current ≤ fuel)
    (newDomainAvailable : newDomainFootprint.Available available) :
    ∃ changed : LambdaTypeResult current fuel env U registry target locals right available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B body other key output domainSupport,
      changed.resultSupport = fixed.resultSupport := by
  obtain ⟨code⟩ := fixed.gradedCodomainTransfer henv hscoped originalDomain originalCodomain
    closed formedA hTarget substitutions fits domain guard pack covered domainBound domainAvailable guard.anchor
  obtain ⟨packed, external, bodyPack, coverage, externalAvailable⟩ :=
    Footprint.pack_available code.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  let certificate := newDomain.piLiteral
    (PiRows.cons newGuard code.certificate bodyPack coverage PiRows.nil)
  refine ⟨⟨fixed.resultSupport, code.footprint, code.certificate, code.available,
    fixed.outputTyped, _, certificate, ?_, ?_, code.certificateBound, ?_⟩, rfl⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (newDomainAvailable i need)
      (fun h => externalAvailable i need (by simpa using h))
  · exact Profile.HasType.fn certificate.formed.wf_value
      (List.mem_singleton_self _) fixed.outputTyped
  · simpa only [certificate, CodeCert.piLiteral, CodeCert.pi, CodeCert.nativeDepth,
      Obs.nativeDepth, PiRows.nativeDepth, Nat.max_zero] using
      Nat.max_le.mpr ⟨newDomainBound, code.certificateBound⟩

/-- Interpret the actual raw right lambda at the left-realized assigned Pi.
Only the original domain/body/codomain clauses are invoked. -/
theorem LambdaTypeResult.gradedRawRightRelated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {leftDomainFootprint rightDomainFootprint bodyFootprint outside : Footprint}
    (leftFixed : LambdaTypeResult current fuel env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B other other key output domainSupport)
    (rightFixed : LambdaTypeResult current fuel env U registry target locals right available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      A B other other key output domainSupport)
    (support_eq : leftFixed.resultSupport = rightFixed.resultSupport)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) other other B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits current fuel env U registry source target locals left right available)
    (leftDomain : CodeCert env U registry target locals left A domainSupport leftDomainFootprint)
    (leftGuard : LambdaGuard env U registry target left A key domainSupport)
    (rightDomain : CodeCert env U registry target locals right A domainSupport rightDomainFootprint)
    (rightGuard : LambdaGuard env U registry target right A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (right.cons key.anchor) other (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (leftDomainBound : leftDomain.nativeDepth current ≤ fuel)
    (rightDomainBound : rightDomain.nativeDepth current ≤ fuel)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (leftAvailable : leftDomainFootprint.Available available)
    (rightAvailable : rightDomainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Related env U registry target ((VExpr.lam A' other).subst right)
      ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
      (Profile.fn key output)
      (Profile.pi (A.subst left) (B.subst left.lift) domainSupport
        [(key, leftFixed.resultSupport)]) := by
  have rawA := domains.hasType.1.subst henv substitutions.left hTarget
  have formedA : env.IsType U target (A.subst left) := ⟨_, rawA⟩
  have contextA : OnCtx (A.subst left :: target) (env.IsType U) := ⟨hTarget, formedA⟩
  have formedB : env.IsType U (A.subst left :: target) (B.subst left.lift) :=
    ⟨_, codomain.subst henv (substitutions.left.lift henv domains.hasType.1) contextA⟩
  have row : ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ (((B.subst left.lift).lift' ρ.cons).inst x)
        (((B.subst left.lift).lift' ρ.cons).inst y) (leftFixed.resultSupport.rename ρ) := by
    intro Δ ρ future x y admitted
    let fixed := leftFixed.future henv future
    have pack' := pack.rename ρ
    have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
        atom ∈ (key.input.rename ρ).atoms := by
      intro atom hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (covered a ha)
    have sub := substitutions.future henv future
    have val := fits.future henv future
    have targetWF := future.targetWF henv
    obtain ⟨cx⟩ := fixed.gradedCodomainTransfer henv hscoped originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF sub.left val.left
      (leftDomain.future henv future) (leftGuard.future henv future) pack' covered'
      (by simpa only [CodeCert.nativeDepth_future] using leftDomainBound)
      (leftAvailable.rename ρ) (Admitted.left_diagonal admitted)
    have ay : Admitted env U registry Δ (key.rename ρ) y y := by
      obtain ⟨raw, pair, support, typed, formed, code, first, second⟩ := admitted
      exact ⟨raw.trans pair, pair.hasType.2, support, typed, formed, code,
        Related.trans henv hscoped first second, Related.left_diagonal (Related.symm henv second)⟩
    obtain ⟨cy⟩ := fixed.gradedCodomainTransfer henv hscoped originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF sub.left val.left
      (leftDomain.future henv future) (leftGuard.future henv future) pack' covered'
      (by simpa only [CodeCert.nativeDepth_future] using leftDomainBound)
      (leftAvailable.rename ρ) ay
    have result := (cx.related.symm henv fixed.outputTyped.wf_type).trans henv cy.related
    simpa only [fixed, LambdaTypeResult.future, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons] using result
  let display := PiWitness.literal henv hTarget formedA formedB leftGuard.inputTyped
    leftGuard.formed leftGuard.path leftGuard.domains row
  have code := TypeRelated.literalPi henv formedA formedB leftGuard.inputTyped
    leftGuard.formed leftGuard.path leftGuard.domains row
  have behavior : FunctionBehavior env U registry (relations env U registry n) target
      ((VExpr.lam A' other).subst right) ((VExpr.lam A' other).subst right)
      (.forallE (A.subst left) (B.subst left.lift)) key output
      (.pi (A.subst left) (B.subst left.lift) domainSupport [(key, leftFixed.resultSupport)]) := by
    refine ⟨leftGuard.anchor, _, _, domainSupport, [(key, leftFixed.resultSupport)],
      leftFixed.resultSupport, List.mem_singleton_self _, List.mem_singleton_self _,
      leftFixed.outputTyped, display, ?_⟩
    intro Δ ρ future x y admitted
    simp only [display, PiWitness.literal, Lift.refl_comp] at admitted
    have result := rightFixed.gradedFutureOutputs henv hscoped originalDomain originalBody
      originalCodomain closed domains codomain leftBody rightBody
      (substitutions.right henv hTarget) fits.right rightDomain rightGuard observation
      pack covered rightDomainBound observationBound rightAvailable outsideAvailable future admitted
    let fixed := rightFixed.future henv future
    have pack' := pack.rename ρ
    have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
        atom ∈ (key.input.rename ρ).atoms := by
      intro atom hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (covered a ha)
    have sub := substitutions.future henv future
    have val := fits.future henv future
    have targetWF := future.targetWF henv
    obtain ⟨cx⟩ := fixed.gradedCodomainTransfer henv hscoped originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF (sub.right henv targetWF) val.right
      (rightDomain.future henv future) (rightGuard.future henv future) pack' covered'
      (by simpa only [CodeCert.nativeDepth_future] using rightDomainBound)
      (rightAvailable.rename ρ) (Admitted.left_diagonal admitted)
    obtain ⟨cross⟩ := fixed.gradedCodomainTransfer henv hscoped originalDomain originalCodomain
      (closed.rename ρ) domains.hasType.1 targetWF (sub.symm henv targetWF) val.symm
      (rightDomain.future henv future) (rightGuard.future henv future) pack' covered'
      (by simpa only [CodeCert.nativeDepth_future] using rightDomainBound)
      (rightAvailable.rename ρ) (Admitted.left_diagonal admitted)
    have bridge := (cx.related.symm henv fixed.outputTyped.wf_type).trans henv cross.related
    have rightOutput := Related.convert henv fixed.outputTyped bridge result.2.2.1
    have support_eq' : fixed.resultSupport = leftFixed.resultSupport.rename ρ :=
      congrArg (Profile.rename ρ) support_eq.symm
    rw [support_eq'] at rightOutput
    have converted := rightOutput
    simp only [display, PiWitness.literal, Lift.refl_comp, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons, Related] at converted ⊢
    exact ⟨converted, converted, Related.left_diagonal converted⟩
  exact Related.function henv hscoped leftFixed.typed code behavior

end Lean4Lean.AnchoredSource.Adapted.Staged
