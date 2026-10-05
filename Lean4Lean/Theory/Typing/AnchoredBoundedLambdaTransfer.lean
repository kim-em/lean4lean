import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaRaw

/-! One initial graded body result fixes the returned lambda grade. Later
semantic calls project their requested result instead of chasing raw grades. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private theorem union_code
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem CoveredLambda.gradedTransfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : CoveredLambda env U registry target locals left A body key output)
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) body other B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits current fuel env U registry source target locals left right available)
    (domainBound : node.domain.nativeDepth current ≤ fuel)
    (observationBound : node.bodyObservation.nativeDepth current ≤ fuel)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    Nonempty (Result current fuel env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  have originalA := Joint.left henv hscoped originalDomain
  have originalOther := Joint.right henv hscoped originalBody
  have domainChild : Transfer current fuel env U registry target locals left right available A A' (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  have actualDomainChild : Transfer current fuel env U registry target locals left right available A A (.sort domainLevel) := (originalA target locals left right available closed
    hTarget substitutions fits).1
  obtain ⟨annotation⟩ := domainChild.codeCertificate henv hscoped hTarget closed
    node.domain domainBound domainAvailable
  obtain ⟨actualDomain⟩ := actualDomainChild.codeCertificate henv hscoped hTarget closed
    node.domain domainBound domainAvailable
  have annotationGuard : LambdaGuard env U registry target right A' key node.domainSupport := {
    inputTyped := node.guard.inputTyped
    formed := node.guard.formed
    path := node.guard.path.trans (.single (domains.substDF henv substitutions.wf hTarget substitutions))
    domains := node.guard.domains.trans henv annotation.related
    anchor := node.guard.anchor }
  have actualGuard : LambdaGuard env U registry target right A key node.domainSupport := {
    inputTyped := node.guard.inputTyped
    formed := node.guard.formed
    path := node.guard.path.trans (.single (domains.hasType.1.substDF henv substitutions.wf hTarget substitutions))
    domains := node.guard.domains.trans henv actualDomain.related
    anchor := node.guard.anchor }
  obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := node.guard.anchor
  have arguments := Related.convert henv node.guard.inputTyped node.guard.domains anchor
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons key.anchor) (A :: source) :=
    .cons substitutions domains.hasType.1 (node.guard.path.cast raw)
  have localFits := fits.pushGraded henv hscoped hTarget closed actualDomainChild node.domain
    domainBound domainAvailable node.guard.inputTyped arguments
    (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (node.pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  have localClosed := Valuation.push_atomized_closed closed node.bodyFootprint.localNeeds
  obtain ⟨returned⟩ := (originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons key.anchor)
    (Valuation.push (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons) available)
    localClosed hTarget paired localFits).1 node.bodyObservation observationBound
      (node.pack.available_atomized_localNeeds outsideAvailable)
  obtain ⟨normalAtom, member, ⟨outputAdapter⟩⟩ := returned.adapter.origin
    (by
      rw [raiseProfile_singleton]
      exact List.mem_map.mpr ⟨_, List.mem_singleton_self _, rfl⟩)
  obtain ⟨rawOutput, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨selected, selectedLower⟩ := returned.observation.atom_bounded (current := current) rawMember
  have selectedBound := Nat.le_trans selectedLower returned.observationBound
  have selectedAvailable := selected.atomizes.available_closed returned.resultAvailable localClosed
  obtain ⟨packed, external, pack, covered, externalAvailable⟩ :=
    Footprint.pack_available selectedAvailable
      (fun need hm => (node.pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  let highKey := raiseKey returned.rank returned.bound key
  have highPack := pack.raise returned.bound
  have highCovered := raiseProfile_subset returned.bound covered
  let highAnnotation := annotation.certificate.raise returned.bound
  let highActualDomain := actualDomain.certificate.raise returned.bound
  let highDomain := node.domain.raise returned.bound
  have highAnnotationGuard := annotationGuard.raise henv returned.bound
  have highActualGuard := actualGuard.raise henv returned.bound
  have highGuard := node.guard.raise henv returned.bound
  let rawNode : CoveredLambda env U registry target locals right A' other highKey rawOutput := {
    domainSupport := raiseProfile returned.rank returned.bound node.domainSupport
    domainFootprint := annotation.footprint
    domain := highAnnotation
    guard := highAnnotationGuard
    bodyFootprint := selected.footprint
    bodyObservation := selected.observation
    outside := external
    packed := raiseProfile returned.rank returned.bound packed
    pack := highPack
    covered := highCovered }
  obtain ⟨rightFixed⟩ := Obs.lambda_typeBounded henv originalOther closed domains.hasType.1
    hTarget (substitutions.right henv hTarget) fits.right highActualDomain highActualGuard
    selected.observation highPack highCovered
    (by simpa only [highActualDomain, CodeCert.nativeDepth_raise] using actualDomain.certificateBound)
    selectedBound actualDomain.available externalAvailable
  obtain ⟨leftFixed, support_eq⟩ := rightFixed.gradedChangeBase henv hscoped originalA originalCodomain
    closed domains.hasType.1 hTarget (substitutions.symm henv hTarget) fits.symm
    highActualDomain highActualGuard highDomain highGuard highPack highCovered
    (by simpa only [highActualDomain, CodeCert.nativeDepth_raise] using actualDomain.certificateBound)
    actualDomain.available (by simpa only [highDomain, CodeCert.nativeDepth_raise] using domainBound) domainAvailable
  have rawRelated := leftFixed.gradedRawRightRelated henv hscoped rightFixed support_eq originalA
    originalOther originalCodomain closed domains codomain bodies.hasType.2 rightBody hTarget
    substitutions fits highDomain highGuard highActualDomain highActualGuard
    selected.observation highPack highCovered
    (by simpa only [highDomain, CodeCert.nativeDepth_raise] using domainBound)
    (by simpa only [highActualDomain, CodeCert.nativeDepth_raise] using actualDomain.certificateBound)
    selectedBound domainAvailable actualDomain.available externalAvailable
  obtain ⟨requestedSupport, requestedFootprint, requestedCertificate, requestedBound, requestedAvailable,
      requestedTyped, requestedRelated⟩ := CoveredLambda.gradedInterpret henv hscoped node originalA originalBody
    originalCodomain closed domains codomain bodies.hasType.1 rightBody hTarget substitutions fits
    domainBound observationBound domainAvailable outsideAvailable
  have bound := Nat.succ_le_succ returned.bound
  let highRequestedCertificate := requestedCertificate.raise bound
  have highRequestedRelated := Related.raise henv bound requestedRelated
  have highRequestedTyped := Profile.HasType.raise bound requestedTyped
  have requestedCode := TypeRelated.raise henv bound
    (requestedRelated.typeCode henv hscoped hTarget
      (by simp [Profile.fn, Profile.singleton, Profile.mk, Profile.Nonempty, Profile.atoms]))
  have rawCode := rawRelated.typeCode henv hscoped hTarget
    (by simp [Profile.fn, Profile.singleton, Profile.mk, Profile.Nonempty, Profile.atoms])
  have code := union_code requestedCode rawCode
  have wf := highRequestedTyped.wf_type.union leftFixed.typed.wf_type
  have typed := highRequestedTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := leftFixed.typed.enlarge (Profile.le_union_right _ _) wf
  have outputStep : NormalAtomAdapter (n := returned.rank + 1) env U registry target
      (AtomData.fn highKey rawOutput) (AtomData.fn highKey (raiseAtom returned.rank returned.bound output)) :=
    .fn (.refl _) outputAdapter
  have gradeStep := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) returned.bound key output).inverse henv
  have step := NormalAtomAdapter.comp outputStep (gradeStep.toAdapter henv hscoped hTarget)
  have adapter : NormalProfileAdapter env U registry target
      (Profile.fn highKey rawOutput) (raiseProfile (returned.rank + 1) bound (Profile.fn key output)) := by
    simp only [Profile.fn, raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) step (.nil _)
  exact ⟨{
    rank := returned.rank + 1
    bound := bound
    rawDemand := Profile.fn highKey rawOutput
    resultFootprint := rawNode.domainFootprint ++ rawNode.outside
    observation := rawNode.observation
    adapter := adapter
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (annotation.available i need) (externalAvailable i need)
    support := _
    typeFootprint := _
    certificate := .union highRequestedCertificate leftFixed.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (requestedAvailable i need) (leftFixed.available i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRequestedRelated
    rawRelated := Related.retag henv rawTyped code rawRelated
    observationBound := by
      simpa only [rawNode, CoveredLambda.observation, Obs.nativeDepth, highAnnotation,
        CodeCert.nativeDepth_raise] using Nat.max_le.mpr ⟨annotation.certificateBound, selectedBound⟩
    certificateBound := by
      simpa only [CodeCert.nativeDepth, highRequestedCertificate, CodeCert.nativeDepth_raise] using
        Nat.max_le.mpr ⟨requestedBound, leftFixed.certificateBound⟩ }⟩

theorem Obs.lam_transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (bodyObservation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) body other B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits current fuel env U registry source target locals left right available)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (observationBound : bodyObservation.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (Result current fuel env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  let node : CoveredLambda env U registry target locals left A body key output :=
    ⟨domainSupport, domainFootprint, domain, guard, bodyFootprint, bodyObservation,
      outside, packed, pack, covered⟩
  exact CoveredLambda.gradedTransfer henv hscoped node originalDomain originalBody originalCodomain
    closed domains codomain bodies rightBody hTarget substitutions fits domainBound observationBound domainAvailable outsideAvailable

end Lean4Lean.AnchoredSource.Adapted.Staged
