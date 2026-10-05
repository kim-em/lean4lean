import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaRaw

/-! Full lambda transfer into a concrete covered-lambda node. This remains an
extension record over the old source grammar until its AST migration. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure CoveredLambdaTransferResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (left right : Subst) (available : Valuation)
    (A A' B body other : VExpr) (key : Key n) (output : Atom n) where
  rawOutput : Atom n
  node : CoveredLambda env U registry target locals right A' other key rawOutput
  domainAvailable : node.domainFootprint.Available available
  outsideAvailable : node.outside.Available available
  adapter : NormalProfileAdapter env U registry target
    (Profile.fn key rawOutput) (Profile.fn key output)
  support : Profile (n + 1)
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals left (.forallE A B) support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : (Profile.fn key output).HasType support
  rawTyped : (Profile.fn key rawOutput).HasType support
  typeCode : TypeRelated env U registry target ((VExpr.forallE A B).subst left)
    ((VExpr.forallE A B).subst left) support
  related : Related env U registry target ((VExpr.lam A body).subst left)
    ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
    (Profile.fn key output) support
  rawRelated : Related env U registry target ((VExpr.lam A' other).subst right)
    ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
    (Profile.fn key rawOutput) support

private theorem union_code
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem CoveredLambda.transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : CoveredLambda env U registry target locals left A body key output)
    (originalDomain : Joint env U registry source A A' (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits env U registry source target locals left right available)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    Nonempty (CoveredLambdaTransferResult env U registry target locals left right available
      A A' B body other key output) := by
  have originalA := Joint.left henv hscoped originalDomain
  have originalOther := Joint.right henv hscoped originalBody
  have domainChild : Transfer env U registry target locals left right available A A' (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  have actualDomainChild : Transfer env U registry target locals left right available A A (.sort domainLevel) := (originalA target locals left right available closed
    hTarget substitutions fits).1
  obtain ⟨annotation⟩ := node.domain.transfer henv hscoped hTarget closed
    domainChild domainAvailable
  obtain ⟨actualDomain⟩ := node.domain.transfer henv hscoped hTarget closed
    actualDomainChild domainAvailable
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
  have localFits := fits.push henv hscoped hTarget closed actualDomainChild node.domain
    domainAvailable node.guard.inputTyped arguments
    (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (node.pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  have localClosed := Valuation.push_atomized_closed closed node.bodyFootprint.localNeeds
  obtain ⟨returned⟩ := (originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons key.anchor)
    (Valuation.push (node.bodyFootprint.localNeeds ++ node.bodyFootprint.localNeeds.flatMap Need.singletons) available)
    localClosed hTarget paired localFits).1 node.bodyObservation
      (node.pack.available_atomized_localNeeds outsideAvailable)
  obtain ⟨normalAtom, member, ⟨outputAdapter⟩⟩ := returned.adapter.origin
    (List.mem_map.mpr ⟨output, List.mem_singleton_self _, rfl⟩)
  obtain ⟨rawOutput, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨selected⟩ := returned.observation.atom rawMember
  have selectedAvailable := selected.atomizes.available_closed returned.resultAvailable localClosed
  obtain ⟨packed, external, pack, covered, externalAvailable⟩ :=
    Footprint.pack_available selectedAvailable
      (fun need hm => (node.pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => node.covered atom ((node.pack.atomized_localNeeds need hm).2 atom ha))
  let rawNode : CoveredLambda env U registry target locals right A' other key rawOutput := {
    domainSupport := node.domainSupport
    domainFootprint := annotation.footprint
    domain := annotation.certificate
    guard := annotationGuard
    bodyFootprint := selected.footprint
    bodyObservation := selected.observation
    outside := external
    packed := packed
    pack := pack
    covered := covered }
  obtain ⟨rightFixed⟩ := Obs.lambda_type henv originalOther closed domains.hasType.1
    hTarget (substitutions.right henv hTarget) fits.right actualDomain.certificate actualGuard
    selected.observation pack covered actualDomain.available externalAvailable
  obtain ⟨leftFixed, support_eq⟩ := rightFixed.changeBase henv hscoped originalA originalCodomain
    closed domains.hasType.1 hTarget (substitutions.symm henv hTarget) fits.symm
    actualDomain.certificate actualGuard node.domain node.guard pack covered
    actualDomain.available domainAvailable
  have rawRelated := leftFixed.rawRightRelated henv hscoped rightFixed support_eq originalA
    originalOther originalCodomain closed domains codomain bodies.hasType.2 rightBody hTarget
    substitutions fits node.domain node.guard actualDomain.certificate actualGuard
    selected.observation pack covered domainAvailable actualDomain.available externalAvailable
  obtain ⟨requestedSupport, requestedFootprint, ⟨requestedCertificate⟩, requestedAvailable,
      requestedTyped, requestedRelated⟩ := node.interpret henv hscoped originalA originalBody
    originalCodomain closed domains codomain bodies.hasType.1 rightBody hTarget substitutions fits
    domainAvailable outsideAvailable
  have requestedCode := requestedRelated.typeCode henv hscoped hTarget (by simp [Profile.fn, Profile.singleton, Profile.mk, Profile.Nonempty, Profile.atoms])
  have rawCode := rawRelated.typeCode henv hscoped hTarget (by simp [Profile.fn, Profile.singleton, Profile.mk, Profile.Nonempty, Profile.atoms])
  have code := union_code requestedCode rawCode
  have wf := requestedTyped.wf_type.union leftFixed.typed.wf_type
  have typed := requestedTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := leftFixed.typed.enlarge (Profile.le_union_right _ _) wf
  have adapter : NormalProfileAdapter env U registry target
      (Profile.fn key rawOutput) (Profile.fn key output) :=
    .cons (List.mem_singleton_self _) (.fn (.refl _) outputAdapter) (.nil _)
  exact ⟨⟨rawOutput, rawNode, annotation.available, externalAvailable, adapter, _, _,
    .union requestedCertificate leftFixed.certificate,
    (fun i need hm => (List.mem_append.mp hm).elim (requestedAvailable i need) (leftFixed.available i need)),
    typed, rawTyped, code,
    Related.retag henv typed code requestedRelated,
    Related.retag henv rawTyped code rawRelated⟩⟩


/-- The covered record is now a genuine constructor of the replacement AST. -/
noncomputable def CoveredLambda.observation
    (node : CoveredLambda env U registry target locals realization A body key output) :
    Obs env U registry target locals realization (.lam A body) (Profile.fn key output)
      (node.domainFootprint ++ node.outside) :=
  .lam node.domain node.guard node.bodyObservation node.pack node.covered

noncomputable def CoveredLambdaTransferResult.toTransferResult
    (result : CoveredLambdaTransferResult env U registry target locals left right available
      A A' B body other key output) :
    TransferResult env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output) where
  rawDemand := Profile.fn key result.rawOutput
  resultFootprint := result.node.domainFootprint ++ result.node.outside
  observation := result.node.observation
  adapter := result.adapter
  resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
    (result.domainAvailable i need) (result.outsideAvailable i need)
  support := result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate
  typeAvailable := result.typeAvailable
  typed := result.typed
  rawTyped := result.rawTyped
  typeCode := result.typeCode
  related := result.related
  rawRelated := result.rawRelated

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
    (originalDomain : Joint env U registry source A A' (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits env U registry source target locals left right available)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (TransferResult env U registry target locals left right available
      (.lam A body) (.lam A' other) (.forallE A B) (Profile.fn key output)) := by
  let node : CoveredLambda env U registry target locals left A body key output :=
    ⟨domainSupport, domainFootprint, domain, guard, bodyFootprint, bodyObservation,
      outside, packed, pack, covered⟩
  obtain ⟨result⟩ := node.transfer henv hscoped originalDomain originalBody originalCodomain
    closed domains codomain bodies rightBody hTarget substitutions fits domainAvailable outsideAvailable
  exact ⟨result.toTransferResult⟩

end Lean4Lean.AnchoredSource.Adapted
