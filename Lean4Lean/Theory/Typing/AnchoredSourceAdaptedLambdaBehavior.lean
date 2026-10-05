import Lean4Lean.Theory.Typing.AnchoredSourceAdaptedLambda
import Lean4Lean.Theory.Typing.AnchoredSourceLambdaBehavior

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem AdaptedLambdaTypeResult.atArgument
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : AdaptedLambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (originalDomain : AdaptedJoint env U registry source A A (.sort domainLevel))
    (originalBody : AdaptedJoint env U registry (A :: source) body other B)
    (originalCodomain : AdaptedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (admitted : Admitted env U registry target key argument argument) :
    LambdaArgumentResult env U registry target (left.cons key.anchor) (right.cons argument)
      body other B output fixed.resultSupport := by
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains first
  have paired : Ctx.SubstEq env U target (left.cons key.anchor)
      (right.cons argument) (A :: source) :=
    .cons substitutions formedA (guard.path.cast raw)
  have domainChild : AdaptedTransfer env U registry target locals left right available A A (.sort domainLevel) := (originalDomain target locals left right available closed
    hTarget substitutions fits).1
  have localFits := fits.push henv hscoped hTarget closed domainChild domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodies := originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits
  obtain ⟨code⟩ := fixed.bodyCertificate.transfer_adapted henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) codomains.1
    fixed.bodyAvailable
  obtain ⟨forward⟩ := bodies.1 observation (pack.available_atomized_localNeeds outsideAvailable)
  have selfBodies := AdaptedJoint.left henv hscoped originalBody
  obtain ⟨self⟩ := (selfBodies target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument)
    (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available)
    (Valuation.push_atomized_closed closed _) hTarget paired localFits).1
    observation (pack.available_atomized_localNeeds outsideAvailable)
  exact ⟨code.related,
    Related.retag henv fixed.outputTyped code.related.left_diagonal self.related,
    Related.retag henv fixed.outputTyped code.related.left_diagonal forward.related⟩

end Lean4Lean.AnchoredSource
