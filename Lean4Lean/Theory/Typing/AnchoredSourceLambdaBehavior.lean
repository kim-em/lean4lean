import Lean4Lean.Theory.Typing.AnchoredCodeTransitivity
import Lean4Lean.Theory.Typing.AnchoredSourceLambda
import Lean4Lean.Theory.Typing.AnchoredBeta

/-! Interpret the original body and codomain children at an admitted argument.
The codomain support is the one fixed by the actual anchor certificate.
Both body endpoints are reached from that same anchor, without interpreting
a synthesized typing derivation or requesting a new source observation. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure LambdaArgumentResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (anchorRealization argumentRealization : Subst)
    (body other B : VExpr) (output : Atom n) (support : Profile n) : Prop where
  codomain : TypeRelated env U registry target
    (B.subst anchorRealization) (B.subst argumentRealization) support
  left : Related env U registry target
    (body.subst anchorRealization) (body.subst argumentRealization)
    (B.subst anchorRealization) (.singleton output) support
  right : Related env U registry target
    (body.subst anchorRealization) (other.subst argumentRealization)
    (B.subst anchorRealization) (.singleton output) support

theorem LambdaTypeResult.atArgument_subset
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      bodyFootprint.localNeeds A B body other key output domainSupport)
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : Fits env U registry source target locals left right available)
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
  have localFits := fits.push henv hTarget domain domainAvailable guard.inputTyped arguments
    bodyFootprint.localNeeds (fun need hm => (pack.localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.localNeeds need hm).2 atom ha))
  have bodies := originalBody target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push bodyFootprint.localNeeds available)
    hTarget paired localFits
  have codomains := originalCodomain target (Locals.push locals) (left.cons key.anchor)
    (right.cons argument) (Valuation.push bodyFootprint.localNeeds available)
    hTarget paired localFits
  obtain ⟨code⟩ := fixed.bodyCertificate.transfer henv hscoped hTarget codomains.1
    fixed.bodyAvailable
  obtain ⟨forward⟩ := bodies.1 observation (pack.available outsideAvailable)
  obtain ⟨backward⟩ := bodies.2.1 fixed.otherObservation fixed.otherAvailable
  have forwardFixed := Related.retag henv fixed.outputTyped code.related.left_diagonal
    forward.related
  have backwardFixed := Related.retag henv fixed.outputTyped code.related.left_diagonal
    backward.related
  exact ⟨code.related, fixed.anchorRelated.trans henv hscoped backwardFixed, forwardFixed⟩

/-- The four concrete original-child calls share one anchor and one support.
Thus the three function outputs are composed at that anchor, then converted
to the actual left codomain at the first argument. -/
theorem LambdaArgumentResult.outputs
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {anchor leftX leftY rightX rightY : Subst}
    {body other B : VExpr} {output : Atom n} {support : Profile n}
    (typed : (Profile.singleton output).HasType support)
    (lx : LambdaArgumentResult env U registry target anchor leftX body other B output support)
    (ly : LambdaArgumentResult env U registry target anchor leftY body other B output support)
    (rx : LambdaArgumentResult env U registry target anchor rightX body other B output support)
    (ry : LambdaArgumentResult env U registry target anchor rightY body other B output support) :
    TypeRelated env U registry target (B.subst leftX) (B.subst leftY) support ∧
    Related env U registry target (body.subst leftX) (body.subst leftY)
      (B.subst leftX) (.singleton output) support ∧
    Related env U registry target (other.subst rightX) (other.subst rightY)
      (B.subst leftX) (.singleton output) support ∧
    Related env U registry target (body.subst leftX) (other.subst rightX)
      (B.subst leftX) (.singleton output) support := by
  exact ⟨(lx.codomain.symm henv typed.wf_type).trans henv ly.codomain,
    Related.convert henv typed lx.codomain
      ((lx.left.symm henv).trans henv hscoped ly.left),
    Related.convert henv typed lx.codomain
      ((rx.right.symm henv).trans henv hscoped ry.right),
    Related.convert henv typed lx.codomain
      ((lx.left.symm henv).trans henv hscoped rx.right)⟩

theorem LambdaTypeResult.atArgument
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      bodyFootprint.localNeeds A B body other key output domainSupport)
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : Fits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n key.input bodyFootprint outside)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (admitted : Admitted env U registry target key argument argument) :
    LambdaArgumentResult env U registry target (left.cons key.anchor) (right.cons argument)
      body other B output fixed.resultSupport := by
  exact fixed.atArgument_subset henv hscoped originalBody originalCodomain formedA hTarget substitutions fits domain guard observation pack (fun _ h => h) domainAvailable outsideAvailable admitted

end Lean4Lean.AnchoredSource
