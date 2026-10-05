import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaSemantics
import Lean4Lean.Theory.Typing.AnchoredLiteralPi
import Lean4Lean.Theory.Typing.AnchoredFunctionIntroduction

/-! The semantic lambda constructor consumes only original strong-rule
children and the actual finite source observation. This does not assert the
separate source-observation transfer or its enclosing-binder resource law. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem LambdaTypeResult.related
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : LambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (originalDomain : Joint env U registry source A A (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
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
    (outsideAvailable : outside.Available available) :
    Related env U registry target ((VExpr.lam A body).subst left)
      ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
      (Profile.fn key output)
      (Profile.pi (A.subst left) (B.subst left.lift) domainSupport
        [(key, fixed.resultSupport)]) := by
  have rawA := domains.hasType.1.subst henv substitutions.left hTarget
  have formedA : env.IsType U target (A.subst left) := ⟨_, rawA⟩
  have contextA : OnCtx (A.subst left :: target) (env.IsType U) := ⟨hTarget, formedA⟩
  have rawB := codomain.subst henv
    (substitutions.left.lift henv domains.hasType.1) contextA
  have formedB : env.IsType U (A.subst left :: target) (B.subst left.lift) := ⟨_, rawB⟩
  have row : ∀ Δ ρ, FutureInsertion env U target Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ (((B.subst left.lift).lift' ρ.cons).inst x)
        (((B.subst left.lift).lift' ρ.cons).inst y) (fixed.resultSupport.rename ρ) := by
    intro Δ ρ future x y admitted
    have result := fixed.futureOutputs henv hscoped originalDomain originalBody originalCodomain
      closed domains codomain leftBody rightBody substitutions fits domain guard observation pack covered
      domainAvailable outsideAvailable future admitted
    simpa only [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons] using result.1
  let display := PiWitness.literal henv hTarget formedA formedB guard.inputTyped guard.formed
    guard.path guard.domains row
  have code := TypeRelated.literalPi henv formedA formedB guard.inputTyped guard.formed
    guard.path guard.domains row
  have behavior : FunctionBehavior env U registry (relations env U registry n) target
      ((VExpr.lam A body).subst left) ((VExpr.lam A' other).subst right)
      (.forallE (A.subst left) (B.subst left.lift)) key output
      (.pi (A.subst left) (B.subst left.lift) domainSupport [(key, fixed.resultSupport)]) := by
    refine ⟨guard.anchor, _, _, domainSupport, [(key, fixed.resultSupport)],
      fixed.resultSupport, List.mem_singleton_self _, List.mem_singleton_self _,
      fixed.outputTyped, display, ?_⟩
    intro Δ ρ future x y admitted
    simp only [display, PiWitness.literal, Lift.refl_comp] at admitted
    have result := fixed.futureOutputs henv hscoped originalDomain originalBody originalCodomain
      closed domains codomain leftBody rightBody substitutions fits domain guard observation pack covered
      domainAvailable outsideAvailable future admitted
    simpa only [display, PiWitness.literal, Lift.refl_comp, lift'_subst,
      ← Subst.lift_r_lift, inst_lift_cons, Related] using result.2
  exact Related.function henv hscoped fixed.typed code behavior

/-- The actual source certificate and semantic term result are produced
together from the original lambda children. There is no assumed producer for
a newly synthesized typing proof. -/
theorem Obs.lambda_interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (originalDomain : Joint env U registry source A A (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
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
    (outsideAvailable : outside.Available available) :
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals left (.forallE A B) support footprint) ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  obtain ⟨fixed⟩ := Obs.lambda_type henv originalBody closed domains.hasType.1 hTarget
    substitutions.left fits.left domain guard observation pack covered domainAvailable outsideAvailable
  exact ⟨_, _, ⟨fixed.certificate⟩, fixed.available, fixed.typed,
    fixed.related henv hscoped originalDomain originalBody originalCodomain closed domains codomain leftBody rightBody
      hTarget substitutions fits domain guard observation pack covered domainAvailable outsideAvailable⟩

theorem CoveredLambda.interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n}
    (node : CoveredLambda env U registry target locals left A body key output)
    (originalDomain : Joint env U registry source A A (.sort domainLevel))
    (originalBody : Joint env U registry (A :: source) body other B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits env U registry source target locals left right available)
    (domainAvailable : node.domainFootprint.Available available)
    (outsideAvailable : node.outside.Available available) :
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals left (.forallE A B) support footprint) ∧
      footprint.Available available ∧ (Profile.fn key output).HasType support ∧
      Related env U registry target ((VExpr.lam A body).subst left)
        ((VExpr.lam A' other).subst right) ((VExpr.forallE A B).subst left)
        (Profile.fn key output) support := by
  exact Obs.lambda_interpret henv hscoped originalDomain originalBody originalCodomain closed
    domains codomain leftBody rightBody hTarget substitutions fits node.domain node.guard
    node.bodyObservation node.pack node.covered domainAvailable outsideAvailable

end Lean4Lean.AnchoredSource.Adapted
