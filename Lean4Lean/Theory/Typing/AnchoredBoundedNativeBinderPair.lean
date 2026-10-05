import Lean4Lean.Theory.Typing.AnchoredBoundedBinder
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture

/-! One actual registered native binder under paired argument realizations.
Only the original domain formation theorem interprets its stored certificate;
the new argument's domain evidence is not an independent caller premise. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem LambdaGuard.nativeBinderPair
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {domain : VExpr} {level : VLevel}
    (formed : env.HasType U source domain (.sort level))
    (original : Joint current fuel env U registry source domain domain (.sort level))
    (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    {key : Key n} {support packed : Profile n} {domainFoot required outside : Footprint}
    (domainCode : CodeCert env U registry target locals σ domain support domainFoot)
    (domainBound : domainCode.nativeDepth current ≤ fuel)
    (guard : LambdaGuard env U registry target σ domain key support)
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (resources : (domainFoot ++ outside).Available available)
    {argument : VExpr} (admitted : Admitted env U registry target key argument argument) :
    Ctx.SubstEq env U target (σ.cons key.anchor) (τ.cons argument) (domain :: source) ∧
    PairedFits current fuel env U registry (domain :: source) target (Locals.push locals)
      (σ.cons key.anchor) (τ.cons argument)
      (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) available) ∧
    required.Available
      (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) available) := by
  have domainResources : domainFoot.Available available :=
    fun i need hm => resources i need (List.mem_append_left _ hm)
  have outsideResources : outside.Available available :=
    fun i need hm => resources i need (List.mem_append_right _ hm)
  obtain ⟨rawArgument, _, oldSupport, _, _, _, anchor, _⟩ := admitted
  have semanticArgument := Related.convert henv guard.inputTyped guard.domains anchor
  have rawPair := guard.path.cast rawArgument
  have bounds := pack.atomized_localNeeds
  refine ⟨.cons raw formed rawPair, ?_, pack.available_atomized_localNeeds outsideResources⟩
  exact fits.pushGraded henv hscoped hTarget closed
    (original target locals σ τ available closed hTarget raw fits).1 domainCode domainBound domainResources
    guard.inputTyped semanticArgument (required.localNeeds ++ required.localNeeds.flatMap Need.singletons)
    (fun need hm => (bounds need hm).1)
    (fun need hm atom ha => covered atom ((bounds need hm).2 atom ha))

end Lean4Lean.AnchoredSource.Adapted.Staged
