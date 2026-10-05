import Lean4Lean.Theory.Typing.AnchoredSourceEnvelope
import Lean4Lean.Theory.Typing.AnchoredSourcePruning

/-! The beta argument's actual source domain is interpreted by its original
formation child. The original argument observation is retained; selecting a
domain support changes its target typing support and its code provenance,
not its computational variable requirements. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The target observation comes from the original argument child. The
pruned type certificate comes from the chosen source lambda domain, before
that child chooses an unrelated support for the same raw argument type. -/
structure ArgumentAtDomain (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) (argument A : VExpr) (input support : Profile n)
    (domainFootprint : Footprint) where
  targetFootprint : Footprint
  targetObservation : Obs env U registry target locals right argument input targetFootprint
  targetAvailable : targetFootprint.Available available
  typeFootprint : Footprint
  certificate : PrunedCodeCert env U registry target locals left A support typeFootprint
  selected : Footprint.Atomizes typeFootprint domainFootprint
  typeAvailable : typeFootprint.Available (Valuation.atomize available)
  typed : input.HasType support
  related : Related env U registry target (argument.subst left) (argument.subst right)
    (A.subst left) input support

/-- The selected domain support is supplied by the actual original `HA`
child. `Harg` supplies value relatedness, which is retagged at that same raw
source type. Both original children are used once at the unchanged valuation.
Only the finite provenance selection uses its explicit atomized closure. -/
theorem argumentAtDomain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {argument A : VExpr} {level : VLevel}
    {input support : Profile n} {valueFootprint domainFootprint : Footprint}
    (originalArgument : Joint env U registry source argument argument A)
    (originalDomain : Joint env U registry source A A (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : Fits env U registry source target locals left right available)
    (observation : Obs env U registry target locals left argument input valueFootprint)
    (valueAvailable : valueFootprint.Available available)
    (domain : CodeCert env U registry target locals left A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support) :
    Nonempty (ArgumentAtDomain env U registry target locals left right available
      argument A input support domainFootprint) := by
  have argumentProducer : Transfer env U registry target locals left right available
      argument argument A :=
    (originalArgument target locals left right available hTarget substitutions fits).1
  obtain ⟨value⟩ := argumentProducer observation valueAvailable
  have domainProducer : Transfer env U registry target locals left left available A A (.sort level) :=
    (originalDomain target locals left left available hTarget substitutions.left fits.left).1
  obtain ⟨domainValue⟩ := domain.transfer henv hscoped hTarget domainProducer domainAvailable
  obtain ⟨pruned⟩ := domain.prune
  exact ⟨{
    targetFootprint := value.resultFootprint
    targetObservation := value.observation
    targetAvailable := value.resultAvailable
    typeFootprint := pruned.footprint
    certificate := pruned.certificate
    selected := pruned.atomizes
    typeAvailable := pruned.atomizes.available domainAvailable
    typed := typed
    related := Related.retag henv typed domainValue.related value.related }⟩

/-- In the erased-binder beta case, minimal support forces the empty type
profile. Its pruned certificate therefore contributes no annotation leaves,
even when the old certificate had retained leaves through `down` or a map. -/
theorem ArgumentAtDomain.erased_domain
    {input support : Profile n}
    (result : ArgumentAtDomain env U registry target locals left right available
      argument A input support domainFootprint)
    (empty : input = .empty) (minimal : Minimal input support) :
    result.typeFootprint = [] := by
  subst input
  have hs : support = .empty := by cases minimal; rfl
  cases hs
  rcases result with ⟨_, _, _, _, certificate, _, _, _, _⟩
  cases certificate
  rfl

end Lean4Lean.AnchoredSource
