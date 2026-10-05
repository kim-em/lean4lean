import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainRequest
import Lean4Lean.Theory.Typing.StratifiedPiBounds

/-! Read the exact raw Pi inversion target from the semantic witness.
The only uniqueness used below is supplied explicitly by the assigned
comparison interface in the world adequacy theorem. -/
namespace Lean4Lean.VEnv
open VExpr
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- A path with varying edge universes becomes homogeneous once independent
sort typings are compared. No admitted type uniqueness is used. -/
theorem TypeConversion.defeqOfSortUniqueness
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (unique : ∀ {expression u v}, env.HasType U Γ expression (.sort u) →
      env.HasType U Γ expression (.sort v) → u ≈ v)
    (typed : env.HasType U Γ A (.sort u))
    (path : TypeConversion env U Γ A B) : env.IsDefEq U Γ A B (.sort u) := by
  induction path with
  | refl => exact typed
  | @tail middle last v previous edge ih =>
    have levels := unique ih.hasType.2 edge.hasType.1
    have hv := edge.sort_r henv formed
    have hu := typed.sort_r henv formed
    exact ih.trans (.defeqDF (.sortDF hv hu levels.symm) edge)

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem MixedInsertion.pathBackUnderBinder
    (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (hA : env.IsType U Γ A)
    (path : TypeConversion env U (A.lift' ρ :: Δ) (B.lift' ρ.cons) (D.lift' ρ.cons)) :
    TypeConversion env U (A :: Γ) B D := by
  induction route generalizing A B D with
  | proof insertion =>
    obtain ⟨u, typed⟩ := hA
    have under := ProofInsertion.cons insertion typed
    exact (MixedInsertion.proof under).pathBack henv path
  | context chain =>
    apply ((chain.underBinder henv hA).symm henv).path henv
    simpa only [lift'_refl, lift'_depth_zero (l := Lift.cons .refl) rfl] using path
  | comp before after first second =>
    apply first hA
    apply second (before.isType henv hA)
    simpa only [← lift'_comp, Lift.comp] using path

/-- An actual Pi witness returns BOTH original component paths to the
caller's context, including the dependent codomain under its own binder. -/
theorem TypeRelated.literalPiPaths
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (hA : env.IsType U Γ A)
    (related : TypeRelated env U registry Γ (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody (support : Profile n) rows)) :
    TypeConversion env U Γ A C ∧ TypeConversion env U (A :: Γ) B D := by
  have base := related Γ .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody support rows)
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  refine ⟨related.literalPiDomainPath henv formed, ?_⟩
  apply route.pathBackUnderBinder henv hA
  simpa only [witness.leftExposure.literalPi_components.1,
    witness.leftExposure.literalPi_components.2,
    witness.rightExposure.literalPi_components.2] using witness.bodies

/-- This is exactly the stratified public Pi-inversion conclusion. The world
bridge supplies the Pi observation and independent-sort comparison; the
original stratified children, rather than a fresh stratification, fix bounds. -/
theorem TypeRelated.literalPiStratifiedInversion
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (unique : ∀ {context expression u v}, OnCtx context (env.IsType U) →
      env.HasType U context expression (.sort u) →
      env.HasType U context expression (.sort v) → u ≈ v)
    (related : TypeRelated env U registry Γ (.forallE A B) (.forallE A' B')
      (Profile.pi prototypeDomain prototypeBody (support : Profile k) rows))
    (left : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (right : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A :: Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A :: Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A' :: Γ) B' (.sort u) true n' := by
  obtain ⟨m, u, v, leftBound, hu, hv, domain, body⟩ := left.piComponentBounds
  obtain ⟨m', u', v', rightBound, hu', hv', domain', body'⟩ := right.piComponentBounds
  have bodyContext : OnCtx (A :: Γ) (env.IsType U) := ⟨formed, _, domain.hasType⟩
  obtain ⟨domainPath, bodyPath⟩ := related.literalPiPaths henv formed ⟨u, domain.hasType⟩
  have domainEqual := domainPath.defeqOfSortUniqueness henv formed (unique formed) domain.hasType
  have bodyEqual := bodyPath.defeqOfSortUniqueness henv bodyContext (unique bodyContext) body.hasType
  have otherBody : env.HasType U (A :: Γ) B' (.sort v') :=
    body'.hasType.defeqDFC henv (.succ (.refl formed) domainEqual.symm)
  have levels := unique bodyContext bodyEqual.hasType.2 otherBody
  exact stratifiedPiInversionOfOriginalComponents domain body body' leftBound rightBound
    hv hv' levels domainEqual bodyEqual

end Lean4Lean.AnchoredSemantics
