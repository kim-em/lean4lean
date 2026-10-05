import Lean4Lean.Theory.Typing.AnchoredExposureDrop
import Lean4Lean.Theory.Typing.AnchoredCoreContext

/-! The closed rank-zero case of protected-profile proof DROP. Future worlds
retain the specified retraction, and the chosen saturation core moves forward
once through the actual post-proof history. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Universe observations contract along an actual proof section. -/
theorem TypeRelated.drop_zero
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right : VExpr} {profile : Profile 0}
    (H : TypeRelated env U registry Δ left right (profile.rename frame.liftMap)) :
    TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile := by
  intro V τ future atom member
  obtain ⟨W, i, j, proof, largerFuture, square, next, nextMap, nextRetract⟩ :=
    frame.pushoutChosen insertion future henv
  subst i
  have original := H W j largerFuture atom (by
    simpa [Profile.rename, Profile.atoms, Atom.rename] using member)
  have contracted := original.drop henv hscoped next
  have commute (e : VExpr) : (e.lift' j).subst next.retract = (e.subst frame.retract).lift' τ := by
    rw [subst_lift', nextRetract, lift'_subst]
  simpa only [commute, CoreRelated, TypeRelated, relations] using contracted

/-- A rank-zero chosen core contracts without requiring its operands or its
assigned type to be lifts from the smaller context. -/
theorem CoreRelated.drop_zero
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right type : VExpr} {value support : Profile 0}
    (H : CoreRelated env U registry Δ left right type
      (value.rename frame.liftMap) (support.rename frame.liftMap)) :
    CoreRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
      (type.subst frame.retract) value support :=
  ⟨Profile.rename_hasType_iff.mp H.1,
    H.2.1.drop_zero henv hscoped frame insertion,
    H.2.2.drop_zero henv hscoped frame insertion⟩

/-- Saturation transport is independent of rank once the current-rank concrete
core contraction has been established. The only local semantic premise is
that current core step, which the rank induction supplies. -/
theorem Related.drop_of_core
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (coreDrop : ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right type : VExpr} {value support : Profile n},
        CoreRelated env U registry Δ left right type
          (value.rename frame.liftMap) (support.rename frame.liftMap) →
        CoreRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
          (type.subst frame.retract) value support)
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right type : VExpr} {value support : Profile n}
    (H : Related env U registry Δ left right type
      (value.rename frame.liftMap) (support.rename frame.liftMap)) :
    Related env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
      (type.subst frame.retract) value support := by
  cases n <;> intro atom member V τ future
  all_goals
    obtain ⟨W, i, j, proof, largerFuture, square, next, nextMap, nextRetract⟩ :=
      frame.pushoutChosen insertion future henv
    subst i
    have original := H (atom.rename frame.liftMap) (List.mem_map_of_mem member) W j largerFuture
    rcases original with empty | ⟨Ω, υ, post, core⟩
    · cases empty
    obtain ⟨extension⟩ := next.extendProof proof post henv
    have moved := CoreRelated.future henv hscoped extension.oldFuture core
    have composite : ((frame.liftMap.comp j).comp υ).comp extension.oldMap =
        (τ.comp extension.smallMap).comp extension.drop.liftMap := by
      rw [square]
      calc
        ((τ.comp next.liftMap).comp υ).comp extension.oldMap =
            τ.comp ((next.liftMap.comp υ).comp extension.oldMap) := by
          simp only [Lift.comp_assoc]
        _ = (τ.comp extension.smallMap).comp extension.drop.liftMap := by
          rw [extension.square, Lift.comp_assoc]
    have moved' : CoreRelated env U registry extension.context
        (((left.lift' j).lift' υ).lift' extension.oldMap)
        (((right.lift' j).lift' υ).lift' extension.oldMap)
        (((type.lift' j).lift' υ).lift' extension.oldMap)
        ((((Profile.singleton atom).rename τ).rename extension.smallMap).rename extension.drop.liftMap)
        (((support.rename τ).rename extension.smallMap).rename extension.drop.liftMap) := by
      simpa only [← Profile.rename_singleton, ← Profile.rename_comp, composite] using moved
    have contracted := coreDrop extension.drop extension.proofSection moved'
    have commute (e : VExpr) :
        (((e.lift' j).lift' υ).lift' extension.oldMap).subst extension.drop.retract =
          ((e.subst frame.retract).lift' τ).lift' extension.smallMap := by
      rw [subst_lift', extension.restrict, extension.commute]
      simp only [subst_lift', nextRetract, lift'_subst]
    refine .inr ⟨extension.smallContext, extension.smallMap, extension.smallFrame, ?_⟩
    simpa only [commute, CoreRelated, TypeRelated, relations] using contracted

theorem Related.drop_zero
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right type : VExpr} {value support : Profile 0}
    (H : Related env U registry Δ left right type
      (value.rename frame.liftMap) (support.rename frame.liftMap)) :
    Related env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
      (type.subst frame.retract) value support :=
  H.drop_of_core henv hscoped (fun {_ _} next proof {_ _ _ _ _} h => CoreRelated.drop_zero henv hscoped next proof h)
    frame insertion

end Lean4Lean.AnchoredSemantics
