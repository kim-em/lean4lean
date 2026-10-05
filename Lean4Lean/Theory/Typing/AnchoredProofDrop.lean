import Lean4Lean.Theory.Typing.AnchoredProofDropStep
import Lean4Lean.Theory.Typing.AnchoredProofDropProjection

/-! Protected-profile contraction of actual inhabited proof slots. Both
operands and the assigned type may depend on the deleted slots. Only the
finite value and type profiles are required to be literal section lifts.
The chosen retraction is retained through every future and saturation frame.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem drop_rank
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (n : Nat) :
    (∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right : VExpr} {profile : Profile n},
        TypeRelated env U registry Δ left right (profile.rename frame.liftMap) →
        TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile) ∧
    (∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right type : VExpr} {value support : Profile n},
        Related env U registry Δ left right type
          (value.rename frame.liftMap) (support.rename frame.liftMap) →
        Related env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
          (type.subst frame.retract) value support) := by
  induction n with
  | zero =>
    exact ⟨fun {_ _} frame proof {_ _ _} H => H.drop_zero henv hscoped frame proof,
      fun {_ _} frame proof {_ _ _ _ _} H => H.drop_zero henv hscoped frame proof⟩
  | succ n ih =>
    have project : RawPiDropAt env U registry n := by
      intro Γ Δ frame proof left right A B domain rows display
      exact display.dropProjection henv hscoped frame proof
    refine ⟨?_, ?_⟩
    · intro Γ Δ frame proof left right profile H
      exact H.drop_succ henv hscoped project ih.1 ih.2 frame proof
    · intro Γ Δ frame proof left right type value support H
      apply H.drop_of_core henv hscoped (fun {_ _} next insertion {_ _ _ _ _} core =>
        core.drop_succ henv hscoped project ih.1 ih.2 next insertion) frame proof

/-- Contract the specified proof section, preserving an exact protected code
profile and substituting both arbitrary code operands. -/
theorem TypeRelated.drop
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right : VExpr} {profile : Profile n}
    (H : TypeRelated env U registry Δ left right (profile.rename frame.liftMap)) :
    TypeRelated env U registry Γ (left.subst frame.retract) (right.subst frame.retract) profile :=
  (drop_rank henv hscoped n).1 frame insertion H

/-- Contract arbitrary operand/type dependencies through an actual chosen
proof retraction. Future arguments lift through the section before each lower
rank call, so newly introduced data variables remain fixed literally. -/
theorem Related.drop
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ)
    (insertion : ProofInsertion env U Γ Δ frame.liftMap)
    {left right type : VExpr} {value support : Profile n}
    (H : Related env U registry Δ left right type
      (value.rename frame.liftMap) (support.rename frame.liftMap)) :
    Related env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
      (type.subst frame.retract) value support :=
  (drop_rank henv hscoped n).2 frame insertion H

end Lean4Lean.AnchoredSemantics
