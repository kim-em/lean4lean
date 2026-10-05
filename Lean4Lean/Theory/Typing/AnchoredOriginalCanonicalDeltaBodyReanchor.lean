import Lean4Lean.Theory.Typing.AnchoredRecipePiSemantics
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaBodyRecipe
import Lean4Lean.Theory.Typing.AnchoredProfileUnrenaming

/-! Actual right-anchor reconstruction for a retained canonical Pi recipe.
The new admission is computed from the same selected Pi row and paired
binder resource. Its finite support descends from the real private display;
no new source query or semantic admission supplier is introduced. -/


namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The reanchor seed is read from exactly the head need used by the body
recipe. Both raw and semantic argument evidence use the same actual frame. -/
theorem TypeRelated.literalPiRightAdmissionFromFrame
    {n : Nat} {key : Key n} {result ambient : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U (A :: source)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ (A :: source))
    (whole : TypeRelated env U registry target
      ((VExpr.forallE A B).subst σ.tail) ((VExpr.forallE A B).subst τ.tail)
      (.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows)
    (resource : (⟨n, key.input⟩ : Need) ∈ available 0)
    (anchor : key.anchor = σ 0) :
    Admitted env U registry target key (τ 0) (τ 0) := by
  obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed resource (Lookup.zero (Γ := source) (ty := A))
  have raw := substitutions.lookup (Lookup.zero (Γ := source) (ty := A))
  have paired := entry.related
  rw [lift_subst] at raw paired
  exact TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
    (by simpa only [subst] using whole) member anchor raw
    (show Related env U registry target (σ 0) (τ 0) (A.subst σ.tail) key.input entry.support from paired)

end Lean4Lean.AnchoredSource.Adapted
