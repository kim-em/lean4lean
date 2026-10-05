import Lean4Lean.Theory.Typing.CanonicalTraceSubstitution
import Lean4Lean.Theory.Typing.TypedWorldProofSubstitution
import Lean4Lean.Theory.Typing.AnchoredExposurePost

/-! Project actual successful exposures along a chosen typed substitution.
The canonical fresh telescope is rebuilt literally; post proofs are rebuilt
by their actual insertion history. This gives the sort case of proof DROP
without assuming a semantic substitution operation. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem front_skip_inv
    (H : ProofInsertion env U Δ (P :: Ω) ρ.skip) :
    ∃ q, ProofInsertion env U Δ Ω ρ ∧
      env.HasType U Ω P (.sort .zero) ∧ env.HasType U Ω q P := by
  cases H with
  | skip previous hP hq => exact ⟨_, previous, hP, hq⟩

/-- Retain exactly the fresh binders in a substituted canonical trace.
The selected substitution is lifted, rather than replaced by a default
retraction supplied by the proof insertion. -/
theorem ProofInsertion.substFront
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Γ Δ : List VExpr} {σ : Subst} (hΓ : OnCtx Γ (env.IsType U))
    (typed : Ctx.SubstEq env U Γ σ σ Δ) (added : List VExpr)
    (front : ProofInsertion env U Δ (added ++ Δ) (.skipN .refl added.length)) :
    ProofInsertion env U Γ (substAdded σ added ++ Γ) (.skipN .refl added.length) ∧
    Ctx.SubstEq env U (substAdded σ added ++ Γ)
      (σ.liftN added.length) (σ.liftN added.length) (added ++ Δ) := by
  induction added with
  | nil => exact ⟨.refl hΓ, typed⟩
  | cons P rest ih =>
    obtain ⟨q, previous, hP, hq⟩ := front_skip_inv front
    obtain ⟨front', typed'⟩ := ih previous
    have hP' := hP.subst henv typed' (front'.targetWF henv)
    have hq' := hq.subst henv typed' (front'.targetWF henv)
    exact ⟨front'.skip hP' hq', typed'.lift henv hP⟩

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- A concrete exposure projection under any typed substitution. The final
substitution is typed at the old pre-conversion post-context; the old terminal
context conversion is first traversed backwards. All rebuilt worlds and
substitutions come from the actual trace and proof insertion histories. -/
theorem Exposure.project
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {ρ : Lift} {expression head : VExpr} {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (E : Exposure env U registry Δ expression Ω ρ head) :
    ∃ Ω' κ σ', ProofInsertion env U Γ Ω' κ ∧
      Ctx.SubstEq env U Ω' σ' σ' E.postContext ∧
      (∀ e : VExpr, (e.lift' ρ).subst σ' = (e.subst σ).lift' κ) ∧
      Nonempty (Exposure env U registry Γ (expression.subst σ) Ω' κ (head.subst σ')) := by
  obtain ⟨front, frontTyped⟩ := E.generated.substFront henv hΓ typed E.added
  obtain ⟨Ω', κ, σ', post, postTyped, commute⟩ :=
    E.post.mapSubstitution henv (front.targetWF henv) frontTyped
  let map := (Lift.skipN .refl E.added.length).comp κ
  have square (e : VExpr) : (e.lift' ρ).subst σ' = (e.subst σ).lift' map := by
    rw [← E.map_eq, lift'_comp, commute]
    simp only [map, lift'_comp,
      show ∀ e : VExpr, e.lift' (.skipN .refl E.added.length) = e.liftN E.added.length
        from fun e => lift'_consN_skipN (k := 0), liftN_subst_liftN]
  have sound := ((E.terminal.symm henv).path henv E.sound).substTarget henv
    (post.targetWF henv) postTyped
  have headType := ((E.terminal.symm henv).isType henv E.headType).subst henv
    postTyped (post.targetWF henv)
  refine ⟨Ω', map, σ', front.comp post henv, postTyped, square, ⟨{
    added := substAdded σ E.added
    result := E.result.subst (σ.liftN E.added.length)
    postMap := κ
    trace := E.trace.subst hscoped σ
    generated := by simpa only [substAdded_length] using front
    postContext := Ω'
    post := post
    terminal := .refl
    map_eq := by simp only [substAdded_length]; rfl
    result_eq := ?_
    sound := by simpa only [square] using sound
    headType := headType }⟩⟩
  rw [← commute E.result, E.result_eq]

/-- Universe heads are unaffected by substitution. The two rebuilt proof
histories are amalgamated, so the resulting sort comparison has one context
and one map even when the original exposures used different native fronts. -/
theorem SortRelated.project
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {left right : VExpr} {relevant : Bool} {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (H : SortRelated env U registry Δ left right relevant) :
    SortRelated env U registry Γ (left.subst σ) (right.subst σ) relevant := by
  obtain ⟨Ω, ρ, u, v, ⟨leftExposure⟩, ⟨rightExposure⟩, levels, relevance⟩ := H
  obtain ⟨Ωl, κl, σl, Il, _, _, ⟨El⟩⟩ := leftExposure.project henv hscoped hΓ typed
  obtain ⟨Ωr, κr, σr, Ir, _, _, ⟨Er⟩⟩ := rightExposure.project henv hscoped hΓ typed
  obtain ⟨V, i, j, hi, hj, maps⟩ := Il.pushoutProof Ir henv
  refine ⟨V, κl.comp j, u, v, ⟨?_⟩, ⟨?_⟩, levels, relevance⟩
  · simpa only [subst, lift'] using El.postInsertion henv hj
  · rw [maps]
    simpa only [subst, lift'] using Er.postInsertion henv hi

theorem SortRelated.drop
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {left right : VExpr} {relevant : Bool}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frame : SplitTypedEmbedding env U Γ Δ)
    (H : SortRelated env U registry Δ left right relevant) :
    SortRelated env U registry Γ (left.subst frame.retract)
      (right.subst frame.retract) relevant :=
  H.project henv hscoped frame.baseWF frame.typed

end Lean4Lean.AnchoredSemantics
