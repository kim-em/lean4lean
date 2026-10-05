import Lean4Lean.Theory.Typing.TypedWorldMixed
import Lean4Lean.Theory.Typing.TypedWorldAmalgamation
import Lean4Lean.Theory.Typing.TypedWorldProofComparison

/-! Rebuild an actual proof insertion along a chosen typed substitution.
New proof slots are introduced over the complete target base, so a chosen
witness may refer to any retained variable, including a newer one. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

/-- Pull a proof history through a typed substitution. The returned
substitution agrees with the ORIGINAL chosen substitution on every old term;
no default retraction is substituted for the caller's witness choices. -/
theorem ProofInsertion.mapSubstitution
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Δ Ω : List VExpr} {τ : Lift} (insertion : ProofInsertion env U Δ Ω τ)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {σ : Subst}
    (typed : Ctx.SubstEq env U Γ σ σ Δ) :
    ∃ Γ' κ σ', ProofInsertion env U Γ Γ' κ ∧ Ctx.SubstEq env U Γ' σ' σ' Ω ∧
      (∀ expression : VExpr, (expression.lift' τ).subst σ' = (expression.subst σ).lift' κ) := by
  induction insertion generalizing Γ σ with
  | refl hΔ =>
    exact ⟨Γ, .refl, σ, .refl hΓ, typed, fun _ => by simp only [lift'_refl]⟩
  | @skip Δ Ω τ P q previous hP hq ih =>
    obtain ⟨Γ', κ, σ', frame, substituted, commute⟩ := ih hΓ typed
    have hP' := hP.subst henv substituted (frame.targetWF henv)
    have hq' := hq.subst henv substituted (frame.targetWF henv)
    refine ⟨P.subst σ' :: Γ', κ.skip, σ'.lift, frame.skip hP' hq',
      substituted.lift henv hP, ?_⟩
    intro expression
    rw [show expression.lift' τ.skip = (expression.lift' τ).lift from by
      rw [lift_eq_lift', ← lift'_comp]; rfl]
    rw [lift_subst, show σ'.lift.tail = σ'.lift_r (.skip .refl) from by
      funext i; simp only [Subst.tail, Subst.lift, Subst.lift_r, lift_eq_lift']]
    rw [← lift'_subst, commute]
    rw [← lift'_comp]
    rfl
  | @cons Δ Ω τ A u previous hA ih =>
    cases typed with
    | cons typed hA' head =>
      obtain ⟨Γ', κ, σ', frame, substituted, commute⟩ := ih hΓ typed
      let result := σ'.cons ((σ.head).lift' κ)
      have changed : (A.lift' τ).subst σ' = (A.subst σ.tail).lift' κ := commute A
      have head' := head.weak' henv frame.weakening
      have newTyped : Ctx.SubstEq env U Γ' result result (A.lift' τ :: Ω) := by
        refine .cons substituted (hA.weak' henv previous.weakening) ?_
        change env.HasType U Γ' (σ.head.lift' κ) ((A.lift' τ).subst σ')
        rw [changed]
        exact head'
      refine ⟨Γ', κ, result, frame, newTyped, ?_⟩
      intro expression
      rw [subst_lift', lift'_subst]
      apply congrArg (expression.subst ·)
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        have h := commute (.bvar i)
        simpa only [lift', subst_bvar, Subst.tail, Subst.lift_l, Subst.lift_r,
          Lift.liftVar, result, Subst.cons] using h

/-- The concrete common world after replaying a post-frame. Old and new
proof slots coexist; the chosen retraction identifies their corresponding
inhabitants. All old semantic data moves forward before any contraction. -/
structure ProofDropExtension {env : VEnv} {U : Nat} {Γ Δ : List VExpr}
    (original : SplitTypedEmbedding env U Γ Δ) (Ω : List VExpr) (τ : Lift) where
  smallContext : List VExpr
  smallMap : Lift
  smallFrame : ProofInsertion env U Γ smallContext smallMap
  context : List VExpr
  oldMap : Lift
  oldFuture : FutureInsertion env U Ω context oldMap
  drop : SplitTypedEmbedding env U smallContext context
  proofSection : ProofInsertion env U smallContext context drop.liftMap
  readback : Subst
  typed : Ctx.SubstEq env U smallContext readback readback Ω
  restrict : Subst.lift_l oldMap drop.retract = readback
  commute : ∀ expression : VExpr,
    (expression.lift' τ).subst readback = (expression.subst original.retract).lift' smallMap
  square : (original.liftMap.comp τ).comp oldMap = smallMap.comp drop.liftMap

/-- Extend the specified proof-slot contraction through ANY actual old
proof insertion, including insertions underneath retained newer variables.
The additional proof copies resolve the apparent ordering conflict without
exchange, arbitrary substitutions in semantic relations, or a model axiom. -/
theorem SplitTypedEmbedding.extendProof
    {env : VEnv} {U : Nat} {Γ Δ Ω : List VExpr} {τ : Lift}
    (F : SplitTypedEmbedding env U Γ Δ)
    (proofSection : ProofInsertion env U Γ Δ F.liftMap)
    (post : ProofInsertion env U Δ Ω τ) (henv : env.Ordered) :
    Nonempty (ProofDropExtension F Ω τ) := by
  obtain ⟨V, κ, σ, frame, typed, commute⟩ :=
    post.mapSubstitution henv F.baseWF F.typed
  obtain ⟨M⟩ := (proofSection.comp post henv).amalgam frame.toFuture henv
  have agree : Subst.lift_l (F.liftMap.comp τ) σ = Subst.lift_l κ Subst.id := by
    funext i
    have hi := F.leftInv (.bvar i)
    have h := commute ((VExpr.bvar i).lift' F.liftMap)
    change F.retract (F.liftMap.liftVar i) = .bvar i at hi
    change σ (τ.liftVar (F.liftMap.liftVar i)) = (F.retract (F.liftMap.liftVar i)).lift' κ at h
    change σ ((F.liftMap.comp τ).liftVar i) = .bvar (κ.liftVar i)
    rw [Lift.liftVar_comp, h, hi]
    rfl
  obtain ⟨retract, left, right⟩ := M.merge σ Subst.id agree
  have mergedTyped : Ctx.SubstEq env U V retract retract M.context := by
    apply M.typing
    · rw [left]; exact typed
    · rw [right]; exact .id henv (frame.targetWF henv)
  let G := M.proof.withRetraction henv retract mergedTyped
    (by intro e; rw [subst_lift', right, subst_id])
  exact ⟨{
    smallContext := V
    smallMap := κ
    smallFrame := frame
    context := M.context
    oldMap := M.rightMap
    oldFuture := M.future
    drop := G
    proofSection := M.proof
    readback := σ
    typed := typed
    restrict := left
    commute := commute
    square := M.commute }⟩

end Lean4Lean.VEnv
