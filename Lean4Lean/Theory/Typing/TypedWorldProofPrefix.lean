import Lean4Lean.Theory.Typing.TypedWorldProofSubstitutionExact
import Lean4Lean.Theory.Typing.AnchoredExposureDrop

/-! Factor an already generated proof prefix through the canonical total
readback. Fresh prefix variables remain variables; only the original base
is instantiated. -/
namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem front_tail
    (H : ProofInsertion env U Δ (P :: Ω) ρ.skip) :
    ProofInsertion env U Δ Ω ρ := by cases H; assumption

theorem ProofInsertion.mapSubstitutionWithPrefix
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Γ Δ : List VExpr} {σ : Subst} (hΓ : OnCtx Γ (env.IsType U))
    (typed : Ctx.SubstEq env U Γ σ σ Δ) (added : List VExpr)
    (front : ProofInsertion env U Δ (added ++ Δ) (.skipN .refl added.length))
    {Ω : List VExpr} {τ : Lift}
    (post : ProofInsertion env U (added ++ Δ) Ω τ) :
    ProofInsertion env U (substAdded σ added ++ Γ)
      (replayContext Γ Ω ((Lift.skipN .refl added.length).comp τ) σ)
      (proofFrontMap added.length τ) := by
  generalize source_eq : added ++ Δ = source at post
  induction post generalizing added Δ Γ σ with
  | @refl source hSource =>
    subst source
    have hNew := (front.substFront henv hΓ typed added).1.targetWF henv
    have reflMap : proofFrontMap added.length .refl = .refl := by cases added <;> rfl
    simpa only [Lift.comp, reflMap, replayContext_front] using
      (ProofInsertion.refl hNew)
  | @skip source Ω τ P q previous hP hq ih =>
    have next := ih hΓ typed added front source_eq
    have total : ProofInsertion env U Δ Ω
        ((Lift.skipN .refl added.length).comp τ) := by
      subst source
      exact front.comp previous henv
    obtain ⟨frame, readback, _⟩ := total.mapSubstitution_exact henv hΓ typed
    have formed := hP.subst henv readback (frame.targetWF henv)
    have witness := hq.subst henv readback (frame.targetWF henv)
    cases added with
    | nil => simpa only [List.length_nil, Lift.skipN, Lift.refl_comp, proofFrontMap,
        proofCount, Lift.depth, replayContext, List.nil_append, substAdded] using
        next.skip formed witness
    | cons A added => exact next.skip formed witness
  | @cons source Ω τ A u previous hA ih =>
    cases added with
    | nil =>
      simp only [List.nil_append] at source_eq
      subst Δ
      simpa only [List.length_nil, List.nil_append, substAdded, Lift.skipN,
        Lift.refl_comp, proofFrontMap] using
        (ProofInsertion.mapSubstitution_exact henv (previous.cons hA) hΓ typed).1
    | cons P added =>
      simp only [List.cons_append, List.cons.injEq] at source_eq
      obtain ⟨rfl, source_eq⟩ := source_eq
      have previousFront := front_tail front
      have next := ih hΓ typed added previousFront source_eq
      have hA' : env.HasType U (substAdded σ added ++ Γ)
          (P.subst (σ.liftN added.length)) (.sort u) := by
        have inputTyped := (previousFront.substFront henv hΓ typed added).2
        have inputWF := (previousFront.substFront henv hΓ typed added).1.targetWF henv
        subst source
        exact hA.subst henv inputTyped inputWF
      have result := next.cons hA'
      have body := proofReadback_front added.length τ σ P
      simpa only [List.length_cons, Lift.skipN, Lift.comp, replayContext,
        proofFrontMap, substAdded, List.cons_append, body] using result

end Lean4Lean.VEnv
