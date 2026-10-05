import Lean4Lean.Theory.Typing.AnchoredExposureCanonicalProjection
import Lean4Lean.Theory.Typing.AnchoredProofDropPi

/-! The two actual Pi exposures are projected with one total canonical
readback. No type-component inversion or semantic substitution is used. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem proofReadback_underBinder (ρ : Lift) (σ : Subst) (e : VExpr) :
    (e.lift' ρ.cons).subst (proofReadback ρ σ).lift =
      (e.subst σ.lift).lift' (Lift.skipN .refl (proofCount ρ)).cons := by
  rw [subst_lift', ← Subst.lift_l_lift, proofReadback_lift_l,
    Subst.lift_r_lift, ← lift'_subst]

/-- Retain both literal projected Pi heads in the same computed world.
The original terminal conversion transports the canonical readback on both
its source and its target, so all component paths use that same substitution. -/
noncomputable def PiWitness.projectRaw
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {lower : Relations n}
    {Γ Δ : List VExpr} {left right A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)} {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (W : PiWitness env U registry lower Δ left right A B domain rows) :
    RawPiDisplay env U registry Γ (left.subst σ) (right.subst σ)
      (A.subst σ) (B.subst σ.lift) := by
  have total : ProofInsertion env U Δ W.leftExposure.postContext W.map := by
    simpa only [W.leftExposure.map_eq] using
      W.leftExposure.generated.comp W.leftExposure.post henv
  have readback := W.leftExposure.terminal.replayTyped henv total hΓ typed
  let context := replayContext Γ W.context W.map σ
  let back := proofReadback W.map σ
  have hContext : OnCtx context (env.IsType U) := by
    obtain ⟨frame, _, _⟩ := total.mapSubstitution_exact henv hΓ typed
    exact (W.leftExposure.terminal.replayContext henv total hΓ typed).targetWF
      henv (frame.targetWF henv)
  let u := Classical.choose W.leftDomainType
  let v := Classical.choose W.rightDomainType
  have leftDomainType : env.HasType U W.context W.leftDomain (.sort u) :=
    Classical.choose_spec W.leftDomainType
  have rightDomainType : env.HasType U W.context W.rightDomain (.sort v) :=
    Classical.choose_spec W.rightDomainType
  have leftTyped := readback.lift henv leftDomainType
  have rightTyped := readback.lift henv rightDomainType
  have leftType := leftDomainType.subst henv readback hContext
  have rightType := rightDomainType.subst henv readback hContext
  have leftWF : OnCtx (W.leftDomain.subst back :: context) (env.IsType U) :=
    ⟨hContext, _, leftType⟩
  have rightWF : OnCtx (W.rightDomain.subst back :: context) (env.IsType U) :=
    ⟨hContext, _, rightType⟩
  refine {
    context := context
    map := .skipN .refl (proofCount W.map)
    leftDomain := W.leftDomain.subst back
    leftBody := W.leftBody.subst back.lift
    rightDomain := W.rightDomain.subst back
    rightBody := W.rightBody.subst back.lift
    leftExposure := Classical.choice (W.leftExposure.projectCanonical henv hscoped hΓ typed)
    rightExposure := Classical.choice (W.rightExposure.projectCanonical henv hscoped hΓ typed)
    leftDomainType := ⟨u, leftType⟩
    rightDomainType := ⟨v, rightType⟩
    leftBodyType := W.leftBodyType.subst henv leftTyped leftWF
    rightBodyType := W.rightBodyType.subst henv rightTyped rightWF
    domains := W.domains.substTarget henv hContext readback
    bodies := W.bodies.substTarget henv leftWF leftTyped
    prototypeDomainPath := ?_
    prototypeBodyPath := ?_ }
  · have path := W.prototypeDomainPath.substTarget henv hContext readback
    simpa only [proofReadback_commute] using path
  · have path := W.prototypeBodyPath.substTarget henv leftWF leftTyped
    simpa only [proofReadback_underBinder] using path

private theorem leftInv_underBinder
    (F : SplitTypedEmbedding env U Γ Δ) (e : VExpr) :
    (e.lift' F.liftMap.cons).subst F.retract.lift = e := by
  have inverse : Subst.lift_l F.liftMap F.retract = Subst.id := by
    funext i
    exact F.leftInv (.bvar i)
  rw [subst_lift', ← Subst.lift_l_lift, inverse, id_lift, subst_id]

/-- The protected prototypes return literally to their original base.
Actual exposed components remain the chosen canonical readbacks, so the
following section construction can identify their slots without a cast. -/
noncomputable def PiWitness.dropRaw
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {lower : Relations n}
    {Γ Δ : List VExpr} {left right A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (F : SplitTypedEmbedding env U Γ Δ)
    (W : PiWitness env U registry lower Δ left right
      (A.lift' F.liftMap) (B.lift' F.liftMap.cons)
      (domain.rename F.liftMap) (Rows.rename F.liftMap rows)) :
    RawPiDisplay env U registry Γ (left.subst F.retract) (right.subst F.retract) A B := by
  let raw := W.projectRaw henv hscoped F.baseWF F.typed
  exact {
    context := raw.context
    map := raw.map
    leftDomain := raw.leftDomain
    leftBody := raw.leftBody
    rightDomain := raw.rightDomain
    rightBody := raw.rightBody
    leftExposure := raw.leftExposure
    rightExposure := raw.rightExposure
    leftDomainType := raw.leftDomainType
    rightDomainType := raw.rightDomainType
    leftBodyType := raw.leftBodyType
    rightBodyType := raw.rightBodyType
    domains := raw.domains
    bodies := raw.bodies
    prototypeDomainPath := by simpa only [F.leftInv] using raw.prototypeDomainPath
    prototypeBodyPath := by simpa only [leftInv_underBinder] using raw.prototypeBodyPath }

end Lean4Lean.AnchoredSemantics
