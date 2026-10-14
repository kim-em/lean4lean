import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextMixedApplication

/-! # Consequences of typed contextual composition

Composition would permit changing computation endpoints and substituting distinct
compared arguments. The conclusions here remain conditional on that unproved
composition law; ordinary same-argument substitution is already unconditional.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Typed common composition would transport a certificate to both computation
targets. The target typings are explicit; raw untyped transitivity is not used. -/
theorem ContextCommonComposition.compute_targets
    (Hcomp : ContextCommonComposition Step) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (ha' : env.HasType univs Γ a' T) (hb' : env.HasType univs Γ b' T)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b))
    (Ra : ProofShape.Compute Step (proofErase Γ a) (proofErase Γ a'))
    (Rb : ProofShape.Compute Step (proofErase Γ b) (proofErase Γ b')) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ a') (proofErase Γ b') :=
  Hcomp hΓ ha' hb hb' (Hcomp hΓ ha' ha hb (.compute .refl Ra .refl) H)
    (.compute Rb .refl .refl)

/-- With typed common composition, one typed body respects two compared
arguments. An inferred reflexive lambda comparison gives the application step;
beta transport removes the two wrappers. No substitution closure for Step is
needed for this single-body congruence. -/
theorem ContextCommonComposition.inst_congr
    (Hcomp : ContextCommonComposition Step) (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have Hxy := proofErase_context_compare_reflect hstep hΓ hx hy HX
  have hl := HasType.lam hA hb
  have happ := IsDefEq.appDF hl Hxy
  have hβx := IsDefEq.beta hb hx
  have hβy := (show env.IsDefEqU univs Γ (.app (.lam A b) y) (b.inst y) from
    ⟨_, IsDefEq.beta hb hy⟩).of_l henv hΓ happ.hasType.2
  exact Hcomp.compute_targets hΓ happ.hasType.1 happ.hasType.2 hβx.hasType.2 hβy.hasType.2
    (proofErase_context_apply_independent hstep hΓ hl hl hx hy .refl HX)
    (.beta (proofErase_beta_forward hΓ happ.hasType.1 .beta))
    (.beta (proofErase_beta_forward hΓ happ.hasType.2 .beta))

/-- Typed common composition suffices for substituting distinct compared
arguments in a common-typed body certificate. First substitute x uniformly,
then use single-body congruence to replace x by y on the right. -/
theorem ContextCommonComposition.inst_pair
    (Hcomp : ContextCommonComposition Step) (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.ContextCompare Step (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (HX : ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have Hxy := proofErase_context_compare_reflect hstep hΓ hx hy HX
  have hright := hb'.instN_DF Ctx.InstN.zero hΓA Hxy
  exact Hcomp hΓ (hb.instN henv Ctx.InstN.zero hx) hright.hasType.1 hright.hasType.2
    (proofErase_context_compare_instN hsubst hΓA hx Ctx.InstN.zero hb hb' HB)
    (Hcomp.inst_congr hstep hΓ hA hb' hx hy HX)

end Lean4Lean.VEnv.Strengthening
