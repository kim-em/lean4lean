import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlPrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlBeta

/-! # Full constructor-control preservation reduced to prefix evolution

Root primitives and higher-order control cases are proved. The only remaining
compatible case is evolution of the function prefix of a saturated constructor
payload. This file names that obligation and proves its exact sufficiency for
the observer. The boundary module refutes this premise for the current payload
syntax. A constructor-function representation is required before this route can
supply unconditional preservation; no strengthening result is claimed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

open private typed_beta_interpretation from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlBeta

namespace ConstructorControlObservation

/-- The one remaining compatible case: a saturated constructor payload is
viewed as an application, and its function prefix and last argument compute
arbitrarily. The evolved application must have a control observation. The
boundary module refutes this premise using constant expansion of the bare
constructor head: the current observer lacks constructor-function demands.
Root primitives and control lambdas are checked independently, but this premise
cannot complete preservation without changing the observer. No strict
smallness relative to the original strengthening problem is asserted. -/
def PrefixPreservation (D : PureObservation.Definitions) (Γ : List VExpr)
    (r : Name) (info : VProjectionInfo) (origin : ProofShape) : Prop :=
  ∀ {Γ' n Δ S e T f a f' a'}, OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' →
    env.HasType univs Γ' e T → proofEraseCtx Γ' = Δ → proofErase Γ' e = .app f a →
    Valuation D Γ origin n Δ S → ConstructorTypePayload D Γ r info origin n Δ (.app f a) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ f f' →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a a' →
    Obs D Γ r info origin n Δ S (.app f' a') .pi

/-- Constructor-prefix preservation is sufficient for complete compatible
computation preservation of this observer. Every other case is discharged:
all enriched root rules, beta, arbitrary controls and changed annotations. -/
theorem Obs.compute_of_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hO : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u))
    (HPrefix : PrefixPreservation D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : Valuation D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S) (H : Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S source o) :
    Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S out o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S o e T with
  | refl => exact H
  | base R =>
    obtain ⟨stage, R⟩ := R
    exact Obs.stage heq hs hΓ hi hp hx HH hD hO stage R H hΓ' W ht EΓ Ee HS
  | beta =>
    apply H.beta_forward
    cases EΓ
    exact typed_beta_interpretation hΓ' ht Ee
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE HS (ih₁ hΓ' W ht EΓ Ee HS H)
  | app RF RX ihf ihx =>
    cases H with
    | payload HP => exact HPrefix hΓ' W ht EΓ Ee HS HP RF RX
    | app HF HX =>
      obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
      exact .app (ihf hΓ' W hf EΓ Ef HS HF) (fun key hk => ihx hΓ' W hx EΓ Ex HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_forallE.elim
  | @lam Δ A A' b b' RA RB _ ihb =>
    cases H with
    | payload HP => have E := HP.head; cases E
    | lam SD HD HB =>
      obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A₀ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A₀ :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      have EΓA : proofEraseCtx (A₀ :: Γ') = A :: Δ := by simp only [proofEraseCtx, EA, EΓ]
      obtain ⟨A₁, HA₁, EA₁⟩ := proofErase_scoped_compute_realize
        (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' hA EΓ EA RA
      have HC : IsDefEqCtx env univs [] (A₀ :: Γ') (A₁ :: Γ') := .succ (.refl hΓ') HA₁
      have WC : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
        intro Γ₀ hΓ₀ EΓ₀
        have HH := control_context_substitution HC hΓ₀ (EΓ₀.trans EΓA.symm)
        simpa only [proofEraseCtx, EA₁, EΓ] using HH
      apply Obs.lam ⟨Γ', A₁, hΓ', EΓ, HA₁.hasType.2, EA₁⟩
      · intro key hk
        have HD' : LowerTypeDemand D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) key n (proofEraseCtx Γ') (proofErase Γ' A₀) := by
          simpa only [EΓ, EA] using HD key hk
        have RA' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
            (proofErase Γ' A₀) A' := by simpa only [EΓ, EA] using RA
        simpa only [EΓ] using HD'.compute_type heq hs hΓ hΓ' W hA RA'
      · exact (ihb hΓA W' hb EΓA Eb (HS.cons SD HD) HB).context WC

/-- The explicit prefix obligation would supply historical native types
after arbitrary whole-program continuation. This connects the preservation
reduction to native type readout, without assuming exact recovery survives. -/
theorem Obs.native_after_compute_of_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hO : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u))
    (HPrefix : PrefixPreservation D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source target)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : Valuation D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S)
    (H : Obs D Γ r info (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ S source o)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ target selected) :
    LowerTypeDemand D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) o n Δ selected := by
  have HO := H.compute_of_prefix heq hs hΓ hi hp hx HH hD hO HPrefix R hΓ' W ht EΓ Ee HS
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ' ht EΓ Ee R
  exact HO.native heq hs hΓ hi hp hx HH hΓ' W HE.hasType.2 EΓ Ee' HS RN

end ConstructorControlObservation
end Lean4Lean.VEnv.Strengthening
