import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentPayloadObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeArgumentTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Transport of payload histories through dependent control frames

Whole payloads use certificate descent. Ignored frame inputs have arbitrary
types; native eta needs retention only for inputs with a nonempty demand.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open DependentPayloadObservation
open DemandProfile (Typing Sets)
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Updating a whole marked argument preserves its sort demand and typing. -/
theorem TypeArgumentClosure.dependent_payload
    (hstep : ErasedScopedPrimitiveDescent Step) (HC : TypeArgumentClosure Step Γ P)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (EΓ : proofEraseCtx Γ' = Δ) (HP : P a)
    (HT : Typing Δ (a.liftN n) .sort)
    (R : ScopedCompute Step Δ (a.liftN n) out) : Obs P n Δ S out .sort .pi := by
  obtain ⟨a', HP', E⟩ := HC hΓ' W HP (EΓ ▸ R)
  have HT' := HT.compute hstep R
  rw [← E] at HT' ⊢
  exact .payload HT' HP'

/-- Outside a whole payload, opaque primitive heads and level conversion
are excluded. All control expansion frames preserve the finite demand. -/
theorem erased_static_structure_stage_dependent_payload_control
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) : ∀ stage {Δ a b P n S t o},
    ErasedStaticStructureEtaExpansionStage D stage Δ a b → Obs P n Δ S a t o →
    ¬ PrimitiveHead a → (∀ u, a ≠ .sort u) → Obs P n Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b P n S t o R H hn hsort
    rcases R with (R | R) | R
    · exact (hn (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact (hsort _ rfl).elim
      | const => exact (hn trivial).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b P n S t o R H hn hsort
    rcases R with R | R | R | R | R | R
    · exact ih R H hn hsort
    · exact (hn R.2.head).elim
    · exact (hn R.head).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) H.demand.visible R).elim

/-- The same control-frame law permits arbitrary finite guard depth. -/
theorem erased_static_structure_union_dependent_payload_control
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ a b) (H : Obs P n Δ S a t o)
    (hn : ¬ PrimitiveHead a) (hsort : ∀ u, a ≠ .sort u) : Obs P n Δ S b t o := by
  obtain ⟨stage, R⟩ := R
  exact erased_static_structure_stage_dependent_payload_control heq hs stage R H hn hsort

/-- Compatible computation transports arbitrary sort-typed payloads and
their control frames. Whole payloads update by certificate descent; beta and
changing annotations use ordinary typed context interpretation. -/
theorem proofErase_scoped_compute_dependentPayloadObservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b n S t o}, Step Δ a b → Obs P n Δ S a t o →
      ¬ PrimitiveHead a → (∀ u, a ≠ .sort u) → Obs P n Δ S b t o)
    (HC : TypeArgumentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (HS : S.Typed Δ) (H : Obs P n Δ S source t o) : Obs P n Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S t o e T with
  | refl => exact H
  | base R =>
    rcases H.payload_or_headless with ⟨a, rfl, rfl, rfl, HP⟩ | ⟨hn, hsort⟩
    · exact HC.dependent_payload hstep hΓ' W EΓ HP H.typing (.base R)
    · exact hroot R H hn hsort
  | @beta Δ A b a =>
    generalize HE : ProofShape.app (.lam A b) a = src at H
    cases H with
    | payload HT HP => exact HC.dependent_payload hstep hΓ' W EΓ HP HT (HE ▸ ScopedCompute.beta .beta)
    | app HT HF HX => cases HE; exact Obs.beta_frame HT HF HX HS
    | var | lam => cases HE
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE HS (ih₁ hΓ' W ht EΓ Ee HS H)
  | @app Δ f f' a a' RF RX ihf ihx =>
    generalize HE : ProofShape.app f a = src at H
    cases H with
    | payload HT HP => exact HC.dependent_payload hstep hΓ' W EΓ HP HT (HE ▸ ScopedCompute.app RF RX)
    | app HT HF HX =>
      cases HE
      obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
      exact .app (HT.compute hstep (.app RF RX)) (ihf hΓ' W hf EΓ Ef HS HF)
        (fun key hk => ihx hΓ' W hx EΓ Ex HS (HX key hk))
    | var | lam => cases HE
  | @proj Δ m m' s i RM _ =>
    generalize HE : ProofShape.proj s i m = src at H
    cases H with
    | payload HT HP => exact HC.dependent_payload hstep hΓ' W EΓ HP HT (HE ▸ ScopedCompute.proj RM)
    | var | app | lam => cases HE
  | @lam Δ D D' b b' RA RB ihA ihb =>
    generalize HE : ProofShape.lam D b = src at H
    cases H with
    | payload HT HP => exact HC.dependent_payload hstep hΓ' W EΓ HP HT (HE ▸ ScopedCompute.lam RA RB)
    | lam HL HK HB =>
      cases HE
      have HT := HL.compute hstep (.lam RA RB)
      obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, C, hb⟩ := ht.lam_inv henv hΓ'
      have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      have EΓA : proofEraseCtx (A :: Γ') = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
      have SD : DomainSort Δ D u := ⟨Γ', A, hΓ', EΓ, hA, EA⟩
      obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ' hA EΓ EA RA
      have HCtx : IsDefEqCtx env univs [] (A :: Γ') (A' :: Γ') := .succ (.refl hΓ') HA'
      have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
        intro Γ₀ hΓ₀ EΓ₀
        have HH := control_context_substitution HCtx hΓ₀ (EΓA.trans EΓ₀.symm).symm
        simpa only [proofEraseCtx, EA', EΓ] using HH
      apply Obs.lam HT HK
      exact (ihb hΓA W' hb EΓA Eb (HS.cons HL.lam_parts.2 HK SD) HB).context WC
    | var | app => cases HE
  | @forallE Δ A A' B B' RA RB _ _ =>
    generalize HE : ProofShape.forallE A B = src at H
    cases H with
    | payload HT HP => exact HC.dependent_payload hstep hΓ' W EΓ HP HT (HE ▸ ScopedCompute.forallE RA RB)
    | var | app | lam => cases HE

end Lean4Lean.VEnv.Strengthening
