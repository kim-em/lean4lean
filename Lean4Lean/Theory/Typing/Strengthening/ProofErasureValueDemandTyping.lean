import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueDemandProfile
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Ordinary typed nodes with dependent demand profiles -/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A raw node has an actual typed representative at its dependent profile. -/
def Typing (Δ : List ProofShape) (e : ProofShape) (p : Profile) : Prop :=
  ∃ Γ f T, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ f T ∧ Fits Γ T p ∧ proofErase Γ f = e

/-- Observable nodes retain their syntax under proof erasure. -/
theorem Typing.ne_proof (H : Typing Δ e p) (HV : p.Visible) : e ≠ .proof := by
  obtain ⟨Γ, f, T, hΓ, _, ht, HP, Ee⟩ := H
  intro E
  exact HP.not_isProof hΓ HV ht (proofErase_eq_proof.1 (Ee.trans E))

/-- Ordinary interpreted substitution transports a dependent profile at every
node, without requiring native recovery of any substituted argument. -/
theorem Typing.subst (H : Typing Δ e p) (W : ContextSubstitution Δ Δ' τ) :
    Typing Δ' (e.subst τ) p := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ EΓ
  refine ⟨Γ₀, f.subst σ, T.subst σ, hΓ₀, EΓ₀,
    hf.subst henv.orderedStrong HS hΓ₀, HP.subst hΓ₀ HS, ?_⟩
  rw [proofErase_subst_with hΓ₀ HS hf ES, Ef]

/-- Primitive descent preserves ordinary typing at the exact same profile. -/
theorem Typing.compute (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e p) (R : ScopedCompute Step Δ e out) : Typing Δ out p := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H
  obtain ⟨f', HE, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef R
  exact ⟨Γ, f', T, hΓ, EΓ, HE.hasType.2, HP, Ef'⟩

/-- A domain with an ordinary universe assignment permits weakening the
entire observation, including nodes at ignored parameter types. -/
theorem Typing.weak_interpretation (H : Typing Δ e p) (S : DomainSort Δ A u) :
    ContextSubstitution Δ (A :: Δ) (fun i => .bvar (i+1)) := by
  obtain ⟨Γ, f, T, hΓ, rfl, hf, HP, Ef⟩ := H
  obtain ⟨D, hD, ED⟩ := S.realize hΓ
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  intro Γ' hΓ' EΓ'
  have W := ContextRenaming.of_liftN hΓ hΓD Ctx.LiftN.one
  simpa only [proofEraseCtx, ED, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm]
    using W.interpretation hΓ' EΓ'

/-- Weakening preserves a profile even when its actual type depends on the
surrounding context. -/
theorem Fits.weak (H : Fits Γ T p) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) : Fits (A :: Γ) T.lift p := by
  have W := substEq_of_thinning hΓ (Ctx.Lift'.skip (A := A) .refl)
  simpa only [← lift'_subst, VExpr.subst_id, ← lift_eq_lift'] using H.subst hΓA W

/-- A universe profile exposes an actual universe assignment. -/
theorem Typing.at_sort (H : Typing Δ e .sort) : ∃ u, ControlTyping Δ e (.sort u) := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, ⟨_, u, E⟩, Ef⟩ := H
  exact ⟨u, Γ, f, hΓ, EΓ, hf.defeqU_r henv hΓ E, Ef⟩

/-- An arrow profile exposes its actual dependent telescope and both component
profiles, with the codomain in that telescope's own domain context. -/
theorem Typing.at_arrow (H : Typing Δ e (.arrow p q)) :
    ∃ Γ f A B, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
      env.HasType univs Γ f (.forallE A B) ∧ Fits Γ A p ∧ Fits (A :: Γ) B q ∧
      proofErase Γ f = e := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, ⟨_, A, B, E, HA, HB⟩, Ef⟩ := H
  exact ⟨Γ, f, A, B, hΓ, EΓ, hf.defeqU_r henv hΓ E, HA, HB, Ef⟩

/-- A literal lambda supplies its body's profile in its written domain.
The fresh variable is retained whenever its domain profile is observed. An
ignored domain may be a proposition, so retention is deliberately conditional. -/
theorem Typing.lam_parts (H : Typing Δ (.lam D b) (.arrow p q)) :
    Typing (D :: Δ) b q ∧ (p.Visible → Typing (D :: Δ) (.bvar 0) p) := by
  obtain ⟨Γ, f, A, B, hΓ, rfl, hf, HA, HB, Ef⟩ := H.at_arrow
  obtain ⟨D', b', rfl, _, ED, Eb⟩ := erase_lam_inv Ef
  obtain ⟨⟨u, hD⟩, C, hb⟩ := hf.lam_inv henv hΓ
  have hΓD : OnCtx (D' :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  obtain ⟨⟨_, HD⟩, _, HC⟩ := ((HasType.lam hD hb).uniqU henv hΓ hf).forallE_inv henv hΓ
  have HP := HA.convert hΓ HD.toU.symm
  have HQ := (HB.context hΓD (IsDefEqCtx.succ (.refl hΓ) HD.symm)).convert hΓD HC.toU.symm
  refine ⟨⟨D' :: Γ, b', C, hΓD, by simp only [proofEraseCtx, ED], hb, HQ, Eb⟩, ?_⟩
  intro HV
  have HX : env.HasType univs (D' :: Γ) (.bvar 0) D'.lift := .bvar .zero
  have HPL := HP.weak hΓ hΓD
  exact ⟨D' :: Γ, .bvar 0, D'.lift, hΓD, by simp only [proofEraseCtx, ED], HX, HPL,
    if_neg (HPL.not_isProof hΓD HV HX)⟩

/-- A universe demand cannot be expanded by native function eta. -/
theorem Typing.no_eta_sort (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e .sort) (R : NativeEtaExpansion Step Δ e out) : False := by
  obtain ⟨u, H⟩ := H.at_sort
  exact H.no_eta_sort hstep R

/-- A headed profile has a sort or Pi head, excluding structure-major
typing independently of the arbitrary types in its ignored domains. -/
theorem Typing.no_masked_structure (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Typing Δ e p) (HV : p.Headed)
    (R : NativeMaskedStructureExpansion Step Δ e out) : False := by
  cases HV with
  | sort =>
    obtain ⟨u, H⟩ := H.at_sort
    exact H.no_masked_structure hstep R
  | arrow =>
    obtain ⟨Γ, f, A, B, hΓ, rfl, hf, HA, HB, rfl⟩ := H.at_arrow
    cases R with
    | intro hi hx ha hp RN =>
      obtain ⟨T, hT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv ET
      obtain ⟨_, hS⟩ := hT.isType henv hΓ
      exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hS
        (hT.uniqU henv hΓ hf)

/-- A typed beta redex interprets its ordinary argument substitution at the
displayed binder. No native certificate for the argument is required. -/
theorem Typing.beta_interpretation (H : Typing Δ (.app (.lam D b) a) t) :
    ContextSubstitution (D :: Δ) Δ (ProofShape.Subst.one a) := by
  obtain ⟨Γ, f, T, hΓ, rfl, hf, HP, Ef⟩ := H
  obtain ⟨f₀, a₀, rfl, _, EF, Ea⟩ := erase_app_inv Ef
  obtain ⟨D₀, b₀, rfl, _, ED, Eb⟩ := erase_lam_inv EF
  obtain ⟨_, _, hF, ha⟩ := hf.app_inv henv hΓ
  obtain ⟨⟨u, hD⟩, _, hb⟩ := hF.lam_inv henv hΓ
  have haD := argument_at_displayed_domain hΓ hF (HasType.lam hD hb) ha
  have hΓD : OnCtx (D₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have W : ContextSubstitution (proofEraseCtx (D₀ :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ a₀)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓD haD)
      (erasedSubstAgreement_one hΓD haD)
  rw [proofEraseCtx, ED, Ea] at W
  intro Γ' hΓ' EΓ'
  exact W hΓ' EΓ'

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
