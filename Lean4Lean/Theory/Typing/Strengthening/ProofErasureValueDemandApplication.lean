import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueObservationTransport

/-! # Typed applications in the value-observer interpretation -/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Forgetting the profile retains the raw source's actual typing witness. -/
theorem Typing.source (H : Typing Δ e p) : TypedSource Δ e := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, _, Ef⟩ := H
  exact ⟨Γ, f, T, hΓ, EΓ, hf, Ef⟩

/-- An arbitrary typed raw term has an ignored profile. -/
theorem typing_ignored (H : TypedSource Δ e) : Typing Δ e .ignored := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, Ef⟩ := H
  exact ⟨Γ, f, T, hΓ, EΓ, hf, hf.isType henv hΓ, Ef⟩

/-- Reinterpret a profile in any well-formed realization of its erased context. -/
theorem Typing.realize (H : Typing Δ e p) (hΓ : OnCtx Γ (env.IsType univs))
    (EΓ : proofEraseCtx Γ = Δ) :
    ∃ f T, env.HasType univs Γ f T ∧ Fits Γ T p ∧ proofErase Γ f = e := by
  obtain ⟨Γ', f, T, hΓ', EΓ', hf, HP, Ef⟩ := H
  have W := proofEraseCtx_defeq hΓ' hΓ (EΓ'.trans EΓ.symm)
  exact ⟨f, T, hf.defeqDFC henv W, HP.context hΓ W,
    (proofErase_defeqCtx hΓ' W hf).symm.trans Ef⟩

/-- A nonproof representative inherits the profile at its own assignment. -/
theorem Typing.profile_at (H : Typing Δ e p) (hΓ : OnCtx Γ (env.IsType univs))
    (EΓ : proofEraseCtx Γ = Δ) (hf : env.HasType univs Γ f T)
    (hn : ¬ IsProof Γ f) (Ef : proofErase Γ f = e) : Fits Γ T p := by
  obtain ⟨g, U, hg, HP, Eg⟩ := H.realize hΓ EΓ
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ hf hg (Ef.trans Eg.symm)).2 hn
  have HE := (HN.defeq hΓ).of_l henv hΓ hf
  exact HP.convert hΓ (hg.uniqU henv hΓ HE.hasType.2)

/-- A typed application consumes the actual dependent domain profile and
supplies the instantiated result profile. Merely matching profiles is not used
as permission to apply a function: the whole source application is typed. -/
theorem Typing.app_parts (HF : Typing Δ f (.arrow p q)) (HT : TypedSource Δ (.app f a)) :
    Typing Δ a p ∧ Typing Δ (.app f a) q := by
  obtain ⟨Γ, e, T, hΓ, EΓ, he, Ee⟩ := HT
  obtain ⟨f₀, a₀, rfl, hn, Ef, Ea⟩ := erase_app_inv Ee
  obtain ⟨A, B, hf, ha⟩ := he.app_inv henv hΓ
  have HP := HF.profile_at hΓ EΓ hf (not_isProof_fn hΓ hf ha hn) Ef
  obtain ⟨HA, HB⟩ := HP.forallE_inv hΓ
  obtain ⟨u, hA⟩ := HA.isType
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := Ctx.InstN.zero.substEq hΓA ha
  have HB' : Fits Γ (B.inst a₀) q := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
  exact ⟨⟨Γ, a₀, A, hΓ, EΓ, ha, HA, Ea⟩, ⟨Γ, .app f₀ a₀, B.inst a₀, hΓ, EΓ, hf.app ha, HB', Ee⟩⟩

/-- An argument at a proof-domain profile has exactly the proof-marker erasure. -/
theorem Typing.proof_eq (H : Typing Δ e .proof) : e = .proof := by
  obtain ⟨Γ, f, T, _, _, hf, HP, Ef⟩ := H
  exact Ef.symm.trans (proofErase_eq_proof.mpr ⟨T, hf, HP⟩)

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
