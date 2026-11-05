import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainNative

/-! # Native expansions preserve historical lambda-domain observations -/
namespace Lean4Lean.VEnv.Strengthening.LambdaDomainObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob Sets)
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
private theorem primitive_const_spine (args : List ProofShape) :
    PrimitiveHead (ProofShape.mkApps (.const c ls) args) := by
  have H {f : ProofShape} (h : PrimitiveHead f) : PrimitiveHead (ProofShape.mkApps f args) := by
    induction args generalizing f with
    | nil => exact h
    | cons a args ih => exact ih h
  exact H trivial

/-- Every native identity frame records its actual selected annotation's
recursive history, rather than demanding later recovery from its argument. -/
theorem Obs.native_identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : Obs D Γ anchor n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ anchor n Δ S)
    (R : NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    Obs D Γ anchor n Δ S out o := by
  cases R with
  | intro RN =>
    have HN := H.native heq hs hΓ hΓ' W ht EΓ Ee HS RN
    obtain ⟨u, _, SD⟩ := HN.sort_witness
    apply Obs.app (keys := [o])
    · apply Obs.lam SD
      · intro key hk
        obtain rfl := List.mem_singleton.1 hk
        exact HN
      · exact .var (by simp [Sets.cons])
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact H

/-- Native eta either exposes a payload domain already reached from the
anchor, or preserves a control-function demand using its observed input type.
Only demanded fresh variables must be retained; ignored inputs may be proofs. -/
theorem Obs.native_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : Obs D Γ anchor n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ anchor n Δ S)
    (R : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) :
    Obs D Γ anchor n Δ S out o := by
  cases R with
  | intro RN SD =>
    have HN := H.native heq hs hΓ hΓ' W ht EΓ Ee HS RN
    cases o with
    | sort => simp only [LowerDomainDemand, NativeTypeDemand] at HN
    | pi => exact .payload HN.payload_parts
    | app keys result =>
      have HD := HN.function_parts.1
      apply Obs.lam SD HD
      apply Obs.app (H.lift SD)
      intro key hk
      have E : etaArgument _ = .bvar 0 := if_neg ((HD key hk).sort_ne_zero SD)
      rw [E]
      exact .var hk

/-- Structure expansion cannot consume an observed function: its native
family type would have an opaque head, excluded by the recursive type demand. -/
theorem Obs.no_structure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : Obs D Γ anchor n Δ S raw o)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = raw)
    (HS : Valuation D Γ anchor n Δ S)
    (R : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ raw out) : False := by
  cases R with
  | intro _ _ _ _ RN =>
    exact (H.native heq hs hΓ hΓ' W ht EΓ Ee HS RN).not_primitiveHead (primitive_const_spine _)

/-- Every finite static structure/function-eta stage preserves the marked
lambda-domain observation at every temporary control depth. -/
theorem Obs.stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : ∀ stage {n Δ S raw out o Γ' e T},
    ErasedStaticStructureEtaExpansionStage D stage Δ raw out → Obs D Γ anchor n Δ S raw o →
    OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' → env.HasType univs Γ' e T →
    proofEraseCtx Γ' = Δ → proofErase Γ' e = raw → Valuation D Γ anchor n Δ S →
    Obs D Γ anchor n Δ S out o := by
  intro stage
  induction stage with
  | zero =>
    intro n Δ S raw out o Γ' e T R H hΓ' W ht EΓ Ee HS
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion ⟨Γ', .sort (.succ .zero), hΓ', EΓ,
        HasType.sort (by trivial), if_neg (not_isProof_of_sort hΓ' (HasType.sort (by trivial)))⟩
  | succ stage ih =>
    intro n Δ S raw out o Γ' e T R H hΓ' W ht EΓ Ee HS
    rcases R with R | R | R | R | R | R
    · exact ih R H hΓ' W ht EΓ Ee HS
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity heq hs hΓ hΓ' W ht EΓ Ee HS (R.mono (fun H => ⟨stage, H⟩))
    · exact H.native_eta heq hs hΓ hΓ' W ht EΓ Ee HS (R.mono (fun H => ⟨stage, H⟩))
    · exact (H.no_structure heq hs hΓ hΓ' W ht EΓ Ee HS (R.mono (fun H => ⟨stage, H⟩))).elim

end Lean4Lean.VEnv.Strengthening.LambdaDomainObservation
