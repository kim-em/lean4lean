import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixArity

/-! # General singleton arity after computation of a probe prefix

Pad the computed initial segment with unchanged arguments, replay the whole
typed five-argument prefix, and apply the literal-prefix guard exclusions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_sort_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

/-- Computing any initial segment of a typed Prop-carrier Eq.rec prefix
cannot enable a shorter general singleton guard. Whole-source replay supplies
the actual computed argument typings without inverse typing weakening. -/
theorem proofErase_singleton_eq_prop_computed_prefix_arity
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsourcehead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargethead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Target Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hk : k ≤ 5)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ))
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k) args)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero]) args) out) : k = 5 := by
  let original := [.sort .zero,P,M,m,Q].map (proofErase Γ)
  have hlen : args.length = k := by
    have E := HA.length_eq
    simp only [List.length_take, List.length_map, List.length_cons, List.length_nil] at E
    omega
  have HF : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ)) original
      (args ++ original.drop k) := by
    have HF := HA.append' (Lean4Lean.List.Forall₂.rfl
      (l := original.drop k) (fun _ _ => ScopedCompute.refl (Step := Source) (Δ := proofEraseCtx Γ)))
    simpa only [original, List.take_append_drop] using HF
  have EH : (args ++ original.drop k).take k = args := by
    rw [← hlen, List.take_left]
  generalize Eall : args ++ original.drop k = all at HF EH
  simp only [original, List.map_cons, List.map_nil] at HF
  cases HF with | cons RS HF =>
    cases HF with | cons RP HF =>
      cases HF with | cons RM HF =>
        cases HF with | cons Rm HF =>
          cases HF with | cons RQ HF =>
            cases HF
            have ES : proofErase Γ (.sort .zero) = .sort .zero :=
              if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
            rw [ES] at RS
            cases RS.sort_fixed hsourcehead
            rename_i rp rM rm rq
            have R : ScopedCompute Source (proofEraseCtx Γ)
                (proofErase Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
                (ProofShape.eqRecBeforeMajor v (.succ .zero) (.sort .zero) rp rM rm rq) := by
              rw [eqRecBeforeMajor, proofErase_const_spine hΓ (args := [.sort .zero,P,M,m,Q]) ht hn]
              simp only [List.map_cons, List.map_nil, ProofShape.mkApps, ES]
              exact .app (.app (.app (.app (.app .refl RS) RP) RM) Rm) RQ
            obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_descend hsource hΓ hΓ
              (show Ctx.LiftN 0 0 Γ Γ from .zero []) ht rfl
              (by simpa only [ProofShape.liftN_zero] using R)
            simp only [ProofShape.liftN_zero] at Ee'
            obtain ⟨α, P', M', m', Q', rfl, Eα, EP, EM, Em, EQ⟩ := proofErase_eqRecBeforeMajor_inv Ee'
            obtain rfl := erase_sort_inv Eα
            apply proofErase_singleton_eq_prop_prefix_arity heq htarget htargethead hinert hΓ hk HE.hasType.2
            simpa only [List.map_cons, List.map_nil, ES, EP, EM, Em, EQ, EH] using H

end Lean4Lean.VEnv.Strengthening
