import Lean4Lean.Theory.Typing.Strengthening.PatternComputation
import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping

/-! # Replay of reflexive type casts from source typing

A cast whose two endpoint types are syntactically identical has a context-free
K computation. Its typing premises are recovered from the canonical recursor
spine; its proof argument may be a variable. No strengthening is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- The canonical type of a full cast determines the actual typings of its
endpoint types, proof, and payload, regardless of the source's supplied type. -/
theorem typeCast_typings (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (typeCast u X Y proof value)) :
    u.WF U ∧ env.HasType U Γ X (.sort u) ∧ env.HasType U Γ Y (.sort u) ∧
      env.HasType U Γ proof (eqApp (.succ u) (.sort u) X Y) ∧
      env.HasType U Γ value X := by
  have H' : VExpr.WF env U Γ (mkApps (.const ``Eq.rec [u, .succ u])
      [.sort u, X, castMotive u X, value, Y, proof]) := H
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ H'
  obtain ⟨ci, hci, hw, _⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.2.1] at hci
  cases Option.some.inj hci
  have hu : u.WF U := hw _ (by simp)
  have hhead := HasType.const (Γ := Γ) heq.2.2.1 hw (by rfl)
  obtain ⟨res, ht, _⟩ := HasType.mkApps_telescope henv hΓ hhead H' (by rfl)
  cases ht with | cons hα ht =>
  cases ht with | cons hX ht =>
  cases ht with | cons hM ht =>
  cases ht with | cons hv ht =>
  cases ht with | cons hY ht =>
  cases ht with | cons hp ht =>
  cases ht
  simp [canonicalEqRecMinor, instL, VLevel.inst, inst, instVar, liftN, inst_liftN_lo] at hX hY hp hv
  have hrefl := HasType.eqReflApp heq (show (VLevel.succ u).WF U from hu)
    (HasType.sort hu) hX
  have hm := IsDefEq.castMotive_app henv.ordered heq hu hX hX hrefl
  refine ⟨hu, hX, hY, ?_, ?_⟩
  · simpa [eqApp] using hp
  · exact hm.defeq hv

/-- Syntactic endpoint equality licenses K at every typing of the source cast.
The proof argument is unrestricted, so this covers the free-major obstruction. -/
theorem reflexive_cast_simAt (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) : env.SimAt U Γ (typeCast u X X proof value) value := by
  intro T ht
  obtain ⟨hu, hX, _, hp, hv⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
  exact IsDefEq.trans_l henv hΓ ht (IsDefEq.typeCast_refl henv heq hu hΓ hX hp hv)

end Lean4Lean.VEnv.Strengthening
