import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCoverage

/-! # Recursive structure fields in contextual prefix guards

Field certificates compare against actual projections at aligned original types.
Proof fields need no visible projection. Function eta inside a record field is
included without a transitive comparison rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Aligned original field comparisons produce a recursive structure guard.
The actual expansion typing supplies the closed projection-admissibility guard. -/
theorem proofErase_scoped_structure_fields (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hps : ps.length = info.nparams)
    (hx : info.nindices = 0) (hf : fields.length = info.numFields)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (he : env.HasType univs Γ (mkApps (.const info.ctorName ls) (ps ++ fields))
      (mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (mkApps (.const family ls) ps))
    (H : ∀ i (h : i < fields.length), ∃ A, env.HasType univs Γ fields[i] A ∧
      env.HasType univs Γ (.proj family i m) A ∧
      ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
        (proofErase Γ fields[i]) (proofErase Γ (.proj family i m))) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (mkApps (.const info.ctorName ls) (ps ++ fields))) (proofErase Γ m) := by
  by_cases hpm : IsProof Γ m
  · rw [proofErase_eq_proof.2 hpm,
      proofErase_eq_proof.2 (isProof_of_common_type hΓ hm he hpm)]
    exact .refl
  have hne := fun H => hpm (isProof_of_common_type hΓ he hm H)
  rw [proofErase_const_spine hΓ he hne, List.map_append]
  apply ProofShape.ScopedCompare.structFields hi hx (by simp [hps]) (by simp [hf])
    ((StructureReplay.expansion_typed_iff henv hΓ hi hps hx hm).1 hexp)
  intro i hj hn
  have hj' : i < fields.length := by simpa only [List.length_map] using hj
  obtain ⟨A, ha, hp, HC⟩ := H i hj'
  have hna : ¬ IsProof Γ fields[i] := by
    intro H
    exact hn (by simpa only [List.getElem_map] using proofErase_eq_proof.2 H)
  have hnp := fun H => hna (isProof_of_common_type hΓ hp ha H)
  rw [show proofErase Γ (.proj family i m) = .proj family i (proofErase Γ m) from if_neg hnp] at HC
  simpa only [List.getElem_map] using HC

/-- A one-field structure whose field is a function admits recursive function
eta inside structure eta. The changed constructor's typing is reconstructed
from the typed projected expansion, rather than supplied as an extra premise. -/
theorem proofErase_scoped_structure_function_eta (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hps : ps.length = info.nparams)
    (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hm : env.HasType univs Γ m (mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps m)
      (mkApps (.const family ls) ps))
    (hF : env.HasType univs Γ (.proj family 0 m) (.forallE A B)) :
    env.HasType univs Γ
      (mkApps (.const info.ctorName ls) (ps ++ [.lam A (.app (VExpr.proj family 0 m).lift (.bvar 0))]))
      (mkApps (.const family ls) ps) ∧
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (mkApps (.const info.ctorName ls)
        (ps ++ [.lam A (.app (VExpr.proj family 0 m).lift (.bvar 0))]))) (proofErase Γ m) := by
  have Eexp : structExpand family info ls ps m =
      .app (mkApps (.const info.ctorName ls) ps) (.proj family 0 m) := by
    simp [structExpand, hf, mkApps_snoc]
  have hxp := Eexp ▸ hexp
  obtain ⟨_, _, hhead, hfield⟩ := hxp.app_inv henv hΓ
  have Hη := IsDefEq.eta hF
  have Hη' := (show env.IsDefEqU univs Γ _ _ from ⟨_, Hη⟩).of_r henv hΓ hfield
  have HC := (show env.IsDefEqU univs Γ _ _ from ⟨_, IsDefEq.appDF hhead Hη'⟩).of_r henv hΓ hxp
  have he : env.HasType univs Γ
      (mkApps (.const info.ctorName ls) (ps ++ [.lam A (.app (VExpr.proj family 0 m).lift (.bvar 0))]))
      (mkApps (.const family ls) ps) := by
    simpa only [mkApps_snoc] using HC.hasType.1
  refine ⟨he, proofErase_scoped_structure_fields hΓ hi hps hx (by simp [hf]) hm he hexp ?_⟩
  intro i hj
  have : i = 0 := by simp only [List.length_singleton] at hj; omega
  subst i
  refine ⟨_, Hη.hasType.1, hF, ?_⟩
  obtain ⟨⟨_, hA⟩, _⟩ := (hF.isType henv hΓ).forallE_inv henv
  have hb : env.HasType univs (A :: Γ) (.app (VExpr.proj family 0 m).lift (.bvar 0)) B := by
    simpa only [lift, liftN, inst_liftN_bvar] using
      HasType.app (hF.weak henv.ordered (B := A)) (HasType.bvar .zero)
  exact proofErase_scoped_etaL hΓ hA hb hF .refl

end Lean4Lean.VEnv.Strengthening
