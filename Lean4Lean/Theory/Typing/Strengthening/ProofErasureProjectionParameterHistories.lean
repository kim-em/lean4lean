import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedProjectionRecipe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeStructurePivot

/-! # Dependent projections after changes to recovered parameters

Parameter computations and major computations act simultaneously on the whole
field recipe. A common native family output therefore supplies a new projection
guard, even when its selected parameters differ. Parameter-history joins and the
fork at the original recipe remain explicit; exact original-family recovery at
the pivot is no longer required. Indexed registered families are included.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
/-- Both parts of a projection's raw capture vector compute independently.
Earlier fields all follow the same major path; supplied parameters may change. -/
theorem ProofShape.projectionArgs_compute_parameters_major
    (HP : List.Forall₂ (ScopedCompute Step Δ) ps qs) (HM : ScopedCompute Step Δ m m') :
    List.Forall₂ (ScopedCompute Step Δ) (projectionArgs s ps m j) (projectionArgs s qs m' j) := by
  unfold projectionArgs
  apply List.Forall₂.append HP
  apply List.forall₂_map_left_iff.2
  apply List.forall₂_map_right_iff.2
  exact List.Forall₂.rfl (fun _ _ => ScopedCompute.proj HM)

/-- A closed typed field template permits simultaneous computation of its
parameters and major. Raw proof projections need agree with actual erasure only
at retained template variables. No output typing or native images are assumed. -/
theorem proofErase_projection_template_compute_parameters_major {doms : List VExpr}
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs doms.reverse e T)
    (W : Ctx.SubstEq env univs Γ (VExpr.Subst.ofList (ps ++ projsOf s m j))
      (VExpr.Subst.ofList (ps ++ projsOf s m j)) doms.reverse)
    (ha : (ps ++ projsOf s m j).length = doms.length)
    (HP : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (ps.map (proofErase Γ)) qs)
    (HM : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ m) out) :
    ScopedCompute Step (proofEraseCtx Γ)
      ((proofErase doms.reverse e).instOuter (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j))
      ((proofErase doms.reverse e).instOuter (projectionArgs s qs out j)) := by
  have ES : ErasedSubstAgreement doms.reverse Γ (VExpr.Subst.ofList (ps ++ projsOf s m j))
      (ProofShape.Subst.ofList (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j)) := by
    intro i A hl hn
    exact erased_projection_subst_agreement hΓ W ha hl hn
  have HC := projectionArgs_compute_parameters_major (s := s) (j := j) HP HM
  apply proofErase_compute_subst_images_of_renaming hrename hΓ W he ES
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := HC.length_eq
  by_cases hi : i < (projectionArgs s (ps.map (proofErase Γ)) (proofErase Γ m) j).length
  · simp only [← hlen, dif_pos hi]
    exact HC.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

/-- Actual retained projection typing supplies all source capture typing.
Only the parameter prefix is computed: indices do not occur in the recipe.
The common parameter vector and major can be arbitrary raw outputs. -/
theorem typed_projectionType_compute_parameters_major
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (HT : ProjTele env univs s info ls doms result) (hj : info.nparams + j < doms.length)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args))
    (HP : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((args.map (proofErase Γ)).take info.nparams) psOut)
    (HM : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m))
      (projectionType s info doms j hj psOut out) := by
  obtain ⟨hw, hl, hargs, hnz⟩ := retained_projection_family_facts hΓ hi ht hn hm
  have hp : (args.take info.nparams).length = info.nparams := by simp; omega
  have hidx : (args.drop info.nparams).length = info.nindices := by simp; omega
  have hm' : env.HasType univs Γ m (VExpr.mkApps (.const s ls)
      (args.take info.nparams ++ args.drop info.nparams)) := by simpa only [List.take_append_drop] using hm
  obtain ⟨tail, hps⟩ := projection_parameters_typed henv hΓ hi hp hm'
  have W := projection_prefix_subst hΓ hi hw hl hnz HT hps hp hidx hm' (Nat.le_of_lt hj)
  rw [projection_argSubst_eq_ofList] at W
  obtain ⟨_, hF⟩ := HT.doms _ hj
  have HC := proofErase_projection_template_compute_parameters_major
    (fun {Δ Δ' a b τ} ⟨stage, H⟩ WR =>
      ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage H WR⟩)
    hΓ hF W (by simp only [List.length_append, projsOf, List.length_map, List.length_range,
      hp, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)])
    (by simpa only [List.map_take] using HP) HM
  have hlen : psOut.length = info.nparams := by
    have := HP.length_eq
    simp only [List.length_take, List.length_map] at this
    omega
  simpa only [projectionType, List.map_take, ← hlen, List.take_length] using HC

/-- Common native family output replaces exact family recovery at a projection
pivot. Readout derives its selected universes and parameter histories; only the
parameter prefix needs joins, even for indexed families. The native guard is
replayed to derive typing at the new selected family. The original recipe's
conversion fork and parameter-history joining remain open premises, not hidden
uses of type-fork joining or native completeness. -/
theorem projection_native_tail_common_of_family_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (HT : ProjTele env univs s info ls doms result) (hj : info.nparams + j < doms.length)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (ht' : env.HasType univs Γ (.proj s j m') U') (hn' : ¬ IsProof Γ (.proj s j m'))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args))
    (hm' : env.HasType univs Γ m' T')
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m') commonType)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) commonType)
    (HJ : ∀ p ∈ (args.map (proofErase Γ)).take info.nparams, ∀ q,
      ScopedValueChain D (proofEraseCtx Γ) p q →
      ∃ r, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p r ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) q r)
    (RM : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ m) common)
    (RM' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ m') common)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) selected)
    (joinRecipe : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared) :
    ∃ shared, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.proj s j m')) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) selected shared := by
  obtain ⟨u, hS⟩ := hm.isType henv hΓ
  obtain ⟨ls', qs, hw, _, _, HE, hq, RB, HC⟩ :=
    static_structure_registered_family_value_readout heq hs hi hD hΓ hS RT
  have RNL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m') (ProofShape.mkApps (.const s ls) qs) :=
    (RN.convert (.beta RB)).convert (ScopedCompute.mkApps
      (.base ⟨0, .inl (.inr (.const (HE.flip.imp (fun _ _ H => H.symm)) hw))⟩)
      (List.Forall₂.rfl (fun _ _ => .refl)))
  obtain ⟨A, hmA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hm' RNL
  obtain ⟨args', rfl, rfl⟩ := proofErase_const_spine_inv EA
  have HCP : List.Forall₂ (ScopedValueChain D (proofEraseCtx Γ))
      ((args.map (proofErase Γ)).take info.nparams) ((args'.map (proofErase Γ)).take info.nparams) := by
    apply List.forall₂_of_getElem (by simp only [List.length_take, HC.length_eq])
    intro i hi hi'
    simp only [List.getElem_take]
    exact HC.getElem_of i (by simp only [List.length_take] at hi; omega)
      (by simp only [List.length_take] at hi'; omega)
  obtain ⟨ps, HP, HQ⟩ := scoped_value_chain_vector_join HCP HJ
  have RL := typed_projectionType_compute_parameters_major heq hs hΓ hi HT hj ht hn hm HP RM
  have RR := typed_projectionType_compute_parameters_major heq hs hΓ hi HT hj ht' hn' hmA HQ RM'
  obtain ⟨shared, RS, RJ⟩ := joinRecipe RC RL
  have RP := ScopedTypeRecovery.proj hi HT hj hq RNL
  refine ⟨shared, ?_, RS⟩
  rw [show proofErase Γ (.proj s j m') = .proj s j (proofErase Γ m') from if_neg hn']
  exact RP.convert (RR.trans RJ)

end Lean4Lean.VEnv.Strengthening
