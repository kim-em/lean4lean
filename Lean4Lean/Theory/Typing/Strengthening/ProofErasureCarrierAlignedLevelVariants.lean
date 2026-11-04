import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedStructuralBodies
import Lean4Lean.Theory.Typing.Strengthening.StructureProofFieldUniverses

/-! # Universe variants of dependent projection recipes

Typed universe conversion preserves proof erasure up to structural variants,
including conversion of the context below each binder. Instantiating a field
template at the same parameters and preceding projections preserves this
relation, without transporting any primitive computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- Structural universe variants survive an arbitrary common raw substitution. -/
theorem StructuralVariant.subst (H : StructuralVariant a b) :
    StructuralVariant (a.subst σ) (b.subst σ) := by
  induction H generalizing σ with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

variable [Params]
/-- Structural universe variants are already ordinary computed comparisons in
either mode and in any context; no native recovery is needed. -/
theorem StructuralVariant.computed (H : StructuralVariant a b) :
    ComputedJointCompare Step Δ mode a b := by
  induction H generalizing Δ mode with
  | refl => exact .leaf .refl
  | sort h => exact .leaf (.sort h)
  | const h => exact .leaf (.const h)
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
end ProofShape

variable [Params]

/-- Well-typed expressions differing only by equivalent universes have
structurally variant erasures. Proof classification and the contexts under
lambda and Pi binders are justified by actual conversion. -/
theorem proofErase_carrier_aligned_level_variant
    (H : LEquiv univs a b) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) :
    StructuralVariant (proofErase Γ a) (proofErase Γ b) := by
  induction H generalizing Γ A with
  | refl => exact .refl
  | sort H hw =>
    have HP := isProof_congr hΓ (((LEquiv.sort H hw).defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha)
    simp only [proofErase]
    rw [← HP]
    split
    · exact .refl
    · exact .sort H
  | const H hw =>
    have HP := isProof_congr hΓ (((LEquiv.const H hw).defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha)
    simp only [proofErase]
    rw [← HP]
    split
    · exact .refl
    · exact .const H
  | app HF HX ihf ihx =>
    have HP := isProof_congr hΓ (((LEquiv.app HF HX).defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha)
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    simp only [proofErase]
    rw [← HP]
    split
    · exact .refl
    · exact .app (ihf hΓ hf) (ihx hΓ hx)
  | proj HM ih =>
    have HP := isProof_congr hΓ (((LEquiv.proj HM).defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    simp only [proofErase]
    rw [← HP]
    split
    · exact .refl
    · exact .proj (ih hΓ hm.hasType.2)
  | @lam D D' b b' HD HB ihD ihB =>
    have HP := isProof_congr hΓ (((LEquiv.lam HD HB).defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha)
    obtain ⟨⟨u, hD⟩, _, hb⟩ := ha.lam_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HDD := (HD.defeq henv hΓ ⟨_, hD⟩).of_l henv hΓ hD
    have hbody' := ((HB.defeq henv hΓD ⟨_, hb⟩).of_l henv hΓD hb).hasType.2
    have EB := proofErase_defeqCtx hΓD (.succ .zero HDD) hbody'
    have VB := ihB hΓD hb
    rw [EB] at VB
    simp only [proofErase]
    rw [← HP]
    split
    · exact .refl
    · exact .lam (ihD hΓ hD) VB
  | @forallE D D' b b' HD HB ihD ihB =>
    have HP := isProof_congr hΓ (((LEquiv.forallE HD HB).defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha)
    obtain ⟨⟨u, hD⟩, _, hb⟩ := ha.forallE_inv henv
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HDD := (HD.defeq henv hΓ ⟨_, hD⟩).of_l henv hΓ hD
    have hbody' := ((HB.defeq henv hΓD ⟨_, hb⟩).of_l henv hΓD hb).hasType.2
    have EB := proofErase_defeqCtx hΓD (.succ .zero HDD) hbody'
    have VB := ihB hΓD hb
    rw [EB] at VB
    simp only [proofErase]
    rw [← HP]
    split
    · exact .refl
    · exact .forallE (ihD hΓ hD) VB

/-- The same structural erasure comparison permits any ordinary conversion of
the target context, including a universe-varied dependent telescope prefix. -/
theorem proofErase_carrier_aligned_level_variant_context
    (H : LEquiv univs a b) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (W : IsDefEqCtx env univs [] Γ Γ') :
    StructuralVariant (proofErase Γ a) (proofErase Γ' b) := by
  have hb := ((H.defeq henv hΓ ⟨_, ha⟩).of_l henv hΓ ha).hasType.2
  rw [← proofErase_defeqCtx hΓ W hb]
  exact proofErase_carrier_aligned_level_variant H hΓ ha

omit [Params] in
private theorem level_forallArity (H : LEquiv U a b) : a.forallArity = b.forallArity := by
  induction H with
  | forallE _ _ _ ih => simpa only [VExpr.forallArity] using congrArg (· + 1) ih
  | refl | sort | const | app | proj | lam => rfl

omit [Params] in
private theorem level_telescope_domains
    (H : LEquiv U (wrapForalls ds r) (wrapForalls ds' r')) (hl : ds.length = ds'.length) :
    List.Forall₂ (LEquiv U) ds ds' := by
  induction ds generalizing ds' with
  | nil => cases ds' <;> simp_all
  | cons d ds ih =>
    cases ds' with
    | nil => simp at hl
    | cons d' ds' =>
      obtain ⟨A, B, HE, HD, HB⟩ := H.forallE_inv
      have EE : d = A ∧ wrapForalls ds r = B := VExpr.forallE.inj HE
      rcases EE with ⟨rfl, rfl⟩
      exact .cons HD (ih HB (by simpa using hl))

/-- Two telescope witnesses for equivalent instances of one constructor have
pointwise level-equivalent domains, even when those domains are dependent. -/
theorem carrier_aligned_projection_telescope_levels
    (HT : ProjTele env univs family info ls doms result)
    (HT' : ProjTele env univs family info ls' doms' result')
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls') :
    List.Forall₂ (LEquiv univs) doms doms' := by
  have H := LEquiv.instL_expr info.ctorType hw hw' he
  rw [HT.shape, HT'.shape] at H
  have hl := level_forallArity H
  obtain ⟨c, levels, args, ER⟩ := HT.head
  obtain ⟨c', levels', args', ER'⟩ := HT'.head
  simp only [forallArity_wrapForalls, ER, ER', forallArity_mkApps_const, Nat.add_zero] at hl
  exact level_telescope_domains H hl

/-- Universe transport follows the full erased field recipe, not just its
family metadata. The same raw parameters and preceding projections instantiate
the two level-equivalent templates, so arbitrary dependent fields are allowed. -/
theorem proofErase_carrier_aligned_projection_type_variant
    (HT : ProjTele env univs family info ls doms result)
    (HT' : ProjTele env univs family info ls' doms' result')
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls')
    (hj : info.nparams + j < doms.length) (hj' : info.nparams + j < doms'.length) :
    StructuralVariant (projectionType family info doms j hj args m)
      (projectionType family info doms' j hj' args m) := by
  have HD := carrier_aligned_projection_telescope_levels HT HT' hw hw' he
  have HP : List.Forall₂ (LEquiv univs)
      (doms.take (info.nparams + j)).reverse (doms'.take (info.nparams + j)).reverse := by
    exact List.Forall₂.reverse.2 (List.forall₂_take HD _)
  have hΓ := HT.ctx _ (Nat.le_of_lt hj)
  obtain ⟨u, ht⟩ := HT.doms _ hj
  have H := proofErase_carrier_aligned_level_variant_context
    (List.forall₂_getElem HD _ hj hj') hΓ ht (StructureReplay.level_context henv hΓ HP)
  exact H.subst

end Lean4Lean.VEnv.Strengthening
