import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelVariants

/-! # Structural variants with dependent family parameters

Nested projection types may change universe syntax in their family parameters
as well as at their head. Paired raw substitution preserves structural variants,
so recursive record checking can follow both changes in the field recipe.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

namespace ProofShape
/-- Universe variants survive insertion of variables at any depth. -/
theorem StructuralVariant.liftN (H : StructuralVariant a b) :
    StructuralVariant (a.liftN n k) (b.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | sort H => exact .sort H
  | const H => exact .const H
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

private theorem variant_lift_images {σ τ : Subst} (H : ∀ i, StructuralVariant (σ i) (τ i)) :
    ∀ i, StructuralVariant (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN

private theorem variant_subst_same (a : ProofShape) (H : ∀ i, StructuralVariant (σ i) (τ i)) :
    StructuralVariant (a.subst σ) (a.subst τ) := by
  induction a generalizing σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (variant_lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA H) (ihB (variant_lift_images H))

/-- Independently varied substitution images preserve structural variants of
the templates, including under every dependent binder. -/
theorem StructuralVariant.subst_pair (V : StructuralVariant a b)
    (H : ∀ i, StructuralVariant (σ i) (τ i)) :
    StructuralVariant (a.subst σ) (b.subst τ) := by
  induction V generalizing σ τ with
  | refl => exact variant_subst_same _ H
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (variant_lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA H) (ihB (variant_lift_images H))

/-- Telescope instantiation permits pointwise universe variants of captures. -/
theorem StructuralVariant.instOuter_pair (V : StructuralVariant a b)
    (H : List.Forall₂ StructuralVariant args args') :
    StructuralVariant (a.instOuter args) (b.instOuter args') := by
  apply V.subst_pair
  intro i
  have hl := H.length_eq
  simp only [Subst.ofList, ← hl]
  split
  · exact List.forall₂_getElem H _ (by omega) (by omega)
  · exact .refl

/-- Beta substitution permits structurally varied bodies and arguments. -/
theorem StructuralVariant.inst_pair (V : StructuralVariant a b) (H : StructuralVariant x y) :
    StructuralVariant (a.inst x) (b.inst y) := by
  rw [inst_eq_subst, inst_eq_subst]
  apply V.subst_pair
  intro i
  cases i with
  | zero => exact H
  | succ i => exact .refl

/-- Every finite beta path has a matching path from a structural universe
variant. The reducts remain structurally variant, including reductions inside
annotations and redexes created by earlier contractions. -/
theorem BetaRed.variant (R : ProofShape.BetaRed a a') (V : StructuralVariant a b) :
    ∃ b', ProofShape.BetaRed b b' ∧ StructuralVariant a' b' := by
  induction R generalizing b with
  | refl => exact ⟨_, .refl, V⟩
  | trans RA RB ihA ihB =>
    obtain ⟨b₁, R₁, V₁⟩ := ihA V
    obtain ⟨b₂, R₂, V₂⟩ := ihB V₁
    exact ⟨b₂, R₁.trans R₂, V₂⟩
  | app RF RX ihf ihx =>
    cases V with
    | refl => exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      obtain ⟨g, RG, VG⟩ := ihf VF
      obtain ⟨y, RY, VY⟩ := ihx VX
      exact ⟨_, .app RG RY, .app VG VY⟩
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
  | lam RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      obtain ⟨D, RD, VD⟩ := ihA VA
      obtain ⟨c, RC, VC⟩ := ihB VB
      exact ⟨_, .lam RD RC, .lam VD VC⟩
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨D, RD, VD⟩ := ihA VA
      obtain ⟨C, RC, VC⟩ := ihB VB
      exact ⟨_, .forallE RD RC, .forallE VD VC⟩
  | beta =>
    cases V with
    | refl => exact ⟨_, .beta, .refl⟩
    | app VF VX =>
      cases VF with
      | refl => exact ⟨_, .beta, StructuralVariant.refl.inst_pair VX⟩
      | lam VA VB => exact ⟨_, .beta, VB.inst_pair VX⟩

private theorem variant_app_inv (H : StructuralVariant (.app f x) b) :
    ∃ g y, b = .app g y ∧ StructuralVariant f g ∧ StructuralVariant x y := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app HF HX => exact ⟨_, _, rfl, HF, HX⟩

/-- A structural variant of a family spine retains its family, pointwise
universe equivalence, and a structural variant of every parameter. -/
theorem StructuralVariant.constant_spine
    (H : StructuralVariant (mkApps (.const c ls) args) b) :
    ∃ ls' args', b = mkApps (.const c ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ StructuralVariant args args' := by
  induction args using List.snoc_induction generalizing b with
  | nil =>
    cases H with
    | refl => exact ⟨_, [], rfl, .rfl (fun _ _ => by rfl), .nil⟩
    | const HL => exact ⟨_, [], rfl, HL, .nil⟩
  | snoc args x ih =>
    rw [mkApps_snoc] at H
    obtain ⟨g, y, rfl, HF, HX⟩ := variant_app_inv H
    obtain ⟨ls', args', rfl, HL, Hargs⟩ := ih HF
    exact ⟨ls', args' ++ [y], mkApps_snoc.symm, HL, Hargs.append' (.cons HX .nil)⟩
end ProofShape

variable [Params]

/-- The full projection recipe varies structurally when both constructor
universes and recovered family parameters do. Earlier projections of the same
major supply identical captures; dependent references to varied parameters are
handled by paired substitution. -/
theorem proofErase_carrier_aligned_projection_type_parameter_variant
    (HT : ProjTele env univs family info ls doms result)
    (HT' : ProjTele env univs family info ls' doms' result')
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls')
    (hj : info.nparams + j < doms.length) (hj' : info.nparams + j < doms'.length)
    (Hargs : List.Forall₂ StructuralVariant args args') :
    StructuralVariant (projectionType family info doms j hj args m)
      (projectionType family info doms' j hj' args' m) := by
  have HD := carrier_aligned_projection_telescope_levels HT HT' hw hw' he
  have HP : List.Forall₂ (LEquiv univs)
      (doms.take (info.nparams + j)).reverse (doms'.take (info.nparams + j)).reverse :=
    List.Forall₂.reverse.2 (List.forall₂_take HD _)
  have hΓ := HT.ctx _ (Nat.le_of_lt hj)
  obtain ⟨u, ht⟩ := HT.doms _ hj
  have H := proofErase_carrier_aligned_level_variant_context
    (List.forall₂_getElem HD _ hj hj') hΓ ht (StructureReplay.level_context henv hΓ HP)
  apply H.instOuter_pair
  exact (List.forall₂_take Hargs _).append' (.rfl (fun _ _ => .refl))

end Lean4Lean.VEnv.Strengthening
