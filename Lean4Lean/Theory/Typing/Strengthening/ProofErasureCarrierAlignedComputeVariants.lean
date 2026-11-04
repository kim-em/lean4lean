import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPrimitiveVariants

/-! # Finite concrete computation across universe variants

Replay supplies actual typed representatives at every composition point. Binder
bodies may live in different actual contexts; their erased computations remain
context independent. No normalization or intermediate typing oracle is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private variant_app_inv variant_proj_inv variant_lam_inv variant_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPrimitiveVariants
variable [Params]

/-- Finite compatible concrete computation simulates across typed structural
variants, including nested binders, recursive definitions and created redexes. -/
theorem proofErase_carrier_aligned_compute_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ProofShape.Compute (ErasedIotaPrimitive D) a out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ e T) (ht' : env.HasType univs Γ' e' T')
    (Ee : proofErase Γ e = a) (V : StructuralVariant a (proofErase Γ' e')) :
    ∃ out', ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ' e') out' ∧
      StructuralVariant out out' := by
  induction R generalizing Γ Γ' e e' T T' with
  | base R =>
    obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_iota_variant hs hlevels hcon R hΓ hΓ' ht ht' Ee V
    exact ⟨out', .base R', V'⟩
  | beta R =>
    obtain ⟨out', R', V'⟩ := R.variant V
    exact ⟨out', .beta R', V'⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨mid', R₁', V₁⟩ := ih₁ hΓ hΓ' ht ht' Ee V
    obtain ⟨e₁, Re₁, E₁⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht (Ee ▸ R₁)
    obtain ⟨e₁', Re₁', E₁'⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ' ht' R₁'
    obtain ⟨out', R₂', V₂⟩ := ih₂ hΓ hΓ' (Re₁.simAt hs hΓ _ ht).hasType.2
      (Re₁'.simAt hs hΓ' _ ht').hasType.2 E₁ (by simpa only [E₁'] using V₁)
    exact ⟨out', .trans R₁' (by simpa only [E₁'] using R₂'), V₂⟩
  | app Rf Rx ihf ihx =>
    obtain ⟨g, y, EV, Vf, Vx⟩ := variant_app_inv V
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨g', y', rfl, _, Eg, Ey⟩ := erase_app_inv EV
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := ht'.app_inv henv hΓ'
    obtain ⟨g₁, Rg, Vg⟩ := ihf hΓ hΓ' hf hg Ef (by simpa only [Eg] using Vf)
    obtain ⟨y₁, Ry, Vy⟩ := ihx hΓ hΓ' hx hy Ex (by simpa only [Ey] using Vx)
    exact ⟨_, by simpa only [EV, Eg, Ey] using ProofShape.Compute.app Rg Ry, .app Vg Vy⟩
  | proj Rm ihm =>
    obtain ⟨m', EV, Vm⟩ := variant_proj_inv V
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨n, rfl, _, En⟩ := erase_proj_inv EV
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _⟩ := ht'.proj_inv henv hΓ'
    obtain ⟨n₁, Rn, Vn⟩ := ihm hΓ hΓ' hm.hasType.2 hn.hasType.2 Em (by simpa only [En] using Vm)
    exact ⟨_, by simpa only [EV, En] using ProofShape.Compute.proj Rn, .proj Vn⟩
  | lam RA Rb ihA ihb =>
    obtain ⟨D, c, EV, VA, Vb⟩ := variant_lam_inv V
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨D', c', rfl, _, ED, Ec⟩ := erase_lam_inv EV
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨⟨v, hD⟩, _, hc⟩ := ht'.lam_inv henv hΓ'
    obtain ⟨D₁, RD, VD⟩ := ihA hΓ hΓ' hA hD EA (by simpa only [ED] using VA)
    obtain ⟨c₁, Rc, Vc⟩ := ihb (Γ := A :: Γ) (Γ' := D' :: Γ') ⟨hΓ, u, hA⟩ ⟨hΓ', v, hD⟩ hb hc Eb (by simpa only [Ec] using Vb)
    exact ⟨_, by simpa only [EV, ED, Ec] using ProofShape.Compute.lam RD Rc, .lam VD Vc⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨D, C, EV, VA, VB⟩ := variant_forallE_inv V
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨D', C', rfl, _, ED, EC⟩ := erase_forallE_inv EV
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨⟨v, hD⟩, _, hC⟩ := ht'.forallE_inv henv
    obtain ⟨D₁, RD, VD⟩ := ihA hΓ hΓ' hA hD EA (by simpa only [ED] using VA)
    obtain ⟨C₁, RC, VC⟩ := ihB (Γ := A :: Γ) (Γ' := D' :: Γ') ⟨hΓ, u, hA⟩ ⟨hΓ', v, hD⟩ hB hC EB (by simpa only [EC] using VB)
    exact ⟨_, by simpa only [EV, ED, EC] using ProofShape.Compute.forallE RD RC, .forallE VD VC⟩

end Lean4Lean.VEnv.Strengthening
