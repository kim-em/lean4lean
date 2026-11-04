import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredStages

/-! # Comparing native types before carrier promotion

Common-mode promotion needs only the left native recovery, since common actual
endpoint typings align its carrier by uniqueness. Inferred promotion instead
compares the two independently recovered types in inferred mode. Their actual
sort typings justify this recursive comparison during binder descent. Neither
rule assumes a computational join or semantic recovery completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- Compatible closure of the exact-recovery checker, common-mode carrier
checking from one native recovery, and inferred carrier checking after a
recursive comparison of the two native types. -/
inductive CarrierAlignedCompare (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → Bool → ProofShape → ProofShape → Prop where
  | base : CarrierRecoveredCompare Step Δ mode a b → CarrierAlignedCompare Step Δ mode a b
  | commonCarrier : ScopedTypeRecovery Step Δ a A → ComputedJointCarrierGuard Step Δ A a b →
      CarrierAlignedCompare Step Δ true a b
  | aligned : ScopedTypeRecovery Step Δ a A → ScopedTypeRecovery Step Δ b B →
      CarrierAlignedCompare Step Δ false A B → ComputedJointCarrierGuard Step Δ A a b →
      CarrierAlignedCompare Step Δ mode a b
  /-- Native types align a recursive common comparison, including its new eta
  bodies and carrier promotions, before inferred checking is requested. -/
  | recover : ScopedTypeRecovery Step Δ a A → ScopedTypeRecovery Step Δ b B →
      CarrierAlignedCompare Step Δ false A B → CarrierAlignedCompare Step Δ true a b →
      CarrierAlignedCompare Step Δ mode a b
  | app : CarrierAlignedCompare Step Δ false f g → CarrierAlignedCompare Step Δ true a b →
      CarrierAlignedCompare Step Δ mode (.app f a) (.app g b)
  | proj : CarrierAlignedCompare Step Δ false a b →
      CarrierAlignedCompare Step Δ mode (.proj s i a) (.proj s i b)
  | lam : CarrierAlignedCompare Step Δ false A D → CarrierAlignedCompare Step (A :: Δ) mode b c →
      CarrierAlignedCompare Step Δ mode (.lam A b) (.lam D c)
  | forallE : CarrierAlignedCompare Step Δ false A D → CarrierAlignedCompare Step (A :: Δ) false B C →
      CarrierAlignedCompare Step Δ mode (.forallE A B) (.forallE D C)
  | lamSorted : DomainSort Δ A u → DomainSort Δ D u → CarrierAlignedCompare Step Δ true A D →
      CarrierAlignedCompare Step (A :: Δ) mode b c →
      CarrierAlignedCompare Step Δ mode (.lam A b) (.lam D c)
  | forallSorted : DomainSort Δ A u → DomainSort Δ D u → CarrierAlignedCompare Step Δ true A D →
      DomainSort (A :: Δ) B v → DomainSort (A :: Δ) C v → CarrierAlignedCompare Step (A :: Δ) true B C →
      CarrierAlignedCompare Step Δ mode (.forallE A B) (.forallE D C)
  | structFields {family : Name} {info : VProjectionInfo} {ls : List VLevel}
      {ps fields : List ProofShape} {m : ProofShape}
      (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i (h : i < fields.length), fields[i] ≠ .proof →
        CarrierAlignedCompare Step Δ true fields[i] (.proj family i m)) :
      CarrierAlignedCompare Step Δ true (mkApps (.const info.ctorName ls) (ps ++ fields)) m
  | lamCommon : CarrierAlignedCompare Step (A :: Δ) true b c →
      CarrierAlignedCompare Step Δ true (.lam A b) (.lam D c)
  | etaBodyL : DomainSort Δ A u →
      CarrierAlignedCompare Step (A :: Δ) true b (.app (f.liftN 1) (etaArgument u)) →
      CarrierAlignedCompare Step Δ true (.lam A b) f
  | etaBodyR : DomainSort Δ A u →
      CarrierAlignedCompare Step (A :: Δ) true (.app (f.liftN 1) (etaArgument u)) b →
      CarrierAlignedCompare Step Δ true f (.lam A b)
  | etaLams : CarrierAlignedCompare Step Δ false A D →
      (EtaHead (.lam A b) (.lam D c) ∨ EtaHead (.lam D c) (.lam A b)) →
      CarrierAlignedCompare Step Δ mode (.lam A b) (.lam D c)
  | compute : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' →
      CarrierAlignedCompare Step Δ mode a' b' → CarrierAlignedCompare Step Δ mode a b
  | symm : CarrierAlignedCompare Step Δ mode a b → CarrierAlignedCompare Step Δ mode b a

/-- Either checking mode embeds into common mode without changing recursive
inferred premises. -/
theorem CarrierAlignedCompare.common (H : CarrierAlignedCompare Step Δ mode a b) :
    CarrierAlignedCompare Step Δ true a b := by
  induction H with
  | base H => exact .base H.common
  | commonCarrier RA H => exact .commonCarrier RA H
  | aligned RA RB HT H ih => exact .aligned RA RB HT H
  | recover RA RB HT HC ihT ihC => exact .recover RA RB HT HC
  | lamSorted S S' HA HB ihA ihB => exact .lamSorted S S' HA ihB
  | forallSorted S S' HA T T' HB => exact .forallSorted S S' HA T T' HB
  | structFields hi hx hp hf hadm H => exact .structFields hi hx hp hf hadm H
  | lamCommon H => exact .lamCommon H
  | etaBodyL S H => exact .etaBodyL S H
  | etaBodyR S H => exact .etaBodyR S H
  | etaLams HD HE => exact .etaLams HD HE
  | app HF HX => exact .app HF HX
  | proj H => exact .proj H
  | lam HA HB ihA ihB => exact .lam HA ihB
  | forallE HA HB => exact .forallE HA HB
  | compute RA RB H ih => exact .compute RA RB ih
  | symm H ih => exact .symm ih

end ProofShape

private def CarrierAlignedDescent (n : Nat) (Δ : List ProofShape)
    (mode : Bool) (sa sb : ProofShape) : Prop :=
  ∀ {Γ Γ' k a b A B}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → proofEraseCtx Γ' = Δ →
    env.HasType univs Γ a A → env.HasType univs Γ b B →
    (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b)

private theorem carrier_aligned_descent (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierAlignedCompare Step Δ mode sa sb) : CarrierAlignedDescent n Δ mode sa sb := by
  induction H with
  | base H =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    exact proofErase_carrier_recovered_compare_descend hstep hΓ hΓ' W hΔ ha hb
      (by simpa only [Ea, Eb] using H)
  | commonCarrier RA HC =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ha hΔ
      (by simpa only [hΔ, Ea] using RA)
    constructor
    · intro hAB
      have hb₀ := (hAB.symm.trans henv hΓ (ha.uniqU henv hΓ ha₀)).defeqDF henv hΓ hb
      exact proofErase_computed_joint_carrier_descend hstep hΓ hΓ' W ha₀ hb₀
        (by simpa only [hΔ, EA₀, Ea, Eb] using HC)
    · intro hm; cases hm
  | aligned RA RB HT HC ihT =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ha hΔ
      (by simpa only [hΔ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W hb hΔ
      (by simpa only [hΔ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    obtain ⟨_, hB₀⟩ := hb₀.isType henv hΓ
    have HAB := (ihT hΓ hΓ' W hΔ hA₀ hB₀ EA₀ EB₀).2 rfl
      (not_isProof_of_sort hΓ hA₀) (not_isProof_of_sort hΓ hB₀)
    have hbA := HAB.symm.defeqDF henv hΓ hb₀
    have HH := proofErase_computed_joint_carrier_descend hstep hΓ hΓ' W ha₀ hbA
      (by simpa only [hΔ, EA₀, Ea, Eb] using HC)
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | recover RA RB HT HC ihT ihC =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ha hΔ
      (by simpa only [hΔ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W hb hΔ
      (by simpa only [hΔ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    obtain ⟨_, hB₀⟩ := hb₀.isType henv hΓ
    have HAB := (ihT hΓ hΓ' W hΔ hA₀ hB₀ EA₀ EB₀).2 rfl
      (not_isProof_of_sort hΓ hA₀) (not_isProof_of_sort hΓ hB₀)
    have HH := (ihC hΓ hΓ' W hΔ ha₀ hb₀ Ea Eb).1 HAB
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | app Hf Hx ihf ihx =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, hbE, Ebf, Ebx⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv haE
    obtain ⟨f', x', rfl, hnb, Ef', Ex'⟩ := erase_app_inv hbE
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Ef'] at Ebf
    rw [← Ex'] at Ebx
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    have HF := (ihf hΓ hΓ' W hΔ hf hf' Eaf Ebf).2 rfl (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hf' hx' hnb)
    have HFF := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (HFF.hasType.2.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HX := (ihx hΓ hΓ' W hΔ hx hx' Eax Ebx).1 ⟨_, hDD⟩
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.appDF HFF (HX.of_l henv hΓ hx)⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | proj Hm ihm =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, haE, Eam⟩ := ProofShape.liftN_proj_inv Ea
    obtain ⟨_, hbE, Ebm⟩ := ProofShape.liftN_proj_inv Eb
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv haE
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv hbE
    rw [← Em] at Eam
    rw [← Em'] at Ebm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HM := (ihm hΓ hΓ' W hΔ hm.hasType.2 hm'.hasType.2 Eam Ebm).2 rfl (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    have HH : env.IsDefEqU univs Γ _ _ :=
      ⟨_, SimAt.proj henv.orderedStrong hΓ (fun _ ht => HM.of_l henv hΓ ht) _ ha⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | lam HD Hbody ihD ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, Eab⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, Ebb⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← Ebody] at Eab
    rw [← ED'] at EbD
    rw [← Ebody'] at Ebb
    obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
    rw [Ectx] at Ebb
    have hbody'' := hbody'.defeqDFC henv hctx
    have HI := ihbody hΓD hΓD' W.succ
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
      hbody hbody'' Eab Ebb
    have finish (HH : env.IsDefEqU univs (D :: Γ) body body') :
        env.IsDefEqU univs Γ (.lam D body) (.lam D' body') :=
      ⟨_, IsDefEq.lamDF HDD (HH.of_l henv hΓD hbody)⟩
    constructor
    · intro hAB
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨_, _, hCC⟩ := HPi.forallE_inv henv hΓ
      exact finish (HI.1 ⟨_, hCC⟩)
    · intro hmode hn hn'
      exact finish (HI.2 hmode (fun hp => hn (hp.lam hΓ hD))
        (fun hp => hn' ((isProof_defeqCtx hctx).2 hp |>.lam hΓ hD')))
  | forallE HD HC ihD ihC =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, EaC⟩ := ProofShape.liftN_forallE_inv Ea
    obtain ⟨_, _, hbE, EbD, EbC⟩ := ProofShape.liftN_forallE_inv Eb
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv haE
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv hbE
    rw [← ED] at EaD
    rw [← EC] at EaC
    rw [← ED'] at EbD
    rw [← EC'] at EbC
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have HCU := (ihC hΓD hΓD' W.succ
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
      hC (hC'.defeqDFC henv hctx) EaC EbC).2 rfl
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD (hC'.defeqDFC henv hctx))
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | lamSorted SA SA' HD Hbody ihD ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, Eab⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, Ebb⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← Ebody] at Eab
    rw [← ED'] at EbD
    rw [← Ebody'] at Ebb
    obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
    have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, EaD] using SA) hΓ hΓ' W hD
    have hD' := ProofShape.DomainSort.descend (by simpa only [hΔ, EbD] using SA') hΓ hΓ' W hD'
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
    rw [Ectx] at Ebb
    have hbody'' := hbody'.defeqDFC henv hctx
    have HI := ihbody hΓD hΓD' W.succ
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
      hbody hbody'' Eab Ebb
    have finish (HH : env.IsDefEqU univs (D :: Γ) body body') :
        env.IsDefEqU univs Γ (.lam D body) (.lam D' body') :=
      ⟨_, IsDefEq.lamDF HDD (HH.of_l henv hΓD hbody)⟩
    constructor
    · intro hAB
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨_, _, hCC⟩ := HPi.forallE_inv henv hΓ
      exact finish (HI.1 ⟨_, hCC⟩)
    · intro hmode hn hn'
      exact finish (HI.2 hmode (fun hp => hn (hp.lam hΓ hD))
        (fun hp => hn' ((isProof_defeqCtx hctx).2 hp |>.lam hΓ hD')))
  | forallSorted SA SA' HD SB SB' HC ihD ihC =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, EaC⟩ := ProofShape.liftN_forallE_inv Ea
    obtain ⟨_, _, hbE, EbD, EbC⟩ := ProofShape.liftN_forallE_inv Eb
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv haE
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv hbE
    rw [← ED] at EaD
    rw [← EC] at EaC
    rw [← ED'] at EbD
    rw [← EC'] at EbC
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, EaD] using SA) hΓ hΓ' W hD
    have hD' := ProofShape.DomainSort.descend (by simpa only [hΔ, EbD] using SA') hΓ hΓ' W hD'
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have hctxE := congr (congrArg List.cons ((proofErase_liftN hΓ hΓ' W hD).trans EaD)) hΔ
    change proofEraseCtx (D.liftN n k :: Γ') = _ at hctxE
    have hC := ProofShape.DomainSort.descend
      (by simpa only [hctxE, EaC] using SB) hΓD hΓD' W.succ hC
    have hC' := ProofShape.DomainSort.descend
      (by simpa only [hctxE, EbC] using SB') hΓD hΓD' W.succ (hC'.defeqDFC henv hctx)
    have HCU := (ihC hΓD hΓD' W.succ hctxE
      hC hC' EaC EbC).1 ⟨_, HasType.sort (hC.sort_r henv hΓD)⟩
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
      apply Exists.intro _
      apply proofErase_structure_fields_reflect hΓ ha (hb.defeqU_r henv hΓ hAB.symm)
        hi hx hp hf hadm Ea
      intro i hj x X hxt hpt Ex
      by_cases hpx : IsProof Γ x
      · exact proofErase_structure_field hΓ hb hxt hpt (.inl (proofErase_eq_proof.2 hpx))
      have hnp : ¬ IsProof Γ (.proj family i b) := by
        rintro ⟨P, hpP, hP⟩
        exact hpx ⟨P, hxt.defeqU_r henv hΓ (hpt.uniqU henv hΓ hpP), hP⟩
      have hnraw : fields[i] ≠ ProofShape.proof := by
        intro H
        apply hpx
        apply proofErase_eq_proof.1
        exact ProofShape.liftN_inj.1 (Ex.trans H)
      have Eproj : (proofErase Γ (.proj family i b)).liftN n k = .proj family i major := by
        rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp]
        simp only [ProofShape.liftN, Eb]
      exact (ihfields i hj hnraw hΓ hΓ' W hΔ hxt hpt Ex Eproj).1
        ⟨_, hxt.isType henv hΓ |>.choose_spec⟩
    · intro hm; cases hm
  | lamCommon Hbody ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
      obtain ⟨_, _, haE, EaD, Eab⟩ := ProofShape.liftN_lam_inv Ea
      obtain ⟨_, _, hbE, EbD, Ebb⟩ := ProofShape.liftN_lam_inv Eb
      obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv haE
      obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv hbE
      rw [← ED] at EaD
      rw [← Ebody] at Eab
      rw [← ED'] at EbD
      rw [← Ebody'] at Ebb
      obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
      obtain ⟨⟨_, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨⟨_, HDD⟩, _, hCC⟩ := HPi.forallE_inv henv hΓ
      have HDU : env.IsDefEqU univs Γ D D' := ⟨_, HDD⟩
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
      have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
      have hctx := IsDefEqCtx.succ .zero HDD.symm
      have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
      rw [Ectx] at Ebb
      have hbody'' := hbody'.defeqDFC henv hctx
      have HI := ihbody hΓD hΓD' W.succ
        (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
        hbody hbody'' Eab Ebb
      exact ⟨_, IsDefEq.lamDF (HDU.of_l henv hΓ hD) ((HI.1 ⟨_, hCC⟩).of_l henv hΓD hbody)⟩
    · intro hmode; cases hmode
  | etaBodyL HR Hbody ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
      obtain ⟨_, _, Elam, ED, Ebody⟩ := ProofShape.liftN_lam_inv Ea
      obtain ⟨D, body, rfl, hn, ED', Ebody'⟩ := erase_lam_inv Elam
      rw [← ED'] at ED
      rw [← Ebody'] at Ebody
      obtain ⟨⟨_, hD₀⟩, C, hbody⟩ := ha.lam_inv henv hΓ
      have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, ED] using HR) hΓ hΓ' W hD₀
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
      have hfPi : env.HasType univs Γ b (.forallE D C) :=
        hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ (ha.uniqU henv hΓ (HasType.lam hD hbody)))
      have hnf : ¬ IsProof Γ b := by
        rintro ⟨P, hfP, hP⟩
        exact hn ⟨P, ha.defeqU_r henv hΓ (hAB.trans henv hΓ (hb.uniqU henv hΓ hfP)), hP⟩
      have hηbody : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) C := by
        have H := HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
        simpa only [VExpr.lift, VExpr.liftN, inst_liftN_bvar] using H
      have Eη := proofErase_eta_body_liftN (n := n) (k := k) hΓ hD hfPi hnf
      rw [Eb] at Eη
      have HI := (ihbody hΓD hΓD' W.succ
        (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, ED])
        hbody hηbody Ebody Eη).1 ⟨_, hηbody.isType henv hΓD |>.choose_spec⟩
      have HH : env.IsDefEqU univs Γ (.lam D body) b :=
        ⟨_, (IsDefEq.lamDF hD (HI.of_l henv hΓD hbody)).trans (IsDefEq.eta hfPi)⟩
      exact HH
    · intro hmode; cases hmode
  | etaBodyR HR Hbody ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
      obtain ⟨_, _, Elam, ED, Ebody⟩ := ProofShape.liftN_lam_inv Eb
      obtain ⟨D, body, rfl, hn, ED', Ebody'⟩ := erase_lam_inv Elam
      rw [← ED'] at ED
      rw [← Ebody'] at Ebody
      obtain ⟨⟨_, hD₀⟩, C, hbody⟩ := hb.lam_inv henv hΓ
      have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, ED] using HR) hΓ hΓ' W hD₀
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
      have hfPi : env.HasType univs Γ a (.forallE D C) :=
        ha.defeqU_r henv hΓ (hAB.trans henv hΓ (hb.uniqU henv hΓ (HasType.lam hD hbody)))
      have hnf : ¬ IsProof Γ a := by
        rintro ⟨P, hfP, hP⟩
        exact hn ⟨P, hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ (ha.uniqU henv hΓ hfP)), hP⟩
      have hηbody : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) C := by
        have H := HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
        simpa only [VExpr.lift, VExpr.liftN, inst_liftN_bvar] using H
      have Eη := proofErase_eta_body_liftN (n := n) (k := k) hΓ hD hfPi hnf
      rw [Ea] at Eη
      have HI := (ihbody hΓD hΓD' W.succ
        (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, ED])
        hηbody hbody Eη Ebody).1 ⟨_, hηbody.isType henv hΓD |>.choose_spec⟩
      have HH : env.IsDefEqU univs Γ (.lam D body) a :=
        ⟨_, (IsDefEq.lamDF hD (HI.symm.of_l henv hΓD hbody)).trans (IsDefEq.eta hfPi)⟩
      exact HH.symm
    · intro hmode; cases hmode
  | etaLams HD Hη ihD =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    rw [← Ea, ← Eb] at Hη
    obtain ⟨_, _, haE, EaD, _⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, _⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', _⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← ED'] at EbD
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.lam_inv henv hΓ
    have HDD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HH : env.IsDefEqU univs Γ (.lam D body) (.lam D' body') := by
      rcases Hη with Hη | Hη
      · exact proofErase_eta_head_infer hΓ ha (HasType.lam hD' hbody') HDD Hη.of_liftN
      · exact (proofErase_eta_head_infer hΓ hb (HasType.lam hD hbody) HDD.symm Hη.of_liftN).symm
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | compute Ra Rb HC ih =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ha hΔ Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W hb hΔ Rb
    have HI := ih hΓ hΓ' W hΔ HA.hasType.2 HB.hasType.2 EA EB
    have finish (HH : env.IsDefEqU univs Γ a' b') : env.IsDefEqU univs Γ a b :=
      ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HH).trans henv hΓ ⟨_, HB.symm⟩
    exact ⟨fun hAB => finish (HI.1 hAB),
      fun hmode hn hn' => finish (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn)
        (mt (isProof_congr hΓ HB).2 hn'))⟩

  | symm HC ih =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    have HI := ih hΓ hΓ' W hΔ hb ha Eb Ea
    exact ⟨fun hAB => (HI.1 hAB.symm).symm, fun hm hn hn' => (HI.2 hm hn' hn).symm⟩



/-- The enlarged comparison descends through arbitrary inserted binder blocks.
The aligned case reconstructs both lower types and compares them using their
actual sort typings before descending the supplied carrier certificate. -/
theorem proofErase_carrier_aligned_compare_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hΔ : proofEraseCtx Γ' = Δ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : CarrierAlignedCompare Step Δ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) :=
  carrier_aligned_descent hstep H hΓ hΓ' W hΔ ha hb rfl rfl

end Lean4Lean.VEnv.Strengthening
