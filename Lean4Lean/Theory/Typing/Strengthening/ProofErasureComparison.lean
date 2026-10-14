import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureEta

/-! # Recursive erased comparison with explicit type modes

Common-type mode admits function eta and guarded structure eta. Inferred mode reconstructs equality between
non-proof endpoints without a supplied type conversion, including eta between
lambda-shaped endpoints whose displayed domains compare recursively. Function
positions and domains use inferred mode; arguments use common-type mode after alignment.
The structure guard retains the registry and closed projection admissibility.
Both modes admit computations at every node. No completeness claim is made.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay

variable [Params]

namespace ProofShape
/-- `true` requests common endpoint types. `false` permits type inference at a
non-proof endpoint and excludes an unsupported eta comparison at that position. -/
inductive Compare (Step : ProofShape → ProofShape → Prop) : Bool → ProofShape → ProofShape → Prop where
  | refl : Compare Step mode e e
  | sort : u ≈ v → Compare Step mode (.sort u) (.sort v)
  | const : List.Forall₂ (· ≈ ·) ls ls' → Compare Step mode (.const c ls) (.const c ls')
  | app : Compare Step false f f' → Compare Step true a a' →
      Compare Step mode (.app f a) (.app f' a')
  | proj : Compare Step false m m' → Compare Step mode (.proj s i m) (.proj s i m')
  | lam : Compare Step false A A' → Compare Step mode b b' →
      Compare Step mode (.lam A b) (.lam A' b')
  | forallE : Compare Step false A A' → Compare Step false B B' →
      Compare Step mode (.forallE A B) (.forallE A' B')
  | etaL : EtaHead e f → Compare Step true e f
  | etaR : EtaHead f e → Compare Step true e f
  | structL : StructureEtaHead e f → Compare Step true e f
  | structR : StructureEtaHead f e → Compare Step true e f
  /-- Lambda-shaped short endpoints expose their Pi type below. Comparing the
  displayed domains suffices for eta even in inferred function positions. -/
  | etaLams : Compare Step false A D →
      (EtaHead (.lam A b) (.lam D f) ∨ EtaHead (.lam D f) (.lam A b)) →
      Compare Step mode (.lam A b) (.lam D f)
  | compute : Compute Step a a' → Compute Step b b' → Compare Step mode a' b' → Compare Step mode a b

/-- Comparison is symmetric without introducing untyped transitive witnesses. -/
theorem Compare.symm (H : Compare Step mode a b) : Compare Step mode b a := by
  induction H with
  | refl => exact .refl
  | sort h => exact .sort h.symm
  | const h =>
    apply Compare.const
    induction h with
    | nil => exact .nil
    | cons h _ ih => exact .cons h.symm ih
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL h => exact .etaR h
  | etaR h => exact .etaL h
  | structL h => exact .structR h
  | structR h => exact .structL h
  | etaLams _ h ih => exact .etaLams ih h.symm
  | compute Ra Rb _ ih => exact .compute Rb Ra ih

/-- An inferred comparison also works when endpoint types are supplied. -/
theorem Compare.common (H : Compare Step mode a b) : Compare Step true a b := by
  induction H with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA _ _ ihb => exact .lam HA ihb
  | forallE HA HB => exact .forallE HA HB
  | etaL h => exact .etaL h
  | etaR h => exact .etaR h
  | structL h => exact .structL h
  | structR h => exact .structR h
  | etaLams HD h => exact .etaLams HD h
  | compute Ra Rb _ ih => exact .compute Ra Rb ih

/-- The two modes both weaken when their underlying computations weaken. -/
theorem Compare.liftN
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (H : Compare Step mode a b) : Compare Step mode (a.liftN n k) (b.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL h => exact .etaL h.liftN
  | etaR h => exact .etaR h.liftN
  | structL h => exact .structL h.liftN
  | structR h => exact .structR h.liftN
  | etaLams _ h ih => exact .etaLams ih (h.elim (fun h => .inl h.liftN) (fun h => .inr h.liftN))
  | compute Ra Rb _ ih => exact .compute (Ra.liftN hstep) (Rb.liftN hstep) ih

/-- Raw substitution preserves modes and all displayed eta comparisons. -/
theorem Compare.subst
    (hstep : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : Compare Step mode a b) : Compare Step mode (a.subst σ) (b.subst σ) := by
  induction H generalizing σ with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL h => exact .etaL h.subst
  | etaR h => exact .etaR h.subst
  | structL h => exact .structL h.subst
  | structR h => exact .structR h.subst
  | etaLams _ h ih => exact .etaLams ih (h.elim (fun h => .inl h.subst) (fun h => .inr h.subst))
  | compute Ra Rb _ ih => exact .compute (Ra.subst hstep) (Rb.subst hstep) ih

private theorem liftN_sort_inv {e : ProofShape} (H : e.liftN n k = .sort u) : e = .sort u := by
  cases e <;> simp_all [liftN]

private theorem liftN_const_inv {e : ProofShape} (H : e.liftN n k = .const c ls) : e = .const c ls := by
  cases e <;> simp_all [liftN]
end ProofShape


private theorem erase_sort_inv (H : proofErase Γ e = .sort u) : e = .sort u := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all

/-- Both comparison modes descend from independently typed originals. Common
mode requires a lower type conversion; inferred mode instead requires that the
left endpoint is not a proof. Every computed intermediate is reconstructed below. -/
theorem proofErase_compare_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.Compare Step mode ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  induction H generalizing Γ Γ' k a b A B with
  | refl =>
    have EE := ProofShape.liftN_inj.1 (Ea.trans Eb.symm)
    have HH := proofErase_reflect hΓ ha hb EE
    exact ⟨fun ht => let ⟨_, h⟩ := HH.1 ht; h.defeq hΓ,
      fun _ hn => let ⟨_, h⟩ := HH.2 hn; h.defeq hΓ⟩
  | sort hu =>
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Ea)
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Eb)
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.sortDF (ha.sort_inv henv) (hb.sort_inv henv) hu⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | const hl =>
    obtain rfl := erase_const_inv (ProofShape.liftN_const_inv Ea)
    obtain rfl := erase_const_inv (ProofShape.liftN_const_inv Eb)
    obtain ⟨ci, hc, hw, hn⟩ := ha.const_inv henv hΓ
    obtain ⟨_, _, hw', _⟩ := hb.const_inv henv hΓ
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.constDF hc hw hw' hn hl⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | app Hf Hx ihf ihx =>
    obtain ⟨_, _, haE, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, hbE, Ebf, Ebx⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv haE
    obtain ⟨f', x', rfl, _, Ef', Ex'⟩ := erase_app_inv hbE
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Ef'] at Ebf
    rw [← Ex'] at Ebx
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    have HF := (ihf hΓ hΓ' W hf hf' Eaf Ebf).2 rfl (not_isProof_fn hΓ hf hx hna)
    have HFF := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (HFF.hasType.2.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HX := (ihx hΓ hΓ' W hx hx' Eax Ebx).1 ⟨_, hDD⟩
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.appDF HFF (HX.of_l henv hΓ hx)⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | proj Hm ihm =>
    obtain ⟨_, haE, Eam⟩ := ProofShape.liftN_proj_inv Ea
    obtain ⟨_, hbE, Ebm⟩ := ProofShape.liftN_proj_inv Eb
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv haE
    obtain ⟨m', rfl, _, Em'⟩ := erase_proj_inv hbE
    rw [← Em] at Eam
    rw [← Em'] at Ebm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HM := (ihm hΓ hΓ' W hm.hasType.2 hm'.hasType.2 Eam Ebm).2 rfl (not_isProof_major hΓ ha hn)
    have HH : env.IsDefEqU univs Γ _ _ :=
      ⟨_, SimAt.proj henv.orderedStrong hΓ (fun _ ht => HM.of_l henv hΓ ht) _ ha⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | lam HD Hbody ihD ihbody =>
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
    have HDU := (ihD hΓ hΓ' W hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
    rw [Ectx] at Ebb
    have hbody'' := hbody'.defeqDFC henv hctx
    have HI := ihbody hΓD hΓD' W.succ hbody hbody'' Eab Ebb
    have finish (HH : env.IsDefEqU univs (D :: Γ) body body') :
        env.IsDefEqU univs Γ (.lam D body) (.lam D' body') :=
      ⟨_, IsDefEq.lamDF HDD (HH.of_l henv hΓD hbody)⟩
    constructor
    · intro hAB
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨_, _, hCC⟩ := HPi.forallE_inv henv hΓ
      exact finish (HI.1 ⟨_, hCC⟩)
    · intro hmode hn
      exact finish (HI.2 hmode (fun hp => hn (hp.lam hΓ hD)))
  | forallE HD HC ihD ihC =>
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
    have HDU := (ihD hΓ hΓ' W hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have HCU := (ihC hΓD hΓD' W.succ hC (hC'.defeqDFC henv hctx) EaC EbC).2 rfl
      (not_isProof_of_sort hΓD hC)
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | etaL Hη =>
    rw [← Ea, ← Eb] at Hη
    refine ⟨fun hAB => ?_, fun h => by cases h⟩
    exact ⟨_, proofErase_eta_head_reflect hΓ ha (hb.defeqU_r henv hΓ hAB.symm) Hη.of_liftN⟩
  | etaR Hη =>
    rw [← Ea, ← Eb] at Hη
    refine ⟨fun hAB => ?_, fun h => by cases h⟩
    exact ⟨_, (proofErase_eta_head_reflect hΓ hb (ha.defeqU_r henv hΓ hAB) Hη.of_liftN).symm⟩
  | structL Hη =>
    rw [← Ea, ← Eb] at Hη
    refine ⟨fun hAB => ?_, fun h => by cases h⟩
    exact ⟨_, proofErase_structure_eta_reflect hΓ ha (hb.defeqU_r henv hΓ hAB.symm) Hη.of_liftN⟩
  | structR Hη =>
    rw [← Ea, ← Eb] at Hη
    refine ⟨fun hAB => ?_, fun h => by cases h⟩
    exact ⟨_, (proofErase_structure_eta_reflect hΓ hb (ha.defeqU_r henv hΓ hAB) Hη.of_liftN).symm⟩
  | etaLams HD Hη ihD =>
    rw [← Ea, ← Eb] at Hη
    obtain ⟨_, _, haE, EaD, _⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, _⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', _⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← ED'] at EbD
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.lam_inv henv hΓ
    have HDD := (ihD hΓ hΓ' W hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HH : env.IsDefEqU univs Γ (.lam D body) (.lam D' body') := by
      rcases Hη with Hη | Hη
      · exact proofErase_eta_head_infer hΓ ha (HasType.lam hD' hbody') HDD Hη.of_liftN
      · exact (proofErase_eta_head_infer hΓ hb (HasType.lam hD hbody) HDD.symm Hη.of_liftN).symm
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | compute Ra Rb HC ih =>
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W ha Ra
    obtain ⟨b', HB, EB⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hb Rb
    have HI := ih hΓ hΓ' W HA.hasType.2 HB.hasType.2 EA EB
    have finish (HH : env.IsDefEqU univs Γ a' b') : env.IsDefEqU univs Γ a b :=
      ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HH).trans henv hΓ ⟨_, HB.symm⟩
    exact ⟨fun hAB => finish (HI.1 hAB),
      fun hmode hn => finish (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn))⟩

/-- The generic descent theorem specializes to direct reflection in one context. -/
theorem proofErase_compare_reflect (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.Compare Step mode (proofErase Γ a) (proofErase Γ b)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  exact proofErase_compare_descend hstep hΓ hΓ W ha hb (by simpa only [ProofShape.liftN_zero] using H)

/-- Recursive comparison built on any finite erased K stage descends at a
common type. Its comparisons may contain eta inside aligned subterms. -/
theorem proofErase_K_compare_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ProofShape.Compare (ErasedKStage D stage) true
      (proofErase Γ' (a.liftN n k)) (proofErase Γ' (b.liftN n k))) :
    env.IsDefEq univs Γ a b T := by
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb] at H
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  exact ((proofErase_compare_descend (erased_K_stage_descent heq hs stage) hΓ hΓ' W ha hb H).1
    ⟨_, hT⟩).of_l henv hΓ ha

end Lean4Lean.VEnv.Strengthening
