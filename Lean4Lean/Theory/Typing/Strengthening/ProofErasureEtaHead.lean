import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaForward

/-! # Eta comparison with a typed short endpoint

An erased eta contractum need not have an original representative. When both
endpoints already have originals at a common type, the short endpoint supplies
the needed function typing. This proves head eta reflection, including a bound
proof variable erased to a marker, without asserting arbitrary eta replay.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- A displayed eta comparison. Its final argument is either the retained bound
variable or its proof marker. Sound reflection requires common-typed originals. -/
inductive EtaHead : ProofShape → ProofShape → Prop where
  | boundVar : EtaHead (.lam A (.app (f.liftN 1) (.bvar 0))) f
  | proof : EtaHead (.lam A (.app (f.liftN 1) .proof)) f

/-- Expose the long endpoint and its retained or erased bound argument. -/
theorem EtaHead.shape (H : EtaHead e f) :
    ∃ A arg, e = .lam A (.app (f.liftN 1) arg) ∧ (arg = .bvar 0 ∨ arg = .proof) := by
  cases H with
  | boundVar => exact ⟨_, _, rfl, .inl rfl⟩
  | proof => exact ⟨_, _, rfl, .inr rfl⟩

/-- Binder insertion preserves both forms of displayed eta comparison. -/
theorem EtaHead.liftN (H : EtaHead e f) : EtaHead (e.liftN n k) (f.liftN n k) := by
  cases H with
  | @boundVar A f =>
    simp only [ProofShape.liftN]
    rw [← liftN_comm f n 1 k 0 (Nat.zero_le _)]
    simpa only [liftVar, Nat.zero_lt_succ, if_true] using
      (EtaHead.boundVar (A := A.liftN n k) (f := f.liftN n k))
  | @proof A f =>
    simp only [ProofShape.liftN]
    rw [← liftN_comm f n 1 k 0 (Nat.zero_le _)]
    exact .proof

/-- Displayed eta comparison reflects through insertion when both endpoints
are already lifts. No original typing is needed for this syntactic fact. -/
theorem EtaHead.of_liftN (H : EtaHead (e.liftN n k) (f.liftN n k)) : EtaHead e f := by
  obtain ⟨A, arg, HE, Harg⟩ := H.shape
  cases e <;> simp only [ProofShape.liftN] at HE <;> try contradiction
  case lam A₀ b =>
    obtain ⟨rfl, Hb⟩ := ProofShape.lam.inj HE
    cases b <;> simp only [ProofShape.liftN] at Hb <;> try contradiction
    case app g x =>
      obtain ⟨Hg, Hx⟩ := ProofShape.app.inj Hb
      rw [liftN_comm f n 1 k 0 (Nat.zero_le _)] at Hg
      obtain rfl := liftN_inj.1 Hg
      rcases Harg with rfl | rfl
      · have hx : x = .bvar 0 := liftN_inj.1 (show x.liftN n (k+1) = (ProofShape.bvar 0).liftN n (k+1) by
          simpa only [ProofShape.liftN, liftVar, Nat.zero_lt_succ, if_true] using Hx)
        rw [hx]
        exact .boundVar
      · have hx : x = .proof := liftN_inj.1 Hx
        rw [hx]
        exact .proof

/-- Substitution preserves the displayed eta pattern, including the marker
case, because the short endpoint is lifted beneath the bound variable. -/
theorem EtaHead.subst (H : EtaHead e f) : EtaHead (e.subst σ) (f.subst σ) := by
  cases H with
  | boundVar =>
    simp only [ProofShape.subst, lift_subst_lift, Subst.lift]
    exact .boundVar
  | proof =>
    simp only [ProofShape.subst, lift_subst_lift]
    exact .proof
end ProofShape

variable [Params]

private theorem erase_bvar_inv (H : proofErase Γ e = .bvar i) : e = .bvar i := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all

/-- A literal variable or an erased proof argument is equal to the fresh
variable when both have its type. The proof case transports the fresh variable
to the argument's proposition before applying proof irrelevance. -/
private theorem eta_argument (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (ha : env.HasType univs (A :: Γ) a A.lift)
    (H : proofErase (A :: Γ) a = .bvar 0 ∨ proofErase (A :: Γ) a = .proof) :
    env.IsDefEqU univs (A :: Γ) a (.bvar 0) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rcases H with H | H
  · obtain rfl := erase_bvar_inv H
    exact ⟨_, ha⟩
  · obtain ⟨P, haP, hP⟩ := proofErase_eq_proof.1 H
    have hAP := ha.uniqU henv hΓA haP
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    exact ⟨_, IsDefEq.proofIrrel hP haP (hx.defeqU_r henv hΓA hAP)⟩

/-- Every typed original function eta equation erases either to identity or to
one of the displayed head comparisons. Proof-valued functions give identity. -/
theorem proofErase_eta_forward (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    proofErase Γ (.lam A (.app f.lift (.bvar 0))) = proofErase Γ f ∨
      ProofShape.EtaHead (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  have Hη := IsDefEq.eta hf
  obtain ⟨⟨u, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hp := isProof_congr hΓ Hη
  by_cases hpf : IsProof Γ f
  · exact .inl ((proofErase_eq_proof.2 (hp.2 hpf)).trans (proofErase_eq_proof.2 hpf).symm)
  have hnl := mt hp.1 hpf
  have hnb : ¬ IsProof (A :: Γ) (.app f.lift (.bvar 0)) := fun h => hnl (h.lam hΓ hA)
  have Ef := proofErase_liftN hΓ hΓA Ctx.LiftN.one hf
  apply Or.inr
  simp only [proofErase, if_neg hnl, if_neg hnb]
  change ProofShape.EtaHead
    (.lam (proofErase Γ A) (.app (proofErase (A :: Γ) f.lift) (proofErase (A :: Γ) (.bvar 0))))
    (proofErase Γ f)
  rw [Ef]
  by_cases hx : IsProof (A :: Γ) (.bvar 0)
  · rw [proofErase_eq_proof.2 hx]
    exact .proof
  · simp only [proofErase, if_neg hx]
    exact .boundVar

/-- Head eta comparison reflects at a common original type. Hidden proof
dependencies in the long endpoint need no untyped representative: the supplied
short endpoint and source inversion align the function and argument types. -/
theorem proofErase_eta_head_reflect (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f)) :
    env.IsDefEq univs Γ e f T := by
  obtain ⟨_, arg, HE, Harg⟩ := H.shape
  obtain ⟨A, body, rfl, _, _, Hb⟩ := erase_lam_inv HE
  obtain ⟨g, a, rfl, hnb, Hg, Ha⟩ := erase_app_inv Hb
  obtain ⟨⟨u, hA⟩, B, hb⟩ := he.lam_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hfPi : env.HasType univs Γ f (.forallE A B) :=
    hf.defeqU_r henv hΓ (he.uniqU henv hΓ (HasType.lam hA hb))
  have hfw := hfPi.weak henv (B := A)
  have Ef := proofErase_liftN hΓ hΓA Ctx.LiftN.one hfPi
  have Eg : proofErase (A :: Γ) g = proofErase (A :: Γ) f.lift := Hg.trans Ef.symm
  obtain ⟨_, _, hg, ha⟩ := HasType.app_inv henv hΓA hb
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓA hg hfw Eg).2 (not_isProof_fn hΓA hg ha hnb)
  have Hgf := (HC.defeq hΓA).of_l henv hΓA hg
  obtain ⟨⟨_, hCA⟩, _⟩ := (Hgf.hasType.2.uniqU henv hΓA hfw).forallE_inv henv hΓA
  have haA := hCA.defeq ha
  have Hax := eta_argument hΓ hA haA (Harg.elim (fun h => .inl (Ha.trans h)) (fun h => .inr (Ha.trans h)))
  have Hbody := IsDefEq.appDF Hgf (Hax.of_l henv hΓA ha)
  have Hbody' := (show env.IsDefEqU univs (A :: Γ) _ _ from ⟨_, Hbody⟩).of_l henv hΓA hb
  have Heta := (IsDefEq.lamDF hA Hbody').trans (IsDefEq.eta hfPi)
  exact (show env.IsDefEqU univs Γ _ _ from ⟨_, Heta⟩).of_l henv hΓ he

/-- Head eta matching of lifted erasures reflects below whenever both originals
already have a common type there. Exact contraction replay is not required. -/
theorem proofErase_eta_head_descend
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ' (e.liftN n k)) (proofErase Γ' (f.liftN n k))) :
    env.IsDefEq univs Γ e f T := by
  rw [proofErase_liftN hΓ hΓ' W he, proofErase_liftN hΓ hΓ' W hf] at H
  exact proofErase_eta_head_reflect hΓ he hf H.of_liftN

/-- Compatible computations may end at an eta comparison instead of a literally
equal erased target. Typed descent supplies both lower endpoint representatives,
which are precisely what head eta reflection needs. -/
theorem proofErase_typed_eta_join_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (Ra : ProofShape.Compute Step ((proofErase Γ a).liftN n k) left)
    (Rb : ProofShape.Compute Step ((proofErase Γ b).liftN n k) right)
    (H : ProofShape.EtaHead left right) : env.IsDefEq univs Γ a b T := by
  obtain ⟨a', HA, EA⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W ha Ra
  obtain ⟨b', HB, EB⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hb Rb
  rw [← EA, ← EB] at H
  exact HA.trans ((proofErase_eta_head_reflect hΓ HA.hasType.2 HB.hasType.2 H.of_liftN).trans HB.symm)

end Lean4Lean.VEnv.Strengthening
