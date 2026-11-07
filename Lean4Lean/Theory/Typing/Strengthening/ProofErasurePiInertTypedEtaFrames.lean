import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertInferredHeadCut

/-! # Typed eta preserves rigid-sort body frames

The eta terminal of inferred lambda comparison retains its actual domains.
Weakening under the long endpoint's binder constructs the expanded body.
Conversely, its fresh typed variable consumes the inner lambda and typed
context conversion returns the short body to its own annotation context.
Both retained-variable and proof-marker eta are covered; no guarded path is
substituted or transported across merely equal domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- Actual typed substitution transports frame data at the erasure of the
substituted original, including when a substituted variable erases as proof. -/
theorem RigidSortFrames.typed_substitute
    (H : RigidSortFrames c (proofEraseCtx Γ) (proofErase Γ e))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ht : env.HasType univs Γ e T) :
    RigidSortFrames c (proofEraseCtx Γ₀) (proofErase Γ₀ (e.subst σ)) := by
  have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ht ES]
  exact H.subst (ContextSubstitution.of_typed hΓ₀ W ES)

/-- Arbitrary binder insertion preserves the frame tree at the exact lifted
original. This includes insertion beneath the lambda's own binder. -/
theorem RigidSortFrames.weakN
    (H : RigidSortFrames c (proofEraseCtx Γ) (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    RigidSortFrames c (proofEraseCtx Γ') (proofErase Γ' (e.liftN n k)) := by
  rw [proofErase_liftN hΓ hΓ' W ht]
  have H' := H.subst (ContextRenaming.of_liftN hΓ hΓ' W).interpretation
  simpa only [subst_bvar_liftN] using H'

/-- A framed lambda application either discards its argument at the live
head or is an identity frame whose argument carries the rigid head. -/
theorem RigidSortFrames.lambda_app_inv
    (H : RigidSortFrames c Δ (.app (.lam A b) x)) :
    RigidSortFrames c (A :: Δ) b ∨ b = .bvar 0 ∧ RigidSortFrames c Δ x := by
  cases H with
  | constant _ HB => exact .inl HB
  | identity _ HX => exact .inr ⟨rfl, HX⟩

/-- At actually equal lambda domains and sort-typed bodies, displayed eta
preserves the entire body-frame predicate in both directions. Proof-domain
eta is allowed: erasure agreement uses the actual typed fresh argument. -/
theorem RigidSortFrames.typed_eta_iff
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAC : env.IsDefEq univs Γ A C (.sort w))
    (hb : env.HasType univs (A :: Γ) b (.sort u))
    (hd : env.HasType univs (C :: Γ) d (.sort v))
    (HE : EtaHead (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d))) :
    RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) ↔
      RigidSortFrames c (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d) := by
  have hA := HAC.hasType.1
  have hC := HAC.hasType.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, w, hC⟩
  have hΓAC : OnCtx (C.lift :: A :: Γ) (env.IsType univs) := ⟨hΓA, w, hC.weak henv⟩
  have W : Ctx.LiftN 1 1 (C :: Γ) (C.lift :: A :: Γ) := Ctx.LiftN.one.succ
  have hdw := hd.weakN henv W
  have EL : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ (.lam hA hb))
  have ES : proofErase Γ (.lam C d) = .lam (proofErase Γ C) (proofErase (C :: Γ) d) :=
    if_neg (not_isProof_function_to_sort hΓ (.lam hC hd))
  obtain ⟨rawA, arg, EE, Harg⟩ := HE.shape
  rw [EL, ES] at EE
  have EB := (ProofShape.lam.inj EE).2
  simp only [ProofShape.liftN] at EB
  have EC := proofErase_liftN hΓ hΓA Ctx.LiftN.one hC
  have ED := proofErase_liftN hΓC hΓAC W hd
  have Ebody : proofErase (A :: Γ) b =
      .app (.lam (proofErase (A :: Γ) C.lift)
        (proofErase (C.lift :: A :: Γ) (d.liftN 1 1))) arg := by
    rw [EC, ED]
    exact EB
  constructor
  · intro H
    rw [Ebody] at H
    rcases H.lambda_app_inv with HB | ⟨_, HX⟩
    · have hx : env.HasType univs (A :: Γ) (.bvar 0) C.lift :=
        (HAC.weak henv).defeq (.bvar .zero)
      have Hinst := HB.typed_substitute hΓA (Ctx.InstN.zero.substEq hΓAC hx) hdw
      have Hbody : RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) d) := by
        simpa only [← instN_eq, VExpr.inst_liftN_bvar] using Hinst
      have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
      have Hout := Hbody.context (ContextSubstitution.of_defeqCtx hΓ HC)
      have hdA := hd.defeqDFC henv (IsDefEqCtx.succ .zero HAC.symm)
      rwa [proofErase_defeqCtx hΓA HC hdA] at Hout
    · rcases Harg with rfl | rfl <;> cases HX
  · intro H
    have HB := H.weakN hΓC hΓAC W hd
    have HT : ControlTyping (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) (.sort u) :=
      .of_typed hΓA hb
    rw [Ebody] at HT ⊢
    exact .constant HT HB

/-- Either orientation of a typed eta terminal preserves rigid-sort frames.
The bodies keep their own actual annotation contexts throughout. -/
theorem RigidSortFrames.typed_eta_pair_iff
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAC : env.IsDefEq univs Γ A C (.sort w))
    (hb : env.HasType univs (A :: Γ) b (.sort u))
    (hd : env.HasType univs (C :: Γ) d (.sort v))
    (HE : EtaHead (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d)) ∨
      EtaHead (proofErase Γ (.lam C d)) (proofErase Γ (.lam A b))) :
    RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) ↔
      RigidSortFrames c (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d) := by
  rcases HE with HE | HE
  · exact typed_eta_iff hΓ HAC hb hd HE
  · exact (typed_eta_iff hΓ HAC.symm hd hb HE).symm

/-- The explicit inferred domain child supplies the equality required by
typed eta frame transport. This discharges the eta terminal of the comparison
cut under actual body typings, without a carrier-conversion assumption. -/
theorem RigidSortFrames.inferred_eta_pair_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort w)) (hC : env.HasType univs Γ C (.sort z))
    (hb : env.HasType univs (A :: Γ) b (.sort u))
    (hd : env.HasType univs (C :: Γ) d (.sort v))
    (HD : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C))
    (HE : EtaHead (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d)) ∨
      EtaHead (proofErase Γ (.lam C d)) (proofErase Γ (.lam A b))) :
    RigidSortFrames c (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) ↔
      RigidSortFrames c (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d) := by
  have hstep : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht HR.1
  have HAC := (proofErase_computed_joint_compare_reflect hstep hΓ hA hC HD).2 rfl
    (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hC)
  exact typed_eta_pair_iff hΓ (HAC.of_l henv hΓ hA) hb hd HE

end Lean4Lean.VEnv.Strengthening
