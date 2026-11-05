import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainTransport

/-! # Lambda-domain readout after arbitrary control computation

The finite observer has an operational interpretation: a beta path exposes a
lambda whose domain is a computed lower domain. The resulting body is arbitrary;
no body-origin, global confluence, or type-fork-joining claim is made.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
variable [Params] {D : PureObservation.Definitions}
namespace LambdaDomainObservation
open PureObservation (Ob Sets)

/-- Operational meaning retaining the lower domain history and allowing an arbitrary lambda body. -/
def Realizes (D : PureObservation.Definitions) (Γ : List VExpr) (anchor : ProofShape) (n : Nat) (e : ProofShape) : Ob → Prop
  | .pi => ∃ A u b, env.HasType univs Γ A (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) anchor (proofErase Γ A) ∧
      ProofShape.BetaRed e (.lam ((proofErase Γ A).liftN n) b)
  | .sort => False
  | .app keys o => ∀ a, (∀ key ∈ keys, Realizes D Γ anchor n a key) → Realizes D Γ anchor n (.app e a) o
termination_by o => sizeOf o

/-- Beta predecessors realize the same payload. -/
theorem Realizes.beta_back (R : ProofShape.BetaRed e e') (H : Realizes D Γ anchor n e' o) : Realizes D Γ anchor n e o := by
  cases o with
  | pi =>
    simp only [Realizes] at H ⊢
    obtain ⟨A, u, b, hA, RA, H⟩ := H
    exact ⟨A, u, b, hA, RA, R.trans H⟩
  | sort => simp only [Realizes] at H
  | app keys o =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Domain observations beta-expose a lambda after every substitution that fixes
original variables and supplies the finite control demands. No typing or native
recovery is required of these operational substitution images. -/
theorem Obs.realizes (H : Obs D Γ anchor n Δ S e o) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → Realizes D Γ anchor m (σ i) key) : Realizes D Γ anchor m (e.subst σ) o := by
  induction H generalizing m σ with
  | var h => exact hσ _ _ h
  | payload h =>
    obtain ⟨A, u, hA, rfl, RA⟩ := h
    simp only [Realizes, ProofShape.subst, HT.payload]
    exact ⟨A, u, _, hA, RA, .refl⟩
  | app _ _ ihf iha =>
    have HF := ihf HT hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk HT hσ)
  | @lam Δ A u keys n S b o _ _ _ ih =>
    simp only [Realizes]
    intro a ha
    have HB := ih HT.cons (fun i key hi => by
      cases i with
      | zero => exact ha key hi
      | succ i => exact hσ i key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back (E ▸ (ProofShape.BetaRed.beta (A := A.subst σ))) HB

/-- At depth zero an empty control valuation reads a lambda with the certified
lower domain. Its body is not claimed to come from the original payload. -/
theorem Obs.readout (H : Obs D Γ anchor 0 Δ (fun _ _ => False) e .pi) :
    ∃ A u b, env.HasType univs Γ A (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) anchor (proofErase Γ A) ∧
      ProofShape.BetaRed e (.lam (proofErase Γ A) b) := by
  have HT : FixedTail 0 0 ProofShape.Subst.id := by intro i; rfl
  have R := H.realizes HT (fun _ _ h => h.elim)
  simpa only [ProofShape.subst_id, Realizes, ProofShape.liftN_zero] using R


end LambdaDomainObservation
/-- Every full-union computation from a retained lambda admits a finite beta
readout whose domain is reached by computation from the original domain.
Only the domain has an origin certificate; the readout body is unrestricted. -/
theorem proofErase_static_structure_lambda_domain_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out) :
    ∃ A' u' b', env.HasType univs Γ A' (.sort u') ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧
      ProofShape.BetaRed out (.lam (proofErase Γ A') b') := by
  have H : LambdaDomainObservation.Obs D Γ (proofErase Γ A) 0 (proofEraseCtx Γ)
      (fun _ _ => False) (proofErase Γ (.lam A b)) .pi := by
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn]
    exact .payload ⟨A, u, hA, ProofShape.liftN_zero _, .refl⟩
  exact (H.compute heq hs hΓ R hΓ (Ctx.LiftN.zero []) (HasType.lam hA hb) rfl rfl
    (fun _ _ h => h.elim)).readout

/-- If two retained lambdas compute to a common endpoint, their written domains
compute to a common endpoint too. One finite beta readout of the common term
suffices; no confluence or type-fork-joining hypothesis is used. -/
theorem proofErase_static_structure_lambda_domain_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hC : env.HasType univs Γ C (.sort v)) (hd : env.HasType univs (C :: Γ) d E)
    (hn : ¬ IsProof Γ (.lam A b)) (hm : ¬ IsProof Γ (.lam C d))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam C d)) out) :
    ∃ X, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) X ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ C) X := by
  obtain ⟨A', _, b', _, RA, Rβ⟩ :=
    proofErase_static_structure_lambda_domain_readout heq hs hΓ hA hb hn RL
  exact ⟨proofErase Γ A', RA,
    proofErase_static_structure_lambda_domain_compute heq hs hΓ hC hd hm (RR.trans (.beta Rβ))⟩

/-- Even after arbitrary control computation, every selected native Pi domain
has a forward history from the original lambda domain. This does not assert
exact native recovery of the current term at an earlier selected type. -/
theorem proofErase_static_structure_computed_lambda_native_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.forallE X Y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) X := by
  have H : LambdaDomainObservation.Obs D Γ (proofErase Γ A) 0 (proofEraseCtx Γ)
      (fun _ _ => False) (proofErase Γ (.lam A b)) .pi := by
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn]
    exact .payload ⟨A, u, hA, ProofShape.liftN_zero _, .refl⟩
  have HO := H.compute heq hs hΓ R hΓ (Ctx.LiftN.zero []) (HasType.lam hA hb) rfl rfl
    (fun _ _ h => h.elim)
  obtain ⟨e', HE, Ee⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ (HasType.lam hA hb) rfl rfl R
  have HD := HO.native heq hs hΓ hΓ (Ctx.LiftN.zero []) HE.hasType.2 rfl Ee
    (fun _ _ h => h.elim) RN
  obtain ⟨A', _, _, E, RA⟩ := HD.domain
  simp only [ProofShape.liftN_zero] at E
  exact E ▸ RA

end Lean4Lean.VEnv.Strengthening
