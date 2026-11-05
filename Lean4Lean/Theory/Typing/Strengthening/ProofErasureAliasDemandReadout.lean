import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandTransport
import Lean4Lean.Theory.Typing.Strengthening.StructureFamilyArity

/-! # Family readout through stored aliases

Full enriched computation preserves the observation. Readout then uses only
ordinary erased computation, including genuine stored delta, after arbitrary
raw substitution. Finite evidence suffices even in a recursive environment.
-/
namespace Lean4Lean.VEnv.Strengthening.AliasDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open DemandProfile
open PureObservation (Ob)
variable [Params] {c : Name} {arity : Nat} {P : ProofShape → Prop}

/-- Dependent typing decorations do not constrain operational substitution:
supplying the free demands suffices for every raw realizing substitution. -/
theorem Obs.realizes (H : Obs c arity Δ S e t o)
    (hP : ∀ {e e'}, ProofShape.BetaRed e e' → P e' → P e)
    (hdelta : ∀ name rhs, (PureObservation.Definitions.ofEnv env univs henv).unfolds name [] rhs →
      P (proofErase [] rhs) → P (.const name []))
    (hconst : ∀ ls, Realizes P (.const c ls) (spineDemand arity))
    (hσ : ∀ i t key, S i t key → Realizes P (σ i) key) :
    Realizes P (e.subst σ) o := by
  induction H generalizing σ with
  | const => exact hconst _
  | delta _ HD _ ih =>
    simp only [Realizes, ProofShape.subst]
    apply hdelta _ _ HD
    simpa only [Realizes, proofErase_closed_subst
      ((PureObservation.Definitions.ofEnv env univs henv).closed HD)] using ih hσ
  | var _ _ h => exact hσ _ _ _ h
  | app _ _ _ ihf ihx =>
    have HF := ihf hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => ihx key hk hσ)
  | @lam Δ D b A B keys S o HT HK HB ih =>
    simp only [Realizes]
    intro a ha
    have H := ih (σ := σ.cons a) (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one,
          ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back hP (E ▸ (ProofShape.BetaRed.beta (A := D.subst σ))) H

/-- The operational result retains the constant head and exact spine length,
while permitting arbitrary argument expressions at the exposed endpoint. -/
def HeadResult (c : Name) (n : Nat) (e : ProofShape) : Prop :=
  ∃ ls args, args.length = n ∧ ProofShape.Compute
    (ErasedIotaPrimitive (PureObservation.Definitions.ofEnv env univs henv))
    e (ProofShape.mkApps (.const c ls) args)

/-- Completing the remaining applications realizes a head demand. -/
theorem head_spine_realizes (h : args.length + k = n) :
    Realizes (HeadResult c n) (ProofShape.mkApps (.const c ls) args) (spineDemand k) := by
  induction k generalizing args with
  | zero =>
    simp only [spineDemand, Realizes, HeadResult]
    exact ⟨ls, args, by simpa using h, .refl⟩
  | succ k ih =>
    simp only [spineDemand, Realizes]
    intro a _
    have R := ih (args := args ++ [a]) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa only [ProofShape.mkApps_snoc] using R

/-- Empty free demands allow every raw substitution, without typing or native
recovery of its images. The final head has the original arity. -/
theorem Obs.head_readout (H : Obs c arity Δ (fun _ _ _ => False) e t .pi) :
    HeadResult c arity (e.subst σ) := by
  have HR := H.realizes (P := HeadResult c arity) (σ := σ)
    (fun R H => by obtain ⟨ls, args, hn, RB⟩ := H; exact ⟨ls, args, hn, (Compute.beta R).trans RB⟩)
    (fun name rhs HD H => by
      obtain ⟨ls, args, hn, RB⟩ := H
      exact ⟨ls, args, hn, (Compute.base (.inl (.inl (.delta HD)))).trans RB⟩)
    (fun ls => head_spine_realizes (args := []) (by simp))
    (fun _ _ _ h => h.elim)
  simpa only [Realizes] using HR

/-- Every full enriched descendant of a finitely observed alias has a family
head after arbitrary raw substitution. The cleanup relation is the actual stored
ordinary core, so it can be replayed below binders from source typing. -/
theorem Obs.full_readout
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c)
    (H : Obs c arity Δ (fun _ _ _ => False) e t .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion
      (PureObservation.Definitions.ofEnv env univs henv)) Δ e out) :
    HeadResult c arity (out.subst σ) :=
  (H.static_structure_union heq hcon hc R (fun _ _ _ h => h.elim)).head_readout

/-- Applying a typed telescope discharges the ignored demands one by one.
Only ordinary argument typing is used, including at proof and data parameters. -/
theorem Obs.telescope (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f T)
    (HP : Fits Γ T (spineProfile args.length))
    (HW : InstForallsC env univs Γ T args result)
    (H : Obs c arity (proofEraseCtx Γ) S (proofErase Γ f)
      (spineProfile args.length) (spineDemand args.length)) :
    Obs c arity (proofEraseCtx Γ) S (proofErase Γ (VExpr.mkApps f args)) .sort .pi := by
  induction HW generalizing f with
  | nil => exact H
  | @cons a A args result B ha HW ih =>
    obtain ⟨HA, HB⟩ := HP.forallE_inv hΓ
    obtain ⟨u, hA⟩ := HA.isType
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA ha
    have HPI : Fits Γ (B.inst a) (spineProfile args.length) := by
      simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
    have hfa := HasType.app hf ha
    have E : proofErase Γ (.app f a) = .app (proofErase Γ f) (proofErase Γ a) :=
      if_neg (HPI.not_isProof hΓ (spineDemand_valid args.length).visible hfa)
    have HT : Typing (proofEraseCtx Γ) (.app (proofErase Γ f) (proofErase Γ a))
        (spineProfile args.length) := ⟨Γ, _, _, hΓ, rfl, hfa, HPI, E⟩
    have HO : Obs c arity (proofEraseCtx Γ) S (proofErase Γ (.app f a))
        (spineProfile args.length) (spineDemand args.length) := by
      rw [E]
      exact .app (keys := []) HT H (by simp)
    exact ih hfa HPI HO

end Lean4Lean.VEnv.Strengthening.AliasDemandProfile
