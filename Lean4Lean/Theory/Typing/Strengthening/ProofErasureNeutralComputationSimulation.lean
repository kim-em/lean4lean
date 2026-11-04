import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNeutralRecovery

/-! # Neutral type simulation from typed context transport

Simulation follows computation, including its actual transitive intermediates.
It needs only context transport at recursively neutral-related oracle types;
it does not assume substitution of arbitrary values into primitive guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private variableHead variableHead_mkApps bvar_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
variable [Params]

/-- Typed computation transport between equal contexts whose oracle types
change recursively at neutral leaves. This explicit interface requires no
arbitrary substitution closure. It will be discharged separately for stages. -/
def RecursiveNeutralComputeContext
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' e T out k}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    IsDefEqCtx env univs [] Γ Γ' →
    (∀ i, NeutralTypeChange k (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i)) →
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) out →
    ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ e) out

/-- The context interface accepts arbitrary raw representatives with their
actual typing and erasure witnesses. -/
theorem RecursiveNeutralComputeContext.raw (HC : RecursiveNeutralComputeContext Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i))
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (R : ScopedCompute Step Δ source out) : ScopedCompute Step (proofEraseCtx Γ') source out := by
  subst Δ
  subst source
  exact HC hΓ ht W HO R

omit [Params] in
private theorem beta_simulate (H : NeutralTypeChange k A B) (R : BetaRed A A') :
    ∃ B', BetaRed B B' ∧ NeutralTypeChange k A' B' := by
  induction H generalizing A' with
  | refl => exact ⟨_, R, .refl⟩
  | neutral hi hj =>
    obtain ⟨args', rfl, _⟩ := R.bvar_spine
    exact ⟨_, .refl, .neutral hi hj⟩
  | forallE HD HC ihD ihC =>
    obtain ⟨D', C', rfl, RD, RC⟩ := beta_forallE_parts R
    obtain ⟨D'', RD', HD'⟩ := ihD RD
    obtain ⟨C'', RC', HC'⟩ := ihC RC
    exact ⟨_, .forallE RD' RC', .forallE HD' HC'⟩

/-- Simulate a typed carrier computation using only typed recursive neutral
context transport. Transitive intermediates are realized on both sides;
Pi bodies move once between the corresponding original binder domains.
No computation path is moved backwards through a changed intermediate domain. -/
theorem ProofShape.NeutralTypeChange.compute_of_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hctx : RecursiveNeutralComputeContext Step)
    (H : NeutralTypeChange k a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EΓ : proofEraseCtx Γ = Δ) (EA : proofErase Γ A = a) (EB : proofErase Γ B = b)
    (R : ScopedCompute Step Δ a out) :
    ∃ out', ScopedCompute Step Δ b out' ∧ NeutralTypeChange k out out' := by
  induction R generalizing Γ A B u k b with
  | base R =>
    cases H with
    | refl => exact ⟨_, .base R, .refl⟩
    | neutral => exact (bvar_spine_not_primitive _ (hhead R)).elim
    | forallE => exact (hhead R).elim
  | beta R =>
    obtain ⟨out', RB, HB⟩ := beta_simulate H R
    exact ⟨_, .beta RB, HB⟩
  | trans R S ihR ihS =>
    obtain ⟨mid, RB, HM⟩ := ihR H hΓ HAB EΓ EA EB
    obtain ⟨A', HAA, EA'⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.1 EΓ EA R
    obtain ⟨B', HBB, EB'⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.2 EΓ EB RB
    obtain ⟨out', RS, HS⟩ := ihS HM hΓ ((HAA.symm.trans HAB).trans HBB) EΓ EA' EB'
    exact ⟨_, RB.trans RS, HS⟩
  | forallE RD RC ihD ihC =>
    obtain ⟨rawD', rawC', rfl, HD, HC⟩ := H.forallE_inv
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv EA
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv EB
    obtain ⟨⟨v, Hdom⟩, ⟨w, Hcod⟩⟩ := HAB.toU.forallE_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, v, Hdom.hasType.1⟩
    have W : IsDefEqCtx env univs [] (D :: Γ) (D' :: Γ) := .succ (.refl hΓ) Hdom
    have EC'' := (proofErase_defeqCtx hΓD W Hcod.hasType.2).trans EC'
    obtain ⟨d, RD', HD'⟩ := ihD HD hΓ Hdom EΓ ED ED'
    obtain ⟨c, RC', HC'⟩ := ihC HC hΓD Hcod
      (by simp only [proofEraseCtx, EΓ, ED]) EC EC''
    have HO : ∀ i, NeutralTypeChange 0
        (contextOracle (proofEraseCtx (D :: Γ)) i)
        (contextOracle (proofEraseCtx (D' :: Γ)) i) := by
      intro i
      cases i with
      | zero =>
        change NeutralTypeChange 0 ((proofErase Γ D).liftN 1) ((proofErase Γ D').liftN 1)
        rw [ED, ED']
        exact (HD.liftN (p := 0) (by omega)).mono (by omega)
      | succ i => exact .refl
    have RT := hctx hΓD Hcod.hasType.2 W HO
      (by simpa only [proofEraseCtx, EΓ, ED, EC''] using RC')
    simp only [proofEraseCtx, EΓ, ED', EC''] at RT
    exact ⟨_, .forallE RD' RT, .forallE HD' HC'⟩
  | app R S =>
    generalize E : ProofShape.app _ _ = source at H
    cases H with
    | refl => cases E; exact ⟨_, .app R S, .refl⟩
    | neutral hi hj =>
      obtain ⟨args', Eout, _⟩ := (E ▸ ScopedCompute.app R S).bvar_spine hhead
      exact ⟨_, .refl, Eout ▸ NeutralTypeChange.neutral hi hj⟩
    | forallE => cases E
  | proj R =>
    generalize E : ProofShape.proj _ _ _ = source at H
    cases H with
    | refl => cases E; exact ⟨_, .proj R, .refl⟩
    | neutral =>
      have HE := congrArg variableHead E
      simp only [variableHead, variableHead_mkApps] at HE
      cases HE
    | forallE => cases E
  | lam R S =>
    generalize E : ProofShape.lam _ _ = source at H
    cases H with
    | refl => cases E; exact ⟨_, .lam R S, .refl⟩
    | neutral =>
      have HE := congrArg variableHead E
      simp only [variableHead, variableHead_mkApps] at HE
      cases HE
    | forallE => cases E

end Lean4Lean.VEnv.Strengthening
