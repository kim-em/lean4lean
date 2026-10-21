import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralDomainGuard

/-! # Recursive neutral changes throughout Pi types

Both domains and codomains may change recursively. Changed neutral heads stay
outside the protected binder depth, so instantiation preserves the relation.
Unlike NeutralResultChange, this relation does not keep Pi domains exact.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private variableHead variableHead_mkApps
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- Recursive Pi structure with arbitrary changes at protected neutral leaves.
Identical subtrees may have any syntax. The relation is syntactic; using it
as type conversion additionally requires actual typed equality. -/
inductive NeutralTypeChange : Nat → ProofShape → ProofShape → Prop where
  | refl : NeutralTypeChange k A A
  | neutral (hi : k ≤ i) (hj : k ≤ j) :
      NeutralTypeChange k (mkApps (.bvar i) args) (mkApps (.bvar j) args')
  | forallE : NeutralTypeChange k A A' → NeutralTypeChange (k + 1) B B' →
      NeutralTypeChange k (.forallE A B) (.forallE A' B')

/-- Pi exposure retains recursive relations for both its domain and body. -/
theorem NeutralTypeChange.forallE_inv (H : NeutralTypeChange k (.forallE A B) T) :
    ∃ A' B', T = .forallE A' B' ∧ NeutralTypeChange k A A' ∧ NeutralTypeChange (k + 1) B B' := by
  generalize E : ProofShape.forallE A B = source at H
  cases H with
  | refl => exact ⟨A, B, E.symm, .refl, .refl⟩
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩

/-- Reversing a recursive neutral type change preserves its protected depth. -/
theorem NeutralTypeChange.symm (H : NeutralTypeChange k A B) : NeutralTypeChange k B A := by
  induction H with
  | refl => exact .refl
  | neutral hi hj => exact .neutral hj hi
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- A stronger depth restriction implies every weaker restriction. -/
theorem NeutralTypeChange.mono (H : NeutralTypeChange k A B) (hn : n ≤ k) : NeutralTypeChange n A B := by
  induction H generalizing n with
  | refl => exact .refl
  | neutral hi hj => exact .neutral (by omega) (by omega)
  | forallE _ _ ihA ihB => exact .forallE (ihA hn) (ihB (by omega))

private theorem NeutralTypeChange.sort (H : NeutralTypeChange k (.sort u) T) : T = .sort u := by
  generalize E : ProofShape.sort u = source at H
  cases H with
  | refl => rfl
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE => cases E

private theorem NeutralTypeChange.const_spine
    (H : NeutralTypeChange k (mkApps (.const c ls) args) T) :
    T = mkApps (.const c ls) args := by
  generalize E : mkApps (.const c ls) args = source at H
  cases H with
  | refl => rfl
  | neutral | forallE =>
    have HE := congrArg ProofShape.constHead E
    simp only [constHead_mkApps, ProofShape.constHead] at HE
    cases HE

/-- Inserting variables preserves the protected depth of changed heads. -/
theorem NeutralTypeChange.liftN (H : NeutralTypeChange k A B) (hp : p ≤ k) :
    NeutralTypeChange (k + n) (A.liftN n p) (B.liftN n p) := by
  induction H generalizing p with
  | refl => exact .refl
  | @neutral k i j args args' hi hj =>
    simp only [liftN_mkApps, ProofShape.liftN, liftVar, if_neg (show ¬ i < p by omega),
      if_neg (show ¬ j < p by omega)]
    exact .neutral (by omega) (by omega)
  | forallE HA HB ihA ihB =>
    exact .forallE (ihA hp) (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihB (p := p + 1) (by omega))

private theorem inst_mkApps (f : ProofShape) (args : List ProofShape) :
    (mkApps f args).inst x p = mkApps (f.inst x p) (args.map (fun a => a.inst x p)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

/-- Applying a recovered function cannot substitute for a changed neutral
head: that head lies outside the removed binder. This is why depth matters. -/
theorem NeutralTypeChange.inst (H : NeutralTypeChange (k + 1) A B) (hp : p ≤ k) :
    NeutralTypeChange k (A.inst x p) (B.inst x p) := by
  generalize hk : k + 1 = d at H
  induction H generalizing k p with
  | refl => exact .refl
  | @neutral d i j args args' hi hj =>
    simp only [inst_mkApps, ProofShape.inst, if_neg (show ¬ i < p by omega),
      if_neg (show ¬ j < p by omega), if_neg (show i ≠ p by omega), if_neg (show j ≠ p by omega)]
    exact .neutral (by omega) (by omega)
  | forallE HA HB ihA ihB =>
    exact .forallE (ihA hp hk) (ihB (k := k + 1) (p := p + 1) (by omega) (by omega))


variable [Params]

/-- Recursive neutral changes preserve structural subsingletons. Neutral
leaves cannot themselves carry a structural subsingleton certificate. -/
theorem NeutralTypeChange.subsingleton (H : NeutralTypeChange k A B)
    (HS : SubsingletonCarrier A) : SubsingletonCarrier B := by
  induction HS generalizing k B with
  | unit hi hx hf hp =>
    obtain rfl := H.const_spine
    exact .unit hi hx hf hp
  | forallE HS ih =>
    obtain ⟨A', B', rfl, _, HB⟩ := H.forallE_inv
    exact .forallE (ih HB)

/-- Computation of an actually typed source type is simulated at a convertible
type related by recursive neutral changes. Domain and body computations are
both retained, and actual Pi injectivity justifies changing the body context.
No computational join or general comparison-transport law is assumed. -/
theorem NeutralTypeChange.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : NeutralTypeChange k a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EA : proofErase Γ A = a) (EB : proofErase Γ B = b)
    (R : ScopedCompute Step (proofEraseCtx Γ) a out) :
    ∃ out', ScopedCompute Step (proofEraseCtx Γ) b out' ∧ NeutralTypeChange k out out' := by
  induction H generalizing Γ A B u out with
  | refl => exact ⟨_, R, .refl⟩
  | neutral hi hj =>
    obtain ⟨args', rfl, _⟩ := R.bvar_spine hhead
    exact ⟨_, .refl, .neutral hi hj⟩
  | forallE HD HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv EA
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv EB
    obtain ⟨⟨v, hD⟩, _, _⟩ := HAB.hasType.1.forallE_inv henv
    obtain ⟨⟨w, Hdom⟩, ⟨z, Hcod⟩⟩ := HAB.toU.forallE_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, v, hD⟩
    have hctx := IsDefEqCtx.succ .zero Hdom
    have EC'' := (proofErase_defeqCtx hΓD hctx Hcod.hasType.2).trans EC'
    obtain ⟨d, c, rfl, RD, RC⟩ := (ED ▸ R).forallE_inv_typed hstep hsubst hhead hΓ hD rfl
    obtain ⟨d', RD', HD'⟩ := ihD hΓ Hdom ED ED' (ED ▸ RD)
    have RC : ScopedCompute Step (proofEraseCtx (D :: Γ)) _ _ := RC
    obtain ⟨c', RC', HC'⟩ := ihC hΓD Hcod EC EC'' RC
    have RC'' := RC'.defeqCtx hsubst hΓ hctx
    simp only [proofEraseCtx, ED'] at RC''
    exact ⟨_, .forallE RD' RC'', .forallE HD' HC'⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
