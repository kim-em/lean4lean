import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignment
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextOracleBeta

/-! # Recovery with changes confined to neutral terminal results

The depth index protects the changed neutral head from later application:
it is outside all displayed Pi binders. Recovery may change its result, but
every displayed function domain, sort, and registered-family result stays
exact. This is enough for consumers that only demand a function domain.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private variableHead variableHead_mkApps bvar_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private identity_cons
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointOracleBetaTransport

/-- Types may differ at a neutral terminal result whose head is outside `k`
binders. Displayed Pi domains stay identical, and increment the protected
depth. Reflexivity also permits unchanged types of every other shape. -/
inductive NeutralResultChange : Nat → ProofShape → ProofShape → Prop where
  | refl : NeutralResultChange k A A
  | neutral (hi : k ≤ i) (hj : k ≤ j) :
      NeutralResultChange k (mkApps (.bvar i) args) (mkApps (.bvar j) args')
  | forallE : NeutralResultChange (k + 1) B B' →
      NeutralResultChange k (.forallE A B) (.forallE A B')

/-- A changed recovered Pi keeps its domain literally, with only its codomain
related at the incremented protected depth. -/
theorem NeutralResultChange.forallE_inv (H : NeutralResultChange k (.forallE A B) T) :
    ∃ B', T = .forallE A B' ∧ NeutralResultChange (k + 1) B B' := by
  generalize E : ProofShape.forallE A B = source at H
  cases H with
  | refl => exact ⟨B, E.symm, .refl⟩
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE H => cases E; exact ⟨_, rfl, H⟩

private theorem NeutralResultChange.sort (H : NeutralResultChange k (.sort u) T) : T = .sort u := by
  generalize E : ProofShape.sort u = source at H
  cases H with
  | refl => rfl
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE => cases E

private theorem NeutralResultChange.const_spine
    (H : NeutralResultChange k (mkApps (.const c ls) args) T) :
    T = mkApps (.const c ls) args := by
  generalize E : mkApps (.const c ls) args = source at H
  cases H with
  | refl => rfl
  | neutral | forallE =>
    have HE := congrArg ProofShape.constHead E
    simp only [constHead_mkApps, ProofShape.constHead] at HE
    cases HE

/-- Inserting variables preserves the protected depth of changed heads. -/
theorem NeutralResultChange.liftN (H : NeutralResultChange k A B) (hp : p ≤ k) :
    NeutralResultChange (k + n) (A.liftN n p) (B.liftN n p) := by
  induction H generalizing p with
  | refl => exact .refl
  | @neutral k i j args args' hi hj =>
    simp only [liftN_mkApps, ProofShape.liftN, liftVar, if_neg (show ¬ i < p by omega),
      if_neg (show ¬ j < p by omega)]
    exact .neutral (by omega) (by omega)
  | forallE H ih =>
    exact .forallE (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (p := p + 1) (by omega))

private theorem inst_mkApps (f : ProofShape) (args : List ProofShape) :
    (mkApps f args).inst x p = mkApps (f.inst x p) (args.map (fun a => a.inst x p)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

/-- Applying a recovered function cannot substitute for a changed neutral
head: that head lies outside the removed binder. This is why depth matters. -/
theorem NeutralResultChange.inst (H : NeutralResultChange (k + 1) A B) (hp : p ≤ k) :
    NeutralResultChange k (A.inst x p) (B.inst x p) := by
  generalize hk : k + 1 = d at H
  induction H generalizing k p with
  | refl => exact .refl
  | @neutral d i j args args' hi hj =>
    simp only [inst_mkApps, ProofShape.inst, if_neg (show ¬ i < p by omega),
      if_neg (show ¬ j < p by omega), if_neg (show i ≠ p by omega), if_neg (show j ≠ p by omega)]
    exact .neutral (by omega) (by omega)
  | forallE H ih => exact .forallE (ih (k := k + 1) (p := p + 1) (by omega) (by omega))

private theorem NeutralResultChange.beta (H : NeutralResultChange k A B) (R : BetaRed A A') :
    ∃ B', BetaRed B B' ∧ NeutralResultChange k A' B' := by
  induction H generalizing A' with
  | refl => exact ⟨_, R, .refl⟩
  | neutral hi hj =>
    obtain ⟨args', rfl, _⟩ := R.bvar_spine
    exact ⟨_, .refl, .neutral hi hj⟩
  | forallE H ih =>
    obtain ⟨D', C', rfl, RD, RC⟩ := beta_forallE_parts R
    obtain ⟨B', RB, HB⟩ := ih RC
    exact ⟨_, .forallE RD RB, .forallE HB⟩

variable [Params]

private theorem compute_context
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : ContextSubstitution Δ Δ' Subst.id) (R : ScopedCompute Step Δ A B) :
    ScopedCompute Step Δ' A B := by
  simpa only [subst_id] using R.subst hsubst W

/-- Source computation can be simulated after a neutral-result change.
Target computation retains every source domain computation; changed neutral
arguments need no join or comparison. Interpreted context changes transport
primitive steps, and no confluence or normalization premise is used. -/
theorem NeutralResultChange.compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : NeutralResultChange k A B) (R : ScopedCompute Step Δ A A')
    (W : ContextSubstitution Δ Δ' Subst.id) :
    ∃ B', ScopedCompute Step Δ' B B' ∧ NeutralResultChange k A' B' := by
  induction R generalizing k B Δ' with
  | base R =>
    cases H with
    | refl => exact ⟨_, compute_context hsubst W (.base R), .refl⟩
    | neutral => exact (bvar_spine_not_primitive _ (hhead R)).elim
    | forallE => exact (hhead R).elim
  | beta R =>
    obtain ⟨B', RB, HB⟩ := H.beta R
    exact ⟨B', .beta RB, HB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨B₁, RB₁, HB₁⟩ := ih₁ H W
    obtain ⟨B₂, RB₂, HB₂⟩ := ih₂ HB₁ W
    exact ⟨B₂, RB₁.trans RB₂, HB₂⟩
  | forallE RA RC ihA ihC =>
    obtain ⟨B', rfl, HB⟩ := H.forallE_inv
    obtain ⟨B'', RB, HB'⟩ := ihC HB (identity_cons W)
    exact ⟨_, .forallE (compute_context hsubst W RA) RB, .forallE HB'⟩
  | app RA RB =>
    generalize E : ProofShape.app _ _ = source at H
    cases H with
    | refl => cases E; exact ⟨_, compute_context hsubst W (.app RA RB), .refl⟩
    | neutral hi hj =>
      obtain ⟨args', Eout, _⟩ := (E ▸ ScopedCompute.app RA RB).bvar_spine hhead
      exact ⟨_, .refl, Eout ▸ NeutralResultChange.neutral hi hj⟩
    | forallE => cases E
  | proj R =>
    generalize E : ProofShape.proj _ _ _ = source at H
    cases H with
    | refl =>
      cases E
      exact ⟨_, compute_context hsubst W (.proj R), .refl⟩
    | neutral =>
      have HE := congrArg variableHead E
      simp only [variableHead, variableHead_mkApps] at HE
      cases HE
    | forallE => cases E
  | lam RA R =>
    generalize E : ProofShape.lam _ _ = source at H
    cases H with
    | refl =>
      cases E
      exact ⟨_, compute_context hsubst W (.lam RA R), .refl⟩
    | neutral =>
      have HE := congrArg variableHead E
      simp only [variableHead, variableHead_mkApps] at HE
      cases HE
    | forallE => cases E

omit [Params] in
private theorem oracle_cons_change
    (HO : ∀ i, NeutralResultChange k (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, NeutralResultChange (k + 1) (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (HO i).liftN (by omega)

/-- Recovery survives interpreted changes to neutral oracle results. It may
choose a different output, but only at protected neutral terminal positions.
In particular, every recovered Pi retains its domain exactly. -/
theorem ScopedTypeRecovery.neutral_oracle
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step Δ e T)
    (W : ContextSubstitution Δ Δ' Subst.id)
    (HO : ∀ i, NeutralResultChange k (contextOracle Δ i) (contextOracle Δ' i)) :
    ∃ T', ScopedTypeRecovery Step Δ' e T' ∧ NeutralResultChange k T T' := by
  induction R generalizing Δ' k with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hl => exact ⟨_, .const hc hw hl, .refl⟩
  | lam R ih =>
    obtain ⟨T', R', HT⟩ := ih (identity_cons W) (oracle_cons_change HO)
    exact ⟨_, .lam R', .forallE HT⟩
  | app R ih =>
    obtain ⟨T', R', HT⟩ := ih W HO
    obtain ⟨B', rfl, HB⟩ := HT.forallE_inv
    exact ⟨_, .app R', HB.inst (by omega)⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨T', RA', HA⟩ := ihA W HO
    obtain rfl := HA.sort
    obtain ⟨T', RB', HB⟩ := ihB (identity_cons W) (oracle_cons_change HO)
    obtain rfl := HB.sort
    exact ⟨_, .forallE RA' RB', .refl⟩
  | proj hi HT hj hlen R ih =>
    obtain ⟨T', R', HR⟩ := ih W HO
    obtain rfl := HR.const_spine
    exact ⟨_, .proj hi HT hj hlen R', .refl⟩
  | convert R RC ih =>
    obtain ⟨T', R', HT⟩ := ih W HO
    obtain ⟨T'', RC', HT'⟩ := HT.compute hhead hsubst RC W
    exact ⟨T'', .convert R' RC', HT'⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
