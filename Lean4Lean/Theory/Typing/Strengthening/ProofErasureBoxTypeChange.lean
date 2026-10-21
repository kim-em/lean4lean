import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxGuard

/-! # Recursive type changes through Pi and registered Box structure

A single registered Box may occur at arbitrary depth among Pi types. Its
parameter changes recursively, so projection recovery can expose the changed
field type instead of requiring an identical recovered record carrier.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private variableHead variableHead_mkApps
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
open private erase_app_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

open private erase_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private BoxCarrierAlignment.family_typed BoxCarrierAlignment.projection_recipe
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment

/-- Recursive Pi and Box structure with changes at protected neutral leaves.
Identical subtrees may have any syntax. The relation is syntactic; using it
as type conversion additionally requires actual typed equality. -/
inductive BoxTypeChange (family : Name) : Nat → ProofShape → ProofShape → Prop where
  | refl : BoxTypeChange family k A A
  | neutral (hi : k ≤ i) (hj : k ≤ j) :
      BoxTypeChange family k (mkApps (.bvar i) args) (mkApps (.bvar j) args')
  | forallE : BoxTypeChange family k A A' → BoxTypeChange family (k + 1) B B' →
      BoxTypeChange family k (.forallE A B) (.forallE A' B')
  | box : BoxTypeChange family k A B →
      BoxTypeChange family k (.app (.const family []) A) (.app (.const family []) B)

/-- The preceding recursive Pi/neutral fragment embeds without changing its
protected depth. Box closure adds new cases rather than replacing that fragment. -/
theorem NeutralTypeChange.toBox (H : NeutralTypeChange k A B) : BoxTypeChange family k A B := by
  induction H with
  | refl => exact .refl
  | neutral hi hj => exact .neutral hi hj
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- Pi exposure retains recursive relations for both its domain and body. -/
theorem BoxTypeChange.forallE_inv (H : BoxTypeChange family k (.forallE A B) T) :
    ∃ A' B', T = .forallE A' B' ∧ BoxTypeChange family k A A' ∧ BoxTypeChange family (k + 1) B B' := by
  generalize E : ProofShape.forallE A B = source at H
  cases H with
  | refl => exact ⟨A, B, E.symm, .refl, .refl⟩
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩
  | box => cases E

/-- Reversing a recursive Pi/Box type change preserves its protected depth. -/
theorem BoxTypeChange.symm (H : BoxTypeChange family k A B) : BoxTypeChange family k B A := by
  induction H with
  | refl => exact .refl
  | neutral hi hj => exact .neutral hj hi
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | box _ ih => exact .box ih

/-- A stronger depth restriction implies every weaker restriction. -/
theorem BoxTypeChange.mono (H : BoxTypeChange family k A B) (hn : n ≤ k) : BoxTypeChange family n A B := by
  induction H generalizing n with
  | refl => exact .refl
  | neutral hi hj => exact .neutral (by omega) (by omega)
  | forallE _ _ ihA ihB => exact .forallE (ihA hn) (ihB (by omega))
  | box _ ih => exact .box (ih hn)

private theorem BoxTypeChange.sort (H : BoxTypeChange family k (.sort u) T) : T = .sort u := by
  generalize E : ProofShape.sort u = source at H
  cases H with
  | refl => rfl
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE | box => cases E

/-- A rigid spine is unchanged unless it is precisely the selected Box. -/
theorem BoxTypeChange.const_spine
    (H : BoxTypeChange family k (mkApps (.const c ls) args) T) :
    T = mkApps (.const c ls) args ∨
      ∃ a b, c = family ∧ ls = [] ∧ args = [a] ∧
        T = .app (.const family []) b ∧ BoxTypeChange family k a b := by
  generalize E : mkApps (.const c ls) args = source at H
  cases H with
  | refl => exact .inl rfl
  | neutral | forallE =>
    have HE := congrArg ProofShape.constHead E
    simp only [constHead_mkApps, ProofShape.constHead] at HE
    cases HE
  | box H =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_inj
      (show mkApps (.const c ls) args = mkApps (.const family []) [_] from E)
    exact .inr ⟨_, _, rfl, rfl, rfl, rfl, H⟩

/-- Inserting variables preserves the protected depth of changed heads. -/
theorem BoxTypeChange.liftN (H : BoxTypeChange family k A B) (hp : p ≤ k) :
    BoxTypeChange family (k + n) (A.liftN n p) (B.liftN n p) := by
  induction H generalizing p with
  | refl => exact .refl
  | @neutral k i j args args' hi hj =>
    simp only [liftN_mkApps, ProofShape.liftN, liftVar, if_neg (show ¬ i < p by omega),
      if_neg (show ¬ j < p by omega)]
    exact .neutral (by omega) (by omega)
  | forallE HA HB ihA ihB =>
    exact .forallE (ihA hp) (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihB (p := p + 1) (by omega))
  | box _ ih => exact .box (ih hp)

private theorem inst_mkApps (f : ProofShape) (args : List ProofShape) :
    (mkApps f args).inst x p = mkApps (f.inst x p) (args.map (fun a => a.inst x p)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

/-- Applying a recovered function cannot substitute for a changed neutral
head: that head lies outside the removed binder. This is why depth matters. -/
theorem BoxTypeChange.inst (H : BoxTypeChange family (k + 1) A B) (hp : p ≤ k) :
    BoxTypeChange family k (A.inst x p) (B.inst x p) := by
  generalize hk : k + 1 = d at H
  induction H generalizing k p with
  | refl => exact .refl
  | @neutral d i j args args' hi hj =>
    simp only [inst_mkApps, ProofShape.inst, if_neg (show ¬ i < p by omega),
      if_neg (show ¬ j < p by omega), if_neg (show i ≠ p by omega), if_neg (show j ≠ p by omega)]
    exact .neutral (by omega) (by omega)
  | forallE HA HB ihA ihB =>
    exact .forallE (ihA hp hk) (ihB (k := k + 1) (p := p + 1) (by omega) (by omega))
  | box _ ih => exact .box (ih hp hk)


variable [Params]

/-- A literal erased Box type determines an actual parameter typed at Type.
The native family signature, rather than assumed argument typing, fixes its sort. -/
theorem box_type_inv
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (ET : proofErase Γ T = .app (.const family []) a) :
    ∃ A, T = .app (.const family []) A ∧ proofErase Γ A = a ∧
      env.HasType univs Γ A (.sort (.succ .zero)) := by
  obtain ⟨f, A, rfl, _, Ef, EA⟩ := erase_app_inv ET
  obtain rfl := erase_const_inv Ef
  obtain ⟨_, _, hf, hA⟩ := hT.app_inv henv hΓ
  exact ⟨A, rfl, EA, argument_at_displayed_domain hΓ hf
    (BoxCarrierAlignment.family_typed hc) hA⟩

/-- Recursive Pi/Box changes preserve structural subsingletons. Neutral
leaves and the nonempty Box cannot carry a unit certificate. -/
theorem BoxTypeChange.subsingleton
    (hiBox : env.projections family infoBox) (hfBox : infoBox.numFields = 1) (H : BoxTypeChange family k A B)
    (HS : SubsingletonCarrier A) : SubsingletonCarrier B := by
  induction HS generalizing k B with
  | unit hi hx hf hp =>
    rcases H.const_spine with E | ⟨a, b, rfl, rfl, rfl, rfl, _⟩
    · rw [E]; exact .unit hi hx hf hp
    · cases henv.ordered.projections_unique hi hiBox
      omega
  | forallE HS ih =>
    obtain ⟨A', B', rfl, _, HB⟩ := H.forallE_inv
    exact .forallE (ih HB)

/-- Every recovered record retains its family and arity, while all selected
field recipes remain related. For the chosen Box the sole field is its
parameter; other registered records retain their parameters literally. -/
theorem BoxTypeChange.projection_recipes
    (hiBox : env.projections family infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hi : env.projections c info) (HT : ProjTele env univs c info ls doms result)
    (H : BoxTypeChange family k (mkApps (.const c ls) ps) target) :
    ∃ ps', target = mkApps (.const c ls) ps' ∧ ps'.length = ps.length ∧
      ∀ j (hj : info.nparams + j < doms.length) major,
        BoxTypeChange family k (projectionType c info doms j hj ps major)
          (projectionType c info doms j hj ps' major) := by
  rcases H.const_spine with E | ⟨a, b, rfl, rfl, rfl, rfl, HP⟩
  · exact ⟨ps, E, rfl, fun _ _ _ => .refl⟩
  · cases henv.ordered.projections_unique hi hiBox
    refine ⟨[b], rfl, rfl, ?_⟩
    intro j hj major
    have hj0 : j = 0 := by have := HT.numFields; omega
    subst j
    simpa only [BoxCarrierAlignment.projection_recipe hpBox hfBox hshapeBox HT] using HP

/-- Computation of an actually typed source type is simulated at a convertible
type related by recursive Pi/Box changes. Domain and body computations are
both retained, and actual Pi injectivity justifies changing the body context.
Rigid-family injectivity supplies equality of Box parameters. No computational
join or general comparison-transport law is assumed. -/
theorem BoxTypeChange.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hiBox : env.projections family infoBox)
    (hcBox : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out)
    (H : BoxTypeChange family k a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EA : proofErase Γ A = a) (EB : proofErase Γ B = b)
    (R : ScopedCompute Step (proofEraseCtx Γ) a out) :
    ∃ out', ScopedCompute Step (proofEraseCtx Γ) b out' ∧ BoxTypeChange family k out out' := by
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

  | box HP ih =>
    obtain ⟨X, rfl, EX, hX⟩ := box_type_inv hcBox hΓ HAB.hasType.1 EA
    obtain ⟨Y, rfl, EY, hY⟩ := box_type_inv hcBox hΓ HAB.hasType.2 EB
    have Hargs := (IsDefEqU.structApp_inv henv hΓ hiBox
      (args := [X]) (args' := [Y]) HAB.toU HAB.hasType.1).2
    cases Hargs with
    | cons HXY _ =>
      have HXY := HXY.of_l henv hΓ hX
      obtain ⟨ps, Eout, RP⟩ := (show ScopedCompute Step _
        (mkApps (.const family []) [_]) out from R).const_spine hinert
      cases RP with
      | cons RX RT =>
        cases RT
        obtain ⟨y', RY, HP'⟩ := ih hΓ HXY EX EY RX
        exact ⟨_, .app .refl RY, Eout ▸ BoxTypeChange.box HP'⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
