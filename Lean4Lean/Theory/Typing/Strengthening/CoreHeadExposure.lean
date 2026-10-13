import Lean4Lean.Theory.Typing.Strengthening.OrdinaryIotaCoverage

/-! # Typed core computation in the head-exposure model

All concrete parallel core reductions embed in the finite observation model,
including recursive definitions and every enabled ordinary iota pattern. Source
typing is used to select the structure replay route, never strengthened.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions Compute)
open ConstructorObservation (EtaCompute)

/-- A concrete constant pattern is its actual stored definition equation. -/
theorem definition_compute {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    {captures : (Pattern.const c).Path → VExpr}
    (hp : ConcretePattern env (.const c) r)
    (hm : (Pattern.const c).Matches source levels captures)
    (ht : VExpr.WF env U Γ source) :
    Compute (Definitions.ofEnv env U henv) source (r.1.apply levels captures) := by
  rcases hp with hp | hp | hp
  · cases hp with
    | @intro value hlookup hclosed =>
      cases hm
      obtain ⟨constant, hconstant, hw, hl⟩ := ht.const_inv henv hΓ
      have hregistered := (definitionRegistry_registered hlookup).1
      cases Option.some.inj (hconstant.symm.trans hregistered.1)
      exact .delta ⟨value.toDefEq, levels, hregistered.2, hw, hl,
        by simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl], rfl⟩
  · cases hp
  · cases hp

/-- Every root pattern computation in the concrete core is represented in the
head model. Source typing determines all declaration and structure metadata. -/
theorem concrete_pattern_compute {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {p : Pattern} {r : p.RHS × p.Check}
    {captures : p.Path → VExpr}
    (hp : ConcretePattern env p r) (hm : p.Matches source levels captures)
    (hc : r.2.OK (env.IsDefEqU U Γ) levels captures)
    (ht : VExpr.WF env U Γ source) :
    @EtaCompute (henv.params U)
      (@ClosedStructure.definitions (henv.params U) (Definitions.ofEnv env U henv))
      source (r.1.apply levels captures) := by
  letI := henv.params U
  obtain ⟨s, rfl⟩ := hp.simple henv
  cases s with
  | defn c => exact .compute (.base (ClosedStructure.compute_base (definition_compute henv hΓ hp hm ht)))
  | iota recursor major ctor fields => exact ClosedStructure.concrete_iota_coverage henv hp hc hm hΓ ht

/-- Every typed parallel core step embeds, with all its parallel capture
computations. This includes all enabled concrete iota patterns. -/
theorem core_compute {env : VEnv} (henv : env.WF)
    (R : @ParRed (henv.params U) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ e) :
    @EtaCompute (henv.params U)
      (@ClosedStructure.definitions (henv.params U) (Definitions.ofEnv env U henv)) e out := by
  letI := henv.params U
  induction R with
  | bvar | sort | const => exact .compute (.base .refl)
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ ⟨_, hf⟩) (iha hΓ ⟨_, ha⟩)
  | lam _ _ ihA ihb =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩)) (ihb ⟨hΓ, hA⟩ hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨hA, hB⟩ := HasType.forallE_inv henv.ordered ht
    exact .forallE (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩))
      (ihB ⟨hΓ, hA⟩ (hB.elim fun _ h => ⟨_, h⟩))
  | proj _ ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := HasType.proj_inv henv hΓ ht
    exact .proj (ih hΓ ⟨_, hm.hasType.2⟩)
  | beta _ _ ihb iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨hA, hb⟩ := HasType.lam_inv henv hΓ hf
    exact (EtaCompute.app (.lam (.compute (.base .refl)) (ihb ⟨hΓ, hA⟩ hb))
      (iha hΓ ⟨_, ha⟩)).trans (.compute (.base .beta))
  | extra hp hm hc _ ih =>
    apply (concrete_pattern_compute henv hΓ hp hm hc ht).trans
    apply EtaCompute.apply_pat
    intro p
    obtain ⟨_, htyped⟩ := ht
    obtain ⟨_, hcap⟩ := HasType.matches_inv hΓ htyped hm p
    exact ih p hΓ ⟨_, hcap⟩

/-- Finite interleavings of actual parallel core reductions and parallel eta
expansions. Prefix unfolding and projection-iota are outside this fragment. -/
def CoreEtaTrace [Params] (Γ : List VExpr) : VExpr → VExpr → Prop :=
  ReflTransGen fun e out => ParRed Γ e out ∨ EtaPar Γ e out

/-- Typed finite core/eta interleavings preserve their source type and embed in
the head model; intermediate source typings follow by subject reduction. -/
theorem CoreEtaTrace.compute {env : VEnv} (henv : env.WF)
    (R : @CoreEtaTrace (henv.params U) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : env.HasType U Γ e T) :
    env.HasType U Γ out T ∧
    @EtaCompute (henv.params U)
      (@ClosedStructure.definitions (henv.params U) (Definitions.ofEnv env U henv)) e out := by
  letI := henv.params U
  induction R with
  | rfl => exact ⟨ht, .compute (.base .refl)⟩
  | tail _ h ih =>
    rcases h with h | h
    · exact ⟨h.hasType hΓ ih.1, ih.2.trans (core_compute henv h hΓ ⟨_, ih.1⟩)⟩
    · exact ⟨(h.full hΓ ih.1).hasType hΓ ih.1,
        ih.2.trans (EtaCompute.of_etaPar h hΓ ⟨_, ih.1⟩)⟩

/-- A function whose lifted type exposes a Pi by finite core/eta computation
already has a Pi type below. Eta annotations may mention the inserted binders;
the recovered computational path and its typing are constructed below. -/
theorem function_type_below_core_eta {env : VEnv} (henv : env.WF)
    (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hf : env.HasType U Γ f T)
    (R : @CoreEtaTrace (henv.params U) Γ' (T.liftN n k) (.forallE A B)) :
    ∃ A' B', env.HasType U Γ f (.forallE A' B') ∧
      env.IsDefEqU U Γ T (.forallE A' B') := by
  letI := henv.params U
  obtain ⟨u, hT⟩ := hf.isType henv.ordered hΓ
  have H := (R.compute henv hΓ' (hT.weakN henv.ordered W)).2
  rw [← lift'_consN_skipN] at H
  exact ClosedStructure.function_type_below_ofEnv hΓ hf H

end Lean4Lean.VEnv.Strengthening
