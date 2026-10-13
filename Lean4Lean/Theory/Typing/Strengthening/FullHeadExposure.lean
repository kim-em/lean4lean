import Lean4Lean.Theory.Typing.Strengthening.CoreHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.SingletonHeadComputation

/-! # Full typed head exposure, with indexed prefixes isolated

Every actual computation and eta rule is covered except indexed singleton-prefix
replay. The remaining hypothesis names exactly those registered prefix steps;
it does not assume arbitrary conversion, head exposure, or strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions Compute ProjectionCompute)
open ConstructorObservation (EtaCompute ConstructorRigid)

/-- Adding closed equations preserves finite computation. -/
theorem PureObservation.Compute.of_inclusion (inc : ∀ c ls rhs, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : Compute D e out) : Compute D' e out := by
  induction R with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .beta
  | delta h => exact .delta (inc _ _ _ h)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Adding closed equations also preserves projection computation. -/
theorem PureObservation.ProjectionCompute.of_inclusion [Params]
    (inc : ∀ c ls rhs, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : ProjectionCompute D e out) : ProjectionCompute D' e out := by
  induction R with
  | base h => exact .base (h.of_inclusion inc)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | projIota hi hl hg => exact .projIota hi hl hg
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- The finite mixed paths are monotone in their closed equation collection. -/
theorem ConstructorObservation.EtaCompute.of_inclusion [Params]
    (inc : ∀ c ls rhs, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : EtaCompute D e out) : EtaCompute D' e out := by
  induction R with
  | compute h => exact .compute (h.of_inclusion inc)
  | iota hp hc hm hn => exact .iota hp hc hm hn
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | funEta => exact .funEta
  | structEta hi hz ha hp => exact .structEta hi hz ha hp
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

namespace FullHead
variable {env : VEnv}

/-- Include quotient equations exactly when their primitive declarations are
registered; environments without Quot need no additional assumption. -/
noncomputable def quotDefinitions (env : VEnv) (U : Nat) (henv : env.WF) : Definitions := by
  classical
  exact if hq : QuotRegistered env then ClosedQuot.definitions env U henv hq
  else Definitions.ofEnv env U henv

/-- All stored constant equations are retained. -/
theorem quot_base (henv : env.WF) :
    ∀ c ls rhs, (Definitions.ofEnv env U henv).unfolds c ls rhs →
      (quotDefinitions env U henv).unfolds c ls rhs := by
  intro c ls rhs h
  unfold quotDefinitions
  split
  · exact .inl h
  · exact h

theorem quot_sound (henv : env.WF) : (quotDefinitions env U henv).Sound env U := by
  unfold quotDefinitions
  split
  · exact ClosedQuot.definitions_sound henv _
  · exact Definitions.ofEnv_sound henv

theorem quot_rigid [Params] : ConstructorRigid (quotDefinitions Params.env Params.univs Params.henv) := by
  unfold quotDefinitions
  split
  · exact ClosedQuot.definitions_rigid _
  · exact ConstructorRigid.ofEnv

/-- The complete sound closed equation collection currently available. -/
noncomputable def definitions {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) : Definitions :=
  @ClosedSingleton.definitions (henv.params U) heq
    (@ClosedStructure.definitions (henv.params U) (quotDefinitions env U henv))

theorem sound (henv : env.WF) (heq : env.HasCanonicalEq) :
    (definitions henv heq U).Sound env U := by
  letI := henv.params U
  exact ClosedSingleton.definitions_sound heq (ClosedStructure.definitions_sound (quot_sound henv))

theorem rigid (henv : env.WF) (heq : env.HasCanonicalEq) :
    @ConstructorRigid (henv.params U) (definitions henv heq U) := by
  letI := henv.params U
  exact ClosedSingleton.definitions_rigid heq (ClosedStructure.definitions_rigid quot_rigid)

/-- The earlier complete core simulation embeds in the full closed collection. -/
theorem core (henv : env.WF) (heq : env.HasCanonicalEq)
    (R : @ParRed (henv.params U) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ e) :
    @EtaCompute (henv.params U) (definitions henv heq U) e out := by
  letI := henv.params U
  apply ClosedSingleton.etaCompute_base heq
  apply (core_compute henv R hΓ ht).of_inclusion
  intro c ls rhs h
  rcases h with h | h
  · exact .inl (quot_base henv _ _ _ h)
  · exact .inr h

/-- Primitive quotient prefixes are included without any global Quot assumption. -/
theorem quotient (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : QuotPrefixUnfold env U Γ levels args rhs) :
    @EtaCompute (henv.params U) (definitions henv heq U)
      (mkApps (.const ``Quot.lift levels) args) rhs := by
  letI := henv.params U
  apply ClosedSingleton.etaCompute_base heq
  apply ClosedStructure.etaCompute_base
  apply EtaCompute.compute
  apply ProjectionCompute.base
  have hq := H.registered
  simp only [quotDefinitions, dif_pos hq]
  exact ClosedQuot.prefix_compute henv hq H

/-- Unindexed singleton prefixes are included using their closed equations. -/
theorem unindexed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hl : env.recursorRegistry name = some data) (hn : data.numIndices = 0)
    (H : PrefixUnfold env U env.recursorRegistry Γ name levels args rhs) :
    @EtaCompute (henv.params U) (definitions henv heq U)
      (mkApps (.const name levels) args) rhs := by
  letI := henv.params U
  exact ClosedSingleton.prefix_etaCompute heq hl hn H

/-- Missing indexed-prefix obligation: simulate each actual checked singleton
prefix at a registered recursor with at least one index in the sound finite head
model. All ordinary iota, unindexed prefixes, quotient prefixes, and etas are
proved separately. This hypothesis is not claimed smaller than PropFront. -/
def IndexedPrefixReplay {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) : Prop :=
  ∀ Γ name levels args rhs data, env.recursorRegistry name = some data → data.numIndices ≠ 0 →
    OnCtx Γ (env.IsType U) →
    PrefixUnfold env U env.recursorRegistry Γ name levels args rhs →
    @EtaCompute (henv.params U) (definitions henv heq U)
      (mkApps (.const name levels) args) rhs

/-- The full-step bridge has only the indexed-prefix replay gap above. In
particular, projection-iota arity and eta admissibility follow from actual typing. -/
theorem step_of_indexed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hindexed : IndexedPrefixReplay henv heq U)
    (R : @FullStep (henv.params U) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ e) :
    @EtaCompute (henv.params U) (definitions henv heq U) e out := by
  letI := henv.params U
  induction R with
  | core h => exact core henv heq h hΓ ht
  | delta h =>
    have hcopy := h
    cases h with
    | @intro data program hl hr hn hlarge hw hz hg hc =>
      by_cases hi : data.numIndices = 0
      · exact unindexed henv heq hl hi hcopy
      · exact hindexed _ _ _ _ _ _ hl hi hΓ hcopy
  | quotDelta h => exact quotient henv heq h
  | projIota hi hs hg _ =>
    obtain ⟨info', _, _, _, _, _, _, hi', _, _, _, _, _, _, hm, _, _⟩ := HasType.proj_inv henv hΓ hs
    obtain rfl := henv.ordered.projections_unique hi hi'
    have ha := (projection_major_family henv hΓ hi (henv.projectionRigid hi) hm.hasType.2).2
    exact .compute (.projIota hi ha hg)
  | structEta hi hp hz hm he =>
    exact .structEta hi hz ((StructureReplay.expansion_typed_iff henv hΓ hi hp hz hm).1 he) hp
  | funEta => exact .funEta
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ ⟨_, hf⟩) (iha hΓ ⟨_, ha⟩)
  | proj _ ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := HasType.proj_inv henv hΓ ht
    exact .proj (ih hΓ ⟨_, hm.hasType.2⟩)
  | lam _ _ ihA ihb =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩)) (ihb ⟨hΓ, hA⟩ hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨hA, hB⟩ := HasType.forallE_inv henv.ordered ht
    exact .forallE (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩))
      (ihB ⟨hΓ, hA⟩ (hB.elim fun _ h => ⟨_, h⟩))

/-- Arbitrary finite full reductions embed once indexed singleton-prefix replay
is supplied. Intermediate typings follow by full subject reduction. -/
theorem reduction_of_indexed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hindexed : IndexedPrefixReplay henv heq U)
    (R : @FullReduction (henv.params U) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : env.HasType U Γ e T) :
    env.HasType U Γ out T ∧ @EtaCompute (henv.params U) (definitions henv heq U) e out := by
  letI := henv.params U
  induction R with
  | rfl => exact ⟨ht, .compute (.base .refl)⟩
  | tail _ h ih => exact ⟨h.hasType hΓ ih.1,
      ih.2.trans (step_of_indexed henv heq hindexed h hΓ ⟨_, ih.1⟩)⟩

/-- Full computational Pi exposure lowers through arbitrary context insertion,
conditional only on the indexed-prefix replay obligation for this head model. -/
theorem function_type_below_of_indexed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hindexed : IndexedPrefixReplay henv heq U) (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hf : env.HasType U Γ f T)
    (R : @FullReduction (henv.params U) Γ' (T.liftN n k) (.forallE A B)) :
    ∃ A' B', env.HasType U Γ f (.forallE A' B') ∧ env.IsDefEqU U Γ T (.forallE A' B') := by
  letI := henv.params U
  obtain ⟨_, hT⟩ := hf.isType henv.ordered hΓ
  have H := (reduction_of_indexed henv heq hindexed R hΓ' (hT.weakN henv.ordered W)).2
  rw [← lift'_consN_skipN] at H
  exact H.function_type_below (rigid henv heq) (sound henv heq) hΓ hf

end FullHead
end Lean4Lean.VEnv.Strengthening
