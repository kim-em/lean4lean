import Lean4Lean.Theory.Typing.Strengthening.ClosedSingletonUnfolding
import Lean4Lean.Theory.Typing.Strengthening.OrdinaryIotaCoverage

/-! # Closed singleton prefixes in computational head exposure

Unindexed Prop-source singleton prefixes are one closed constant unfolding
followed by beta computation. The entire preceding mixed head model embeds in
this extension; occurrence-specific extraction and alignment checks need not be
strengthened.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation (Definitions Compute ProjectionCompute)
variable [Params] {D : Definitions}

/-- Registration data and a generated closed singleton program. -/
inductive Unfolds : Name → List VLevel → VExpr → Prop where
  | intro : RecursorRegistered env data → data.largeTarget = true →
      data.sourceLevel levels ≈ .zero → (∀ l ∈ levels, l.WF univs) → levels.length = data.uvars →
      data.singletonUnfolding env univs levels [] = some program → data.numIndices = 0 →
      Unfolds data.name levels program.rhs

theorem Unfolds.equation (heq : env.HasCanonicalEq) (H : Unfolds name levels rhs) :
    env.IsDefEqU univs [] (.const name levels) rhs := by
  cases H with
  | intro hr hl hz hw hn hg hi => exact zero_equation henv heq hr hl hz hw hn hg hi

/-- Add every proved unindexed singleton equation to the preceding definitions. -/
def definitions (heq : env.HasCanonicalEq) (D : Definitions) : Definitions where
  unfolds name levels rhs := D.unfolds name levels rhs ∨ Unfolds name levels rhs
  closed := by
    rintro name levels rhs (h | h)
    · exact D.closed h
    · obtain ⟨_, he⟩ := h.equation heq
      exact he.hasType.2.closedN henv.ordered (by trivial)

theorem definitions_sound (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    (definitions heq D).Sound env univs := by
  rintro Γ name levels rhs (h | h)
  · exact hs Γ name levels rhs h
  · obtain ⟨_, he⟩ := h.equation heq
    exact ⟨_, he.weak0 henv.ordered⟩

/-- The actual stored iota rule excludes a projection constructor at this head. -/
theorem Unfolds.not_constructor (H : Unfolds name levels rhs)
    (hi : env.projections s info) : info.ctorName ≠ name := by
  cases H with
  | intro hr _ _ _ _ hg _ =>
    intro he
    obtain ⟨_, _, _, _, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨r, ru, hc, hof, hp⟩ := hr.singletonEquation hseq
    obtain ⟨index, howner, hgen⟩ := RecursorData.singletonEquation_eq hseq
    have hhead := hr.equation_head howner hgen
    have hname := hof.2.1
    rw [lamBody_eq_stripLams, VExpr.headConst?_eq_some] at hname
    obtain ⟨us, hname⟩ := hname
    rw [VExpr.getAppFn_eq_fst, hhead] at hname
    have hrname := (VExpr.const.inj hname).1.symm
    exact (henv.projectionCtorRigid hi).pats _ _ hp (by rw [SimplePattern.iota_headConst, hrname, he])

theorem definitions_rigid (heq : env.HasCanonicalEq)
    (hD : ConstructorObservation.ConstructorRigid D) :
    ConstructorObservation.ConstructorRigid (definitions heq D) := by
  rintro s info hi levels rhs (h | h)
  · exact hD s info hi levels rhs h
  · exact h.not_constructor hi rfl

/-- Earlier closed computations remain available. -/
theorem compute_base (heq : env.HasCanonicalEq) (H : Compute D e out) :
    Compute (definitions heq D) e out := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .beta
  | delta hd => exact .delta (.inl hd)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

theorem projection_base (heq : env.HasCanonicalEq) (H : ProjectionCompute D e out) :
    ProjectionCompute (definitions heq D) e out := by
  induction H with
  | base h => exact .base (compute_base heq h)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | projIota hi hl hg => exact .projIota hi hl hg
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Preserve every earlier mixed path, including both etas, ordinary iota,
structure unfoldings and quotient prefixes already included in the base. -/
theorem etaCompute_base (heq : env.HasCanonicalEq) (H : ConstructorObservation.EtaCompute D e out) :
    ConstructorObservation.EtaCompute (definitions heq D) e out := by
  induction H with
  | compute h => exact .compute (projection_base heq h)
  | iota hp hc hm hn => exact .iota hp hc hm hn
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | funEta => exact .funEta
  | structEta hi hz ha hp => exact .structEta hi hz ha hp
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Every generated unindexed prefix is simulated on arbitrary raw arguments.
No source typing or occurrence-specific unfolding check is used. -/
theorem generated_compute (heq : env.HasCanonicalEq) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hg : data.singletonUnfolding env univs levels args = some program) (hn : data.numIndices = 0) :
    Compute (definitions heq D) (mkApps (.const data.name levels) args) program.rhs := by
  obtain ⟨_, _, hlv, hlen, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
  rw [hlv] at hlen
  have hnlevels := hlen.trans (RecursorData.singletonEquation_uvars hseq)
  obtain ⟨zero, hg0⟩ := RecursorData.singletonUnfolding_anyArity hg (args' := []) (by simp)
  have hc : Compute (definitions heq D) (.const data.name levels) zero.rhs :=
    .delta (.inr (.intro H hlarge hzero hw hnlevels hg0 hn))
  exact (ClosedQuot.compute_mkApps hc args).trans
    (.of_beta (generated_prefix_beta henv H hlarge hzero hg0 hg))

/-- A checked prefix in any context embeds after selecting its unindexed registry
entry. Its ambient reconstruction checks play no role in the raw simulation. -/
theorem prefix_compute (heq : env.HasCanonicalEq)
    (hlookup : registry name = some data) (hn : data.numIndices = 0)
    (H : PrefixUnfold env univs registry Γ name levels args rhs) :
    Compute (definitions heq D) (mkApps (.const name levels) args) rhs := by
  cases H with
  | intro hl hr hname hlarge hw hz hg _ =>
    cases Option.some.inj (hl.symm.trans hlookup)
    subst hname
    exact generated_compute heq hr hlarge hz hw hg hn

/-- Lower a checked unindexed singleton prefix using only source typing below. -/
theorem prefix_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hlookup : registry name = some data) (hn : data.numIndices = 0)
    (H : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ (mkApps (.const name levels) args) T) :
    ∃ rhs₀, rhs = rhs₀.lift' ρ ∧ IsDefEq env univs Γ (mkApps (.const name levels) args) rhs₀ T := by
  have R := prefix_compute (D := D) heq hlookup hn H
  have R' : Compute (definitions heq D) ((mkApps (.const name levels) args).lift' ρ) rhs := by
    simpa only [VExpr.lift'_mkApps, VExpr.lift'] using R
  obtain ⟨rhs₀, R0, he⟩ := R'.lift_inv
  exact ⟨rhs₀, he, R0.simAt henv (definitions_sound heq hs) hΓ T ht⟩

/-- Reflect this prefix rule when both endpoints are supplied below the lift. -/
theorem prefix_reflect (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hlookup : registry name = some data) (hn : data.numIndices = 0)
    (H : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) (rhs.lift' ρ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ (mkApps (.const name levels) args) T) :
    IsDefEq env univs Γ (mkApps (.const name levels) args) rhs T := by
  obtain ⟨rhs₀, he, h⟩ := prefix_descend heq hs hlookup hn H hΓ ht
  cases VExpr.lift'_inj.1 he
  exact h

/-- Actual prefix computation is available inside the mixed head model. -/
theorem prefix_etaCompute (heq : env.HasCanonicalEq)
    (hlookup : registry name = some data) (hn : data.numIndices = 0)
    (H : PrefixUnfold env univs registry Γ name levels args rhs) :
    ConstructorObservation.EtaCompute (definitions heq D) (mkApps (.const name levels) args) rhs :=
  .compute (.base (prefix_compute heq hlookup hn H))

/-- Head-type reconstruction now includes these singleton prefixes. -/
theorem function_type_below (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ConstructorObservation.ConstructorRigid D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions heq D) (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  R.function_type_below (definitions_rigid heq hD) (definitions_sound heq hs) hΓ hf

/-- Environment declarations discharge the closed-definition assumptions. -/
theorem function_type_below_ofEnv (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions heq (Definitions.ofEnv env univs henv))
      (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  function_type_below heq (Definitions.ofEnv_sound henv) ConstructorObservation.ConstructorRigid.ofEnv hΓ hf R

/-- Retain all covered structure-iota equations in the singleton extension. -/
theorem function_type_below_structures (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ConstructorObservation.ConstructorRigid D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions heq (ClosedStructure.definitions D))
      (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  function_type_below heq (ClosedStructure.definitions_sound hs) (ClosedStructure.definitions_rigid hD) hΓ hf R

/-- Combined head exposure includes stored equations, both etas, non-structure
iota, covered structure iota, every quotient prefix, and every unindexed singleton prefix. -/
theorem function_type_below_quot_structures (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute
      (definitions heq (ClosedStructure.definitions (ClosedQuot.definitions env univs henv hq)))
      (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  function_type_below_structures heq (ClosedQuot.definitions_sound henv hq)
    (ClosedQuot.definitions_rigid hq) hΓ hf R

/-- Exact prefix reflection with all definition assumptions discharged. -/
theorem prefix_reflect_ofEnv (heq : env.HasCanonicalEq)
    (hlookup : registry name = some data) (hn : data.numIndices = 0)
    (H : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) (rhs.lift' ρ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ (mkApps (.const name levels) args) T) :
    IsDefEq env univs Γ (mkApps (.const name levels) args) rhs T :=
  prefix_reflect heq (Definitions.ofEnv_sound henv) hlookup hn H hΓ ht

end Lean4Lean.VEnv.Strengthening.ClosedSingleton
