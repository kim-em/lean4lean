import Lean4Lean.Theory.Typing.Strengthening.ClosedStructureUnfolding
import Lean4Lean.Theory.Typing.Strengthening.ConstructorHeadExposure

/-! # Replaying closed structure unfoldings in the head model

The augmented declaration collection retains all prior equations and adds the
proved projection unfoldings of registered unindexed structure recursors at
never-zero source universes or proof-valued fields. Occurrence replay uses only the closed equation.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation (Definitions Compute ProjectionCompute CheckFromTyping)
variable [Params]

/-- Registry, universe, and field-admissibility data enabling a closed structure equation. -/
inductive Unfolds : Name → List VLevel → VExpr → Prop where
  | intro {r : (pattern data info).RHS × (pattern data info).Check} :
      RecursorRegistered env data → (∀ l ∈ levels, l.WF univs) → levels.length = data.uvars →
      env.projections (family data) info → info.nindices = 0 →
      Admissible env univs data info levels →
      Pat _ r → CheckFromTyping env univs _ r levels →
      Unfolds data.name levels (value data info levels r.1 (domainsOf data levels))

/-- Each enabled unfolding is a proved closed equation. -/
theorem Unfolds.equation (H : Unfolds name levels rhs) :
    IsDefEqU env univs [] (.const name levels) rhs := by
  cases H with
  | intro hr hw hl hi hn hz hp hc => exact canonical_equation hr hw hl hi hn hz hp hc

/-- Add these equations to any existing collection of closed definitions. -/
def definitions (D : Definitions) : Definitions where
  unfolds name levels rhs := D.unfolds name levels rhs ∨ Unfolds name levels rhs
  closed := by
    rintro name levels rhs (h | h)
    · exact D.closed h
    · obtain ⟨_, he⟩ := h.equation
      exact he.hasType.2.closedN henv.ordered (by trivial)

/-- Soundness of the augmented collection is ordinary weakening of the closed
proof, with no strengthening or occurrence-specific reconstruction premises. -/
theorem definitions_sound (hs : D.Sound env univs) : (definitions D).Sound env univs := by
  rintro Γ name levels rhs (h | h)
  · exact hs Γ name levels rhs h
  · obtain ⟨_, he⟩ := h.equation
    exact ⟨_, he.weak0 henv.ordered⟩

/-- A recursor with one of these rules cannot also be a projection constructor. -/
theorem Unfolds.not_constructor (H : Unfolds name levels rhs)
    (hi : env.projections s info) : info.ctorName ≠ name := by
  cases H with
  | intro _ _ _ _ _ _ hp _ =>
    intro he
    exact (henv.projectionCtorRigid hi).not_patternHeadsStoredRule (pat_storedRule hp)
      (by simp [pattern, Pattern.constHead_eq, Pattern.headConst, Pattern.headConst_varN, he])

/-- The constructor rigidity needed by backwards structure eta is preserved. -/
theorem definitions_rigid (hD : ConstructorObservation.ConstructorRigid D) :
    ConstructorObservation.ConstructorRigid (definitions D) := by
  rintro s info hi levels rhs (h | h)
  · exact hD s info hi levels rhs h
  · exact h.not_constructor hi rfl

/-- Earlier constant equations remain available. -/
theorem compute_base (H : Compute D e out) : Compute (definitions D) e out := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .beta
  | delta hd => exact .delta (.inl hd)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Every earlier projection computation remains available. -/
theorem projection_base (H : ProjectionCompute D e out) : ProjectionCompute (definitions D) e out := by
  induction H with
  | base h => exact .base (compute_base h)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | projIota hi hl hg => exact .projIota hi hl hg
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- The full preceding mixed model embeds, including both eta forms, ordinary
iota, and any quotient-prefix equations already included in the base collection. -/
theorem etaCompute_base (H : ConstructorObservation.EtaCompute D e out) :
    ConstructorObservation.EtaCompute (definitions D) e out := by
  induction H with
  | compute h => exact .compute (projection_base h)
  | iota hp hc hm hn => exact .iota hp hc hm hn
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | funEta => exact .funEta
  | structEta hi hz ha hp => exact .structEta hi hz ha hp
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- The closed structure equation is one actual declaration computation step. -/
theorem unfold_compute (H : Unfolds name levels rhs) :
    Compute (definitions D) (.const name levels) rhs := .delta (.inr H)

/-- Supplying the complete telescope reaches the instantiated projection program
by one constant unfolding and finite beta computation. No source typing is needed. -/
theorem saturated_compute
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hr : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = data.uvars)
    (hi : env.projections (family data) info) (hn : info.nindices = 0)
    (hz : Admissible env univs data info levels)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset + 1) :
    Compute (definitions D) (mkApps (.const data.name levels) args)
      ((body data info levels r.1).instOuter args) := by
  obtain ⟨type, htype⟩ := hr.recursorType_exists
  have hdom := (type_shape (levels := levels) htype).2
  have H := ClosedQuot.compute_mkApps (D := definitions D) (unfold_compute (.intro hr hw hl hi hn hz hp hc)) args
  apply H.trans
  have hb := BetaRed.mkApps_wrapLams (domainsOf data levels) (body data info levels r.1) args (by omega)
  apply Compute.of_beta
  simpa only [value, ← ha, hdom, List.take_length, List.drop_length, mkApps_nil] using hb

/-- The complete mixed model now permits the added closed structure equations. -/
theorem function_type_below (hs : D.Sound env univs) (hD : ConstructorObservation.ConstructorRigid D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions D) (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  R.function_type_below (definitions_rigid hD) (definitions_sound hs) hΓ hf

/-- Actual environment equations discharge all declaration side conditions. -/
theorem function_type_below_ofEnv
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions (Definitions.ofEnv env univs henv))
      (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  function_type_below (Definitions.ofEnv_sound henv) ConstructorObservation.ConstructorRigid.ofEnv hΓ hf R

/-- The same reconstruction with every closed quotient-prefix equation retained. -/
theorem function_type_below_quot (hq : QuotRegistered env)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions (ClosedQuot.definitions env univs henv hq))
      (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  function_type_below (ClosedQuot.definitions_sound henv hq) (ClosedQuot.definitions_rigid hq) hΓ hf R

end Lean4Lean.VEnv.Strengthening.ClosedStructure
