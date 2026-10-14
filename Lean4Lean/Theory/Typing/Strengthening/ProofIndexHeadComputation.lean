import Lean4Lean.Theory.Typing.Strengthening.ClosedProofIndexUnfolding
import Lean4Lean.Theory.Typing.Strengthening.SingletonHeadComputation

/-! # Raw computation and descent for proof-index singleton prefixes

The closed registered equation simulates every generated prefix on arbitrary
raw arguments. Occurrence-specific alignment checks do not enter descent.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofIndexedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation (Definitions Compute)
variable [Params] {D : Definitions}

/-- Registered singleton equations whose declaration indices form a proposition
telescope after the parameters. -/
inductive Unfolds : Name → List VLevel → VExpr → Prop where
  | intro : RecursorRegistered env data → data.largeTarget = true →
      data.sourceLevel levels ≈ .zero → (∀ l ∈ levels, l.WF univs) → levels.length = data.uvars →
      data.singletonLayout env levels = some S →
      PropTelescope env univs (data.propParams levels).reverse S.indices →
      data.singletonUnfolding env univs levels [] = some program →
      Unfolds data.name levels program.rhs

/-- The added equation is valid independently of the occurrence context. -/
theorem Unfolds.equation (heq : env.HasCanonicalEq) (H : Unfolds name levels rhs) :
    env.IsDefEqU univs [] (.const name levels) rhs := by
  cases H with
  | intro hr hl hz hw hn hS hi hg => exact zero_equation henv heq hr hl hz hw hn hS hi hg

/-- Extend any preceding collection with the checked proof-index equations. -/
def definitions (heq : env.HasCanonicalEq) (D : Definitions) : Definitions where
  unfolds name levels rhs := D.unfolds name levels rhs ∨ Unfolds name levels rhs
  closed := by
    rintro name levels rhs (h | h)
    · exact D.closed h
    · obtain ⟨_, he⟩ := h.equation heq
      exact he.hasType.2.closedN henv.ordered trivial

/-- Each closed equation remains sound after weakening to an occurrence. -/
theorem definitions_sound (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    (definitions heq D).Sound env univs := by
  rintro Γ name levels rhs (h | h)
  · exact hs Γ name levels rhs h
  · obtain ⟨_, he⟩ := h.equation heq
    exact ⟨_, he.weak0 henv.ordered⟩

/-- The recursor's installed iota pattern excludes a projection constructor head. -/
theorem Unfolds.not_constructor (H : Unfolds name levels rhs)
    (hi : env.projections s info) : info.ctorName ≠ name := by
  cases H with
  | intro hr _ _ _ _ _ _ hg =>
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

/-- Constructor-sensitive head observations remain valid in the extension. -/
theorem definitions_rigid (heq : env.HasCanonicalEq)
    (hD : ConstructorObservation.ConstructorRigid D) :
    ConstructorObservation.ConstructorRigid (definitions heq D) := by
  rintro s info hi levels rhs (h | h)
  · exact hD s info hi levels rhs h
  · exact h.not_constructor hi rfl

/-- The unindexed singleton equations are included as empty proof telescopes. -/
theorem Unfolds.of_unindexed (H : ClosedSingleton.Unfolds name levels rhs) :
    Unfolds name levels rhs := by
  cases H with
  | intro hr hl hz hw hn hg hi =>
    obtain ⟨S, E, hS, _, _⟩ := RecursorData.singletonUnfolding_layout hg
    have hnil : S.indices = [] := List.eq_nil_of_length_eq_zero
      ((RecursorData.singletonLayout_lengths hS).1.trans hi)
    exact .intro hr hl hz hw hn hS (hnil ▸ PropTelescope.nil) hg

/-- Every generated arity is a closed unfolding followed by finite beta reduction.
The arguments need not be typed for this raw computation certificate. -/
theorem generated_compute (heq : env.HasCanonicalEq) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (hg : data.singletonUnfolding env univs levels args = some program) :
    Compute (definitions heq D) (mkApps (.const data.name levels) args) program.rhs := by
  obtain ⟨_, _, hlv, hlen, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
  rw [hlv] at hlen
  have hnlevels := hlen.trans (RecursorData.singletonEquation_uvars hseq)
  obtain ⟨zero, hg0⟩ := RecursorData.singletonUnfolding_anyArity hg (args' := []) (by simp)
  have hc : Compute (definitions heq D) (.const data.name levels) zero.rhs :=
    .delta (.inr (.intro H hlarge hzero hw hnlevels hS hindices hg0))
  exact (ClosedQuot.compute_mkApps hc args).trans
    (.of_beta (ClosedSingleton.generated_prefix_beta henv H hlarge hzero hg0 hg))

/-- A checked prefix embeds using declaration-level evidence of proof indices. -/
theorem prefix_compute (heq : env.HasCanonicalEq)
    (hlookup : registry name = some data)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (H : PrefixUnfold env univs registry Γ name levels args rhs) :
    Compute (definitions heq D) (mkApps (.const name levels) args) rhs := by
  cases H with
  | intro hl hr hname hlarge hw hz hg _ =>
    cases Option.some.inj (hl.symm.trans hlookup)
    subst hname
    exact generated_compute heq hr hlarge hz hw hS hindices hg

/-- Lower any proof-index singleton prefix with source typing below the lift. -/
theorem prefix_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hlookup : registry name = some data)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (H : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ (mkApps (.const name levels) args) T) :
    ∃ rhs₀, rhs = rhs₀.lift' ρ ∧ IsDefEq env univs Γ (mkApps (.const name levels) args) rhs₀ T := by
  have R := prefix_compute (D := D) heq hlookup hS hindices H
  have R' : Compute (definitions heq D) ((mkApps (.const name levels) args).lift' ρ) rhs := by
    simpa only [VExpr.lift'_mkApps, VExpr.lift'] using R
  obtain ⟨rhs₀, R0, he⟩ := R'.lift_inv
  exact ⟨rhs₀, he, R0.simAt henv (definitions_sound heq hs) hΓ T ht⟩

/-- Exact reflection of both supplied endpoints in the proof-index fragment. -/
theorem prefix_reflect (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hlookup : registry name = some data)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (H : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) (rhs.lift' ρ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ (mkApps (.const name levels) args) T) :
    IsDefEq env univs Γ (mkApps (.const name levels) args) rhs T := by
  obtain ⟨rhs₀, he, h⟩ := prefix_descend heq hs hlookup hS hindices H hΓ ht
  cases VExpr.lift'_inj.1 he
  exact h

/-- All definition assumptions can be discharged by the actual environment. -/
theorem prefix_reflect_ofEnv (heq : env.HasCanonicalEq)
    (hlookup : registry name = some data)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (H : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) (rhs.lift' ρ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ (mkApps (.const name levels) args) T) :
    IsDefEq env univs Γ (mkApps (.const name levels) args) rhs T :=
  prefix_reflect heq (Definitions.ofEnv_sound henv) hlookup hS hindices H hΓ ht

/-- Pi exposure in the preceding mixed model may use proof-index unfoldings. -/
theorem function_type_below (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ConstructorObservation.ConstructorRigid D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : ConstructorObservation.EtaCompute (definitions heq D) (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  R.function_type_below (definitions_rigid heq hD) (definitions_sound heq hs) hΓ hf

end Lean4Lean.VEnv.Strengthening.ProofIndexedSingleton
