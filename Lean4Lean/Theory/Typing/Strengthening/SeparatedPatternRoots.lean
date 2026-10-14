import Lean4Lean.Theory.Typing.Strengthening.TypedStructureCriticalPair
import Lean4Lean.Theory.Typing.Strengthening.CoreHeadExposure

/-! # Removing pattern roots that overlap closed declaration unfolding

At typed sources, every ordinary pattern either computes using only the
stored/structure beta-delta-projection collection or has a head with no closed
unfolding in that collection. This prepares a presentation with disjoint heads;
it does not assert confluence for the remaining ordinary patterns or prefixes.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private theorem compute_registered_base (H : Compute D e out) :
    Compute (RegisteredStructure.definitions D) e out := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | beta => exact .beta
  | delta H => exact .delta (.inl H)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- An iota head cannot also be a stored bare-constant definition. The recursor
case uses its owned constructor; the quotient case uses installed head separation. -/
theorem iota_no_stored_definition
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (H : (Definitions.ofEnv env univs henv).unfolds rc levels rhs) : False := by
  rcases pat_recursor hp with ⟨data, hr, hn, _, _, howner, _⟩ | ⟨hq, hn, _⟩
  · exact Definitions.ofEnv_no_registered henv hr howner (by simpa only [hn] using H)
  · subst hn
    obtain ⟨value, hreg, hname, _⟩ := Definitions.ofEnv_origin henv H
    have hv := (definitionRegistry_registered hreg).1
    exact henv.quotLift_not_definition hq.equation hv.2 (VLevel.params value.uvars)
      (by simp only [VDefVal.toDefEq, hname])

/-- Every typed ordinary pattern root is either already beta/delta/projection
computation, or its head is disjoint from all stored and selected-structure
unfoldings at these universes. The second alternative retains the original
pattern and captures unchanged. -/
theorem pattern_projection_or_separated
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hm : p.Matches source levels captures)
    (ht : env.HasType univs Γ source T) :
    ProjectionCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))
        source (r.1.apply levels captures) ∨
      (∀ rhs, ¬ (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)).unfolds
        p.headConst levels rhs) := by
  classical
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn c =>
    exact .inl (.base (compute_registered_base (definition_compute henv hΓ (hcon hp) hm ⟨_, ht⟩)))
  | iota rc mr cc kc =>
    by_cases H : ∃ rhs, RegisteredStructure.Unfolds rc levels rhs
    · obtain ⟨rhs, H⟩ := H
      obtain ⟨args, major, hsource, _⟩ := iota_matches_spine hm
      have hh : source.getAppFn = .const rc levels := by
        rw [hsource]
        simp only [getAppFn, getAppFn_mkApps]
      exact .inl (H.pattern_compute hΓ hp hm hh ht)
    · refine .inr ?_
      simp only [SimplePattern.iota_headConst]
      change ∀ rhs, ¬ ((Definitions.ofEnv env univs henv).unfolds rc levels rhs ∨
        RegisteredStructure.Unfolds rc levels rhs)
      rintro rhs (H' | H')
      · exact iota_no_stored_definition hp H'
      · exact H ⟨rhs, H'⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
