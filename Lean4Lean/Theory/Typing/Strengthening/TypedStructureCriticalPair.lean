import Lean4Lean.Theory.Typing.Strengthening.StructureUnfoldingCriticalPair
import Lean4Lean.Theory.Typing.Strengthening.ProjectionConfluence

/-! # Every typed pattern overlap with a selected structure program

The recursor lookup fixes the major offset. Typing the matching major at the
registered structure family then fixes its constructor and arity, so any
competing registered pattern is the structure program's own pattern. The
existing beta/projection join therefore covers every typed pattern overlap.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params PureObservation
variable [Params] {D : Definitions}

/-- A competing registered pattern at a typed instance of the selected recursor
joins the closed program. Its pattern, constructor and arity are inferred from
the registry and actual source typing, rather than supplied as equalities. -/
theorem unfolded_pattern_join
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hreg : recursorData data.name = some data)
    (hi : env.projections (family data) info) (hp : Pat _ r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp' : Pat p r') (hm : p.Matches source levels' captures)
    (hh : source.getAppFn = .const data.name levels)
    (ht : env.HasType univs Γ source T) :
    ProjectionCompute D
      (mkApps (value data info levels r.1 (domainsOf data levels)) source.getAppArgs)
      (r'.1.apply levels' captures) := by
  obtain ⟨hr, _⟩ := recursorData_registered hreg
  obtain ⟨sp, rfl⟩ := pat_simple hp'
  cases sp with
  | defn c =>
    cases hm
    cases hh
    rw [(pat_const_not_unfolding hp').1] at hreg
    cases hreg
  | iota rc mr cc kc =>
    cases hm with
    | app hrec hctor =>
      obtain ⟨args, ha, rfl, _⟩ := Pattern.matches_varN_const_inv hrec
      obtain ⟨ctorArgs, hca, rfl, _⟩ := Pattern.matches_varN_const_inv hctor
      simp only [getAppFn, getAppFn_mkApps, VExpr.const.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      rcases pat_recursor hp' with ⟨data', hr', hn', hmo, hreg', _⟩ | ⟨hq, hn, _⟩
      · rw [hreg] at hreg'
        cases hreg'
        cases hmo
        obtain ⟨_, _, params, hmajor⟩ := hr.major_type henv hΓ ht ha
        obtain ⟨rfl, rfl⟩ := pat_struct_major hp' hΓ hi hmajor hca
        exact unfolded_iota_join_other hr hi hp hp' (.app hrec hctor)
      · rw [hn, recursorData_quot hq] at hreg
        cases hreg

end Lean4Lean.VEnv.Strengthening.ClosedStructure

namespace Lean4Lean.VEnv.Strengthening.RegisteredStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params] {D : Definitions}

/-- A selected structure unfolding heads an installed rule, so its head is
never rigid. This also excludes ordinary inductive constructor heads. -/
theorem Unfolds.not_rigid (H : Unfolds name levels rhs) : ¬ env.Rigid name := by
  intro hrig
  cases H.closedStructure with
  | intro _ _ _ _ _ _ hp _ =>
    exact hrig.not_patternHeadsStoredRule (pat_storedRule hp)
      (by simp [ClosedStructure.pattern, Pattern.constHead_eq, Pattern.headConst, Pattern.headConst_varN])

/-- Every rigid head, including each iota constructor, remains unavailable to
closed delta in the actual stored/selected-structure collection. -/
theorem definitions_ofEnv_no_rigid (hrig : env.Rigid name) :
    ¬ (definitions (Definitions.ofEnv env univs henv)).unfolds name levels rhs := by
  rintro (H | H)
  · exact Definitions.ofEnv_no_rigid henv hrig H
  · exact H.not_rigid hrig

/-- Every typed root pattern competing with registry-selected structure delta
is joined by beta and projections after the head has unfolded. -/
theorem Unfolds.pattern_join (H : Unfolds name levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hm : p.Matches source levels' captures)
    (hh : source.getAppFn = .const name levels)
    (ht : env.HasType univs Γ source T) :
    ProjectionCompute D (mkApps rhs source.getAppArgs) (r.1.apply levels' captures) := by
  cases H with
  | intro hreg hw hl hi hx hz hp' hc =>
    obtain ⟨_, hname⟩ := recursorData_registered hreg
    rw [← hname] at hreg hh
    exact ClosedStructure.unfolded_pattern_join hreg hi hp' hΓ hp hm hh ht

/-- A selected structure equation simulates every typed pattern contraction at
its head using only closed delta, beta and projection computation. -/
theorem Unfolds.pattern_compute (H : Unfolds name levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hm : p.Matches source levels' captures)
    (hh : source.getAppFn = .const name levels)
    (ht : env.HasType univs Γ source T) :
    ProjectionCompute (definitions D) source (r.1.apply levels' captures) := by
  have R := ClosedQuot.compute_mkApps (Compute.delta (D := definitions D) (.inr H)) source.getAppArgs
  rw [← hh, mkApps_getAppFn_getAppArgs] at R
  exact (ProjectionCompute.base R).trans (H.pattern_join hΓ hp hm hh ht)

/-- The simulation also develops every captured subterm, as required for an
ordinary parallel iota step. No new matching or check certificate is needed. -/
theorem Unfolds.pattern_compute_captures (H : Unfolds name levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hm : p.Matches source levels' captures)
    (hh : source.getAppFn = .const name levels)
    (ht : env.HasType univs Γ source T)
    (HC : ∀ path, ProjectionCompute (definitions D) (captures path) (captures' path)) :
    ProjectionCompute (definitions D) source (r.1.apply levels' captures') :=
  (H.pattern_compute hΓ hp hm hh ht).trans (ClosedStructure.projection_apply_pat r.1 HC)

/-- At a selected structure head, a typed pattern contraction followed by any
beta/delta/projection path joins every competing such path from the source.
This uses the checked confluence instance of the actual declaration union. -/
theorem Unfolds.pattern_path_join (H : Unfolds name levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hm : p.Matches source levels' captures)
    (hh : source.getAppFn = .const name levels)
    (ht : env.HasType univs Γ source T)
    (R1 : ProjectionCompute (definitions (Definitions.ofEnv env univs henv))
      (r.1.apply levels' captures) a)
    (R2 : ProjectionCompute (definitions (Definitions.ofEnv env univs henv)) source b) :
    ∃ out, ProjectionCompute (definitions (Definitions.ofEnv env univs henv)) a out ∧
      ProjectionCompute (definitions (Definitions.ofEnv env univs henv)) b out :=
  ((H.pattern_compute hΓ hp hm hh ht).trans R1).registeredStructure_confluent R2

end Lean4Lean.VEnv.Strengthening.RegisteredStructure
