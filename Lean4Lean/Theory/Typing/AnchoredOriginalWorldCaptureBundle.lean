import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance

/-! The actual own-capture bundle has strictly more cost than either of its
two retained original calls. A single immutable world at that bundle cost
therefore covers a reconstructed owner/domain pair, even when the selected
tail duplicates covered captures at unchanged cost. This is a reservation
for the existing numerical bundle, not a larger original or a semantic
reconstruction assumption. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def captureBundleWorld
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (captured : WorldEnvironmentProvenance strata U environment) : World strata.rules.length :=
  .node (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
    controls.ordered.constantCount (richSchedule .expressionReindex
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) environment)
        (.close (domain.dependencyOrigin controls.ordered) environment)).cost)) captured.worlds

private theorem close_cost_mono (origin : Origin)
    (capacity : environmentCost actual ≤ environmentCost baseline) :
    (Closure.close origin actual).cost ≤ (Closure.close origin baseline).cost :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1)

private theorem environment_lt_close (origin : Origin) (environment : List Closure) :
    environmentCost environment < (Closure.close origin environment).cost := by
  have bound := Nat.mul_le_mul_right (1 + environmentCost environment) origin.weight_pos
  simp only [Nat.one_mul] at bound
  change environmentCost environment < origin.weight * (1 + environmentCost environment)
  omega

theorem captureBundleWorld_owner_below
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (actual : WorldEnvironmentProvenance strata U actualEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost actualEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds)
    (phase : RichPhase) :
    WorldBelow strata.rules.length (originalCallWorld controls phase argument actual)
      (captureBundleWorld controls domain argument baseline) := by
  apply smaller_root (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans _ covered
  apply EquationControlMeasure.scheduleDecrease
  apply richSchedule_strict
  have bound := close_cost_mono (argument.dependencyOrigin controls.ordered) capacity
  have positive := Closure.cost_pos (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)
  change (Closure.close (argument.dependencyOrigin controls.ordered) actualEnvironment).cost <
    (Closure.close (argument.dependencyOrigin controls.ordered) baselineEnvironment).cost +
      (Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment).cost
  omega

theorem captureBundleWorld_domain_below
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (actual : WorldEnvironmentProvenance strata U actualEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost actualEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds)
    (phase : RichPhase) :
    WorldBelow strata.rules.length (originalCallWorld controls phase (.ref domain) actual)
      (captureBundleWorld controls domain argument baseline) := by
  apply smaller_root (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans _ covered
  apply EquationControlMeasure.scheduleDecrease
  apply richSchedule_strict
  have bound := close_cost_mono (domain.dependencyOrigin controls.ordered) capacity
  have positive := Closure.cost_pos (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
  change (Closure.close (domain.dependencyOrigin controls.ordered) actualEnvironment).cost <
    (Closure.close (argument.dependencyOrigin controls.ordered) baselineEnvironment).cost +
      (Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment).cost
  omega

/-- This is the exact output layout of an immutable original bundle reserve
around a reconstructed flat capture. The old owner/domain reservations remain
available as well; their membership is not replaced by a numeric bound. -/
theorem captureBundleWorld_retained_covered_reserve
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (actual : WorldEnvironmentProvenance strata U actualEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost actualEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds) :
    let reserve := [captureBundleWorld controls domain argument baseline,
      originalCallWorld controls .expressionReindex argument baseline,
      originalCallWorld controls .fundamental (.ref domain) baseline]
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (reserve ++ ([originalCallWorld controls .expressionReindex argument actual,
        originalCallWorld controls .fundamental (.ref domain) actual] ++ actual.worlds))
      reserve := by
  dsimp only
  apply Covered.merge
  · intro world member
    exact ⟨world, member, .inl rfl⟩
  · intro world member
    refine ⟨captureBundleWorld controls domain argument baseline,
      List.mem_cons_self .., .inr ?_⟩
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_cons.mp member with rfl | member
      · exact captureBundleWorld_owner_below controls domain argument actual baseline capacity covered _
      · cases List.mem_singleton.mp member
        exact captureBundleWorld_domain_below controls domain argument actual baseline capacity covered _
    · exact Covered.below (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans covered (fun _ member => .child member) world member

/-- Both old and new selected tails may differ from the original reserved
tail. The invariant is retained by the immutable reserve itself, not by an
assumption that the previous selected frame contains all original worlds. -/
theorem captureBundleWorld_retained_covered
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (argument : EndpointState sourceEnv U source a A)
    (actual : WorldEnvironmentProvenance strata U actualEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost actualEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds)
    (previous : List (World strata.rules.length)) :
    let reserve := [captureBundleWorld controls domain argument baseline,
      originalCallWorld controls .expressionReindex argument baseline,
      originalCallWorld controls .fundamental (.ref domain) baseline]
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (reserve ++ ([originalCallWorld controls .expressionReindex argument actual,
        originalCallWorld controls .fundamental (.ref domain) actual] ++ actual.worlds))
      (reserve ++ previous) := by
  intro reserve world member
  obtain ⟨old, present, lower⟩ :=
    captureBundleWorld_retained_covered_reserve controls domain argument actual baseline capacity covered world member
  exact ⟨old, List.mem_append_left _ present, lower⟩

/-- Adding the immutable bundle reserve changes neither the old capture's
capacity nor its available resources: the numerical environment is a max. -/
theorem captureBundleWorld_retained_capacity
    (owner domain : Origin) (actual baseline : List Closure)
    (capacity : environmentCost actual ≤ environmentCost baseline) :
    environmentCost
      ([Closure.bundle (.close owner baseline) (.close domain baseline)] ++
        (Closure.bundle (.close owner actual) (.close domain actual) :: actual)) =
      environmentCost (Closure.bundle (.close owner baseline) (.close domain baseline) :: baseline) := by
  have ownerBound := close_cost_mono owner capacity
  have domainBound := close_cost_mono domain capacity
  have oldTail := environment_lt_close owner baseline
  simp only [List.cons_append, List.nil_append, environmentCost, Closure.cost]
  change max ((Closure.close owner baseline).cost + (Closure.close domain baseline).cost)
      (max ((Closure.close owner actual).cost + (Closure.close domain actual).cost) (environmentCost actual)) =
    max ((Closure.close owner baseline).cost + (Closure.close domain baseline).cost) (environmentCost baseline)
  omega

/-- The newly introduced bundle reservation is itself a strict child of
the real application which creates this capture. No external sponsor is
added, and both proof-bearing endpoints are the actual application inputs. -/
theorem captureBundleWorld_below_application
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (captured : WorldEnvironmentProvenance strata U environment) :
    WorldBelow strata.rules.length (captureBundleWorld controls domain argument captured)
      (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) captured) := by
  apply original_child
  apply richSchedule_strict
  have bodyBound := capturedApplication_comparison (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered) environment
  have bundleBound := variable_lookup (body.dependencyOrigin controls.ordered)
    (environment := Closure.bundle
      (.close (argument.dependencyOrigin controls.ordered) environment)
      (.close (domain.dependencyOrigin controls.ordered) environment) :: environment)
    (List.mem_cons_self ..)
  exact Nat.lt_trans bundleBound (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) bodyBound)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
