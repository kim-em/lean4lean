import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance

/-! The binder introduced by actual Pi-row replay can retain its original
domain reservation while a later variable query rebuilds its tail. Its
active domain call has F phase; the immutable reservation has R phase.
The extra numerical reserve does not increase the original binder capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def reservedBindWorldEnvironment
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment) :
    WorldEnvironmentProvenance strata U
      ([.close (domain.dependencyOrigin controls.ordered) baselineEnvironment] ++
        (.close (domain.dependencyOrigin controls.ordered) selectedEnvironment :: selectedEnvironment)) :=
  .cons (.scheduled .expressionReindex (.ref domain) controls baseline)
    (.cons (.original (.ref domain) controls selected) selected)

/-- This is the actual domain call needed after a selected tail changes.
The proof uses both numerical capacity and the retained child-world relation. -/
theorem reservedBindWorld_domain_below
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost selectedEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds baseline.worlds) :
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental (.ref domain) selected)
      (originalCallWorld controls .expressionReindex (.ref domain) baseline) := by
  apply smaller_root (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans _ covered
  apply EquationControlMeasure.scheduleDecrease
  have cost : (Closure.close (domain.dependencyOrigin controls.ordered) selectedEnvironment).cost ≤
      (Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1)
  simp only [richSchedule, RichPhase.code]
  change 3 * (Closure.close (domain.dependencyOrigin controls.ordered) selectedEnvironment).cost <
    3 * (Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment).cost + 2
  omega

/-- Repeated activation retains the SAME immutable domain reserve, even when
the previous and next selected tails differ from its original tail. -/
theorem reservedBindWorld_retained_covered
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (selected : WorldEnvironmentProvenance strata U selectedEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost selectedEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) selected.worlds baseline.worlds)
    (previous : List (World strata.rules.length)) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (reservedBindWorldEnvironment controls domain baseline selected).worlds
      ([originalCallWorld controls .expressionReindex (.ref domain) baseline] ++ previous) := by
  intro world member
  refine ⟨originalCallWorld controls .expressionReindex (.ref domain) baseline,
    List.mem_cons_self .., ?_⟩
  change world ∈ [_] ++ ([_] ++ selected.worlds) at member
  rcases List.mem_append.mp member with member | member
  · cases List.mem_singleton.mp member
    exact .inl rfl
  · apply Or.inr
    rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      exact reservedBindWorld_domain_below controls domain selected baseline capacity covered
    · exact Covered.below (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans covered (fun _ present => .child present) world member

/-- The added immutable reservation has exactly the capacity of the original
binder. The active tail need not have an identical closure list. -/
theorem reservedBindWorld_capacity
    (domain : Origin) (selected baseline : List Closure)
    (capacity : environmentCost selected ≤ environmentCost baseline) :
    environmentCost ([Closure.close domain baseline] ++ (Closure.close domain selected :: selected)) =
      environmentCost (Closure.close domain baseline :: baseline) := by
  have bound : (Closure.close domain selected).cost ≤ (Closure.close domain baseline).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1)
  have tailBound : environmentCost baseline < (Closure.close domain baseline).cost := by
    have positive := Nat.mul_le_mul_right (1 + environmentCost baseline) domain.weight_pos
    simp only [Nat.one_mul] at positive
    change environmentCost baseline < domain.weight * (1 + environmentCost baseline)
    omega
  simp only [List.cons_append, List.nil_append, environmentCost]
  omega

/-- Fresh introduction is funded by the actual Pi formation used by
`WorldUnaryFrameData.bind`: its domain and body are actual original children.
This proves the new reservation is not an extra caller-supplied sponsor. -/
theorem reservedBindWorld_pi_children
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (captured : WorldEnvironmentProvenance strata U environment) :
    let parent := originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured
    WorldBelow strata.rules.length (originalCallWorld controls .expressionReindex (.ref domain) captured) parent ∧
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental body
      (reservedBindWorldEnvironment controls domain captured captured)) parent := by
  have domainCost := binder_domain_cost (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered]) (children := []) environment
  have bodyCost := binder_body_cost (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered]) (children := [])
    (List.mem_singleton_self _) environment
  have domainBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex (.ref domain) captured)
      (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured) :=
    original_child (richSchedule_strict domainCost _ _) _ _ _ _ _
  have activeDomainBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref domain) captured)
      (originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) captured) :=
    original_child (richSchedule_strict domainCost _ _) _ _ _ _ _
  refine ⟨domainBelow, ?_⟩
  have reservedBodyCost : (Closure.close (body.dependencyOrigin controls.ordered)
      ([Closure.close (domain.dependencyOrigin controls.ordered) environment] ++
        (Closure.close (domain.dependencyOrigin controls.ordered) environment :: environment))).cost <
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin controls.ordered) environment).cost := by
    change (Closure.close (body.dependencyOrigin controls.ordered)
      ([Closure.close (domain.dependencyOrigin controls.ordered) environment] ++
        (Closure.close (domain.dependencyOrigin controls.ordered) environment :: environment))).cost < _
    change (body.dependencyOrigin controls.ordered).weight * (1 + environmentCost
      ([Closure.close (domain.dependencyOrigin controls.ordered) environment] ++
        (Closure.close (domain.dependencyOrigin controls.ordered) environment :: environment))) < _
    rw [reservedBindWorld_capacity _ _ _ (Nat.le_refl _)]
    exact bodyCost
  apply Below.root (EquationControlMeasure.scheduleDecrease (richSchedule_strict reservedBodyCost _ _) _ _ _ _)
  intro child member
  change child ∈ [_] ++ ([_] ++ captured.worlds) at member
  rcases List.mem_append.mp member with member | member
  · cases List.mem_singleton.mp member
    exact domainBelow
  · rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      exact activeDomainBelow
    · exact .child member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
