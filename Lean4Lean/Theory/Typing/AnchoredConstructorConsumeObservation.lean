import Lean4Lean.Theory.Typing.AnchoredConstructorPlanConsumption
import Lean4Lean.Theory.Typing.AnchoredConstructorSourceShape
import Lean4Lean.Theory.Typing.ConstantHeaderProvenance
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLive

/-! Consume an actual constructor-headed source observer, including all of
its application and adapter wrappers. The original constant header supplies
the strictly earlier formation theorem for each consumed declaration binder. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

noncomputable def ConstructorPlanConsumption.rowShift
    {n : Nat} {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : ConstructorPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 1) (.fn key output)) :
    ConstructorPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 2) (.fn key.pad (.pad output)) :=
  (result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn key output)

theorem Obs.consumeConstructor
    {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ A level}, origin.source.IsDefEqStrong U Γ A A (.sort level) →
      GradedJoint env U registry Γ A A (.sort level))
    {domains familyArguments : List VExpr} {family : Name} {familyLevels : List VLevel}
    (shape : info.type = wrapForalls domains (mkApps (.const family familyLevels) familyArguments))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    {levels : List VLevel} (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available)
    {atom : Atom n} (member : atom ∈ demand.atoms) :
    Nonempty (ConstructorPlanConsumption env U registry target locals σ available info name levels
      expression.getAppFnArgs.2 atom) := by
  match n, atom, demand, expression, observation with
  | _, _, _, _, .delta found nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, _⟩ := VExpr.const.inj head
    rw [sameName, notDefinition] at found
    cases found
  | _, _, _, _, .native found noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, _⟩ := VExpr.const.inj head
    rw [sameName, notNative] at found
    cases found
  | _, _, _, _, .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, packet⟩ := VExpr.const.inj head
    cases sameName
    rw [origin.constant] at found
    cases Option.some.inj found
    exact (tree.not_constructorHeader shape).elim
  | _, _, _, _, .constructor found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, packet⟩ := VExpr.const.inj head
    cases sameName
    rw [origin.constant] at found
    cases Option.some.inj found
    cases packet
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree
    refine ⟨{
      rank := _
      bound := Nat.le_refl _
      seedLevels := _
      seedWF := seedWF
      seedLength := seedLength
      equivalent := equivalent
      signature := signature
      typeClosed := typeClosed
      anchors := []
      length := rfl
      output := _
      footprint := []
      plan := tree
      adapter := by rw [raiseAtom_self]; exact .refl _
      valuation := fun _ => []
      closed := fun _ _ hm => nomatch hm
      raw := .nil
      fits := .nil
      resources := fun _ _ hm => nomatch hm
      observed := NativeGradedValuation.empty }⟩
  | _, _, _, _, .var .. => simp only [getAppFnArgs_bvar] at head; cases head
  | _, _, _, _, .empty => cases member
  | _, _, _, _, .sort .. => simp only [getAppFnArgs_sort] at head; cases head
  | _, _, _, _, .lam .. => simp only [getAppFnArgs_lam] at head; cases head
  | _, _, _, _, .pi .. => simp only [getAppFnArgs_forallE] at head; cases head
  | _, _, _, _, .app fn arg inputs admitted =>
    have atomEq := List.mem_singleton.mp member
    simp only [getAppFnArgs_app] at head ⊢
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    obtain ⟨prior⟩ := fn.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
      hTarget fits head scope.1 first (List.mem_singleton_self _)
    obtain ⟨level, formation⟩ := origin.typeInstance prior.seedWF
    exact atomEq.symm ▸ prior.app henv hscoped origin.sourceBelow earlier hTarget formation
      arg second (arg.live henv hscoped hTarget
        (fits.leavesLive henv hscoped hTarget second (arg.scoped scope.2))) inputs admitted
  | _, _, _, _, .union left right =>
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    rcases List.mem_append.mp member with hm | hm
    · exact left.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
        hTarget fits head scope first hm
    · exact right.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
        hTarget fits head scope second hm
  | _, _, _, _, .view original change =>
    cases List.mem_singleton.mp member
    obtain ⟨prior⟩ := original.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _)
    exact ⟨prior.view henv hscoped hTarget change⟩
  | _, _, _, _, .pad original =>
    obtain ⟨a, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨prior⟩ := original.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
      hTarget fits head scope resources hm
    exact ⟨prior.pad henv hscoped hTarget⟩
  | _, _, _, _, .unpad original =>
    obtain ⟨prior⟩ := original.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
      hTarget fits head scope resources (List.mem_map_of_mem member)
    exact ⟨prior.unpad⟩
  | _, _, _, _, .rowShift original =>
    cases List.mem_singleton.mp member
    obtain ⟨prior⟩ := original.consumeConstructor origin henv hscoped earlier shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _)
    exact ⟨prior.rowShift henv hscoped hTarget⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
