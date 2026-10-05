import Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
import Lean4Lean.Theory.Typing.NativeDeclarationProvenance
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLive

/-! Actual native-headed observers consume their stored finite plan. Every
argument demand is retained as a graded source observer in the caller's fixed
valuation; no native argument supply is assumed independently. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open NativeRecursorData hiding target levels
set_option backward.isDefEq.respectTransparency false

noncomputable def NativePlanConsumption.rowShift
    {n : Nat} {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : NativePlanConsumption env U registry target locals σ available data levels arguments
      (n := n + 1) (.fn key output)) :
    NativePlanConsumption env U registry target locals σ available data levels arguments
      (n := n + 2) (.fn key.pad (.pad output)) :=
  (result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn key output)

/-- Select any actual atom of a native-headed observation, consuming exactly
its observed application spine up to the major argument. The original
registered type supplies each binder's formation child. -/
theorem Obs.consumeNative
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ A level}, origin.stage.typing.recursors.IsDefEqStrong U Γ A A (.sort level) →
      GradedJoint env U registry Γ A A (.sort level))
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    {levels : List VLevel} (head : expression.getAppFnArgs.1 = .const data.name levels)
    (length : expression.getAppFnArgs.2.length ≤ data.majorOffset + 1)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available)
    {atom : Atom n} (member : atom ∈ demand.atoms) :
    Nonempty (NativePlanConsumption env U registry target locals σ available data levels
      expression.getAppFnArgs.2 atom) := by
  match n, atom, demand, expression, observation with
  | _, _, _, _, .delta found nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨name, packet⟩ := VExpr.const.inj head
    rw [name, notDefinition] at found
    cases found
  | _, _, _, _, .native found noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨name, packet⟩ := VExpr.const.inj head
    rw [name, lookup] at found
    cases Option.some.inj found
    cases packet
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree
    refine ⟨{
      rank := _
      bound := Nat.le_refl _
      seedLevels := _
      seedWF := seedWF
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
  | _, _, _, _, .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨name, _⟩ := VExpr.const.inj head
    rw [name, lookup] at noNative
    cases noNative
  | _, _, _, _, .constructor found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨name, _⟩ := VExpr.const.inj head
    rw [name, lookup] at noNative
    cases noNative
  | _, _, _, _, .var .. => simp only [getAppFnArgs_bvar] at head; cases head
  | _, _, _, _, .empty => cases member
  | _, _, _, _, .sort .. => simp only [getAppFnArgs_sort] at head; cases head
  | _, _, _, _, .lam .. => simp only [getAppFnArgs_lam] at head; cases head
  | _, _, _, _, .pi .. => simp only [getAppFnArgs_forallE] at head; cases head
  | _, _, _, _, .app fn arg inputs admitted =>
    have atomEq := List.mem_singleton.mp member
    simp only [getAppFnArgs_app] at head length ⊢
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    obtain ⟨prior⟩ := fn.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
      head (by simp only [List.length_append, List.length_singleton] at length; omega)
      scope.1 first (List.mem_singleton_self _)
    obtain ⟨level, header⟩ := origin.typeStrong prior.signature.typeOrigin
    have formation : origin.stage.typing.recursors.IsDefEqStrong U []
        (prior.signature.type.instL prior.seedLevels) (prior.signature.type.instL prior.seedLevels)
        (.sort (level.inst prior.seedLevels)) := by
      simpa only [List.map_nil, VExpr.instL] using header.instL prior.seedWF
    exact atomEq.symm ▸ prior.app henv hscoped
      (origin.stage.typing.recursors_le.trans origin.stage.installedBelow) earlier hTarget formation
      (by simp only [List.length_append, List.length_singleton] at length; omega)
      arg second (arg.live henv hscoped hTarget
        (fits.leavesLive henv hscoped hTarget second (arg.scoped scope.2))) inputs admitted
  | _, _, _, _, .union left right =>
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    rcases List.mem_append.mp member with hm | hm
    · exact left.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
        head length scope first hm
    · exact right.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
        head length scope second hm
  | _, _, _, _, .view original change =>
    cases List.mem_singleton.mp member
    obtain ⟨prior⟩ := original.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
      head length scope resources (List.mem_singleton_self _)
    exact ⟨prior.view henv hscoped hTarget change⟩
  | _, _, _, _, .pad original =>
    obtain ⟨a, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨prior⟩ := original.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
      head length scope resources hm
    exact ⟨prior.pad henv hscoped hTarget⟩
  | _, _, _, _, .unpad original =>
    obtain ⟨prior⟩ := original.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
      head length scope resources (List.mem_map_of_mem member)
    exact ⟨prior.unpad⟩
  | _, _, _, _, .rowShift original =>
    cases List.mem_singleton.mp member
    obtain ⟨prior⟩ := original.consumeNative origin henv hscoped earlier lookup notDefinition hTarget fits
      head length scope resources (List.mem_singleton_self _)
    exact ⟨prior.rowShift henv hscoped hTarget⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
