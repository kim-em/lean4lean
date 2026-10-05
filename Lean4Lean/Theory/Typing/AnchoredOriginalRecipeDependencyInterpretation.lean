import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeLegacyDependency

/-! Total retained-program dependency evaluation. Charged roots enter their
literal child certificates, native rows enter their literal child bodies,
and all six pending recipe operations preserve the same dependency model.
No requested-row recipe is manufactured during recursion. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private suppliedLeft suppliedRight piModel from Lean4Lean.Theory.Typing.AnchoredOriginalRecipeLegacyDependency
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem tailClosed {available : Valuation} (closed : available.AtomClosed) :
    Valuation.AtomClosed (fun index => available (index + 1)) :=
  fun index need member selected belongs => closed (index + 1) need member selected belongs

private theorem tailSupply
    (supplied : RecipeFootprintDependency env U registry target available
      (footprint.sourceLift (.skip .refl))) :
    RecipeFootprintDependency env U registry target (fun index => available (index + 1)) footprint := by
  intro index need member
  have selected : (index + 1, need) ∈ footprint.sourceLift (.skip .refl) :=
    List.mem_map.mpr ⟨(index, need), member, rfl⟩
  exact RecipeVariableDependency.reindex (fun _ => Iff.rfl) (supplied _ _ selected)

private theorem actualHead
    (closed : available.AtomClosed)
    (head : RecipeVariableDependency env U registry target available 0 input) :
    RecipeResourceDependency env U registry target
      (Valuation.push (recipeDependencyInputs input) (fun index => available (index + 1))) available := by
  intro index need member
  cases index with
  | succ index => exact RecipeVariableDependency.leaf member
  | zero =>
    change need ∈ recipeDependencyInputs input at member
    rcases List.mem_append.mp member with original | atomic
    · cases List.mem_singleton.mp original
      exact head
    · obtain ⟨old, oldMember, selected⟩ := List.mem_flatMap.mp atomic
      cases List.mem_singleton.mp oldMember
      obtain ⟨atom, belongs, equal⟩ := List.mem_map.mp selected
      cases equal
      exact RecipeVariableDependency.select closed head belongs

mutual
 theorem RichCert.dependencyModel
    {node : EndpointState sourceEnv U source expression assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .legacy child => exact SortableCert.dependencyModel child closed supplied
  | .recipe child => exact RichCodeRecipe.dependencyModel child closed supplied
  | .observe child _ => exact RichObs.dependencyModel child closed supplied
  | .pi hu hv domain guard rows =>
    exact piModel (RichCert.dependencyModel domain closed (suppliedLeft supplied))
      (RichRows.dependencyModel rows closed (suppliedRight supplied))
  | .route _ child => exact RichCert.dependencyModel child closed supplied
  | .union left right =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).union (RichCert.dependencyModel left closed (suppliedLeft supplied))
      (RichCert.dependencyModel right closed (suppliedRight supplied))
  | .pad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (RichCert.dependencyModel child closed supplied)
  | .down child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed .down child.formed (RichCert.dependencyModel child closed supplied)
  | .map change child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.map change) child.formed (RichCert.dependencyModel child closed supplied)
  | .support change child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.support change) child.formed (RichCert.dependencyModel child closed supplied)
  | .select child member => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).select closed (RichCert.dependencyModel child closed supplied) member
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem RichObs.dependencyModel
    {node : EndpointState sourceEnv U source expression assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .rigidFamily .. | .family .. | .constructor .. | .canonicalDelta .. | .canonicalConst .. | .projection .. | .projectionSortable .. | .app .. | .lam .. =>
    simp only [RecipeDependencyProfile]
  | .legacy child => exact SortableObs.dependencyModel child closed supplied
  | .code child => exact RichCert.dependencyModel child closed supplied
  | .route _ child => exact RichObs.dependencyModel child closed supplied
  | .union left right =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).union (RichObs.dependencyModel left closed (suppliedLeft supplied))
      (RichObs.dependencyModel right closed (suppliedRight supplied))
  | .view child change => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed (.view change) (RichObs.dependencyModel child closed supplied)
  | .action child change => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed change (RichObs.dependencyModel child closed supplied)
  | .select child member => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).select closed (RichObs.dependencyModel child closed supplied) member
  | .pad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (RichObs.dependencyModel child closed supplied)
  | .unpad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).unpad (RichObs.dependencyModel child closed supplied)
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem RichRows.dependencyModel
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (query : RichRows sourceEnv env U registry target domain body locals σ relevant support rows footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    ∀ key result, (key, result) ∈ rows →
      RecipeDependencyProfile env U registry target B result
        (Valuation.push (recipeDependencyInputs key.input) available) := by
  match query with
  | .nil => intro _ _ member; cases member
  | .cons guard body pack covered tail =>
    intro key result member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact RichCert.dependencyModel body (recipeDependencyInputs.closed closed)
        (BinderPack.dependencySupply pack covered (suppliedLeft supplied))
    · exact RichRows.dependencyModel tail closed (suppliedRight supplied) key result member
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem RichCodeRecipe.dependencyModel
    (query : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .root source locals σ owner node sourceClosed expressionEq realization child resources =>
    have root := RichCert.dependencyModel child
      (available := fun _ => []) (by intro _ _ member; cases member)
      (fun i need member => RecipeVariableDependency.leaf (resources i need member))
    have moved := RecipeDependencyProfile.transport
      (second := available) (fun _ _ member => by cases member) root
    exact RecipeDependencyProfile.levels expressionEq |>.mp moved
  | .domain parent =>
    have whole := RichCodeRecipe.dependencyModel parent closed supplied
    simp only [RecipeDependencyProfile] at whole
    exact (whole _ List.mem_cons_self).1
  | .body parent selected anchor =>
    have parentSupply := tailSupply (fun i need member => supplied i need (List.mem_cons_of_mem _ member))
    have whole := RichCodeRecipe.dependencyModel parent (tailClosed closed) parentSupply
    simp only [RecipeDependencyProfile] at whole
    have row := (whole _ List.mem_cons_self).2 _ _ selected
    exact RecipeDependencyProfile.transport
      (actualHead closed (supplied 0 _ List.mem_cons_self)) row
  | .fixedBody parent selected admitted =>
    have whole := RichCodeRecipe.dependencyModel parent closed supplied
    simp only [RecipeDependencyProfile] at whole
    exact RecipeDependencyProfile.dropUnusedHead ((whole _ List.mem_cons_self).2 _ _ selected)
  | .resources parent transfer =>
    exact RichCodeRecipe.dependencyModel parent closed
      (transfer.dependencyReplay supplied)
  | .action change parent =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) expression).code closed change parent.formed
      (RichCodeRecipe.dependencyModel parent closed supplied)
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega
end

/-- The total incoming-variable compiler target. Every recipe and wrapper has
been evaluated into a finite ordinary variable trace; this is not a second
recipe with the same pending body operation. -/
theorem RichObs.variableDependency
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    RecipeVariableDependency env U registry target available index profile := by
  have result := RichObs.dependencyModel query closed
    (fun i need member => RecipeVariableDependency.leaf (resources i need member))
  simpa only [RecipeDependencyProfile] using result

theorem RichCert.variableDependency
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    RecipeVariableDependency env U registry target available index profile := by
  have result := RichCert.dependencyModel query closed
    (fun i need member => RecipeVariableDependency.leaf (resources i need member))
  simpa only [RecipeDependencyProfile] using result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
