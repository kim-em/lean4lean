import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyScope
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyActions

/-! Every legacy and sortable query has its actual finite dependency
interpretation. This is syntactic program evaluation, not fundamental typing.
No original F/R call or supplied Pi row reanchoring is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

abbrev RecipeFootprintDependency (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (available : Valuation) (footprint : Footprint) : Prop :=
  ∀ index need, (index, need) ∈ footprint →
    RecipeVariableDependency env U registry target available index need.profile

private theorem suppliedLeft
    (supplied : RecipeFootprintDependency env U registry target available (first ++ second)) :
    RecipeFootprintDependency env U registry target available first :=
  fun i need member => supplied i need (List.mem_append_left _ member)
private theorem suppliedRight
    (supplied : RecipeFootprintDependency env U registry target available (first ++ second)) :
    RecipeFootprintDependency env U registry target available second :=
  fun i need member => supplied i need (List.mem_append_right _ member)

private theorem piModel
    {support : Profile n} {table : List (Key n × Profile n)}
    (domain : RecipeDependencyProfile env U registry target A support available)
    (rows : ∀ key result, (key, result) ∈ table →
      RecipeDependencyProfile env U registry target B result
        (Valuation.push (recipeDependencyInputs key.input) available)) :
    RecipeDependencyProfile env U registry target (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody support table) available := by
  simp only [RecipeDependencyProfile]
  intro atom member
  cases List.mem_singleton.mp member
  exact ⟨domain, rows⟩

mutual
 theorem Obs.dependencyModel
    (query : Obs env U registry target locals σ expression profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .delta .. | .native .. | .family .. | .constructor .. | .sort .. | .app .. | .lam .. =>
    simp only [RecipeDependencyProfile]
  | .var .. =>
    simp only [RecipeDependencyProfile]
    exact supplied _ _ List.mem_cons_self
  | .empty => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).empty
  | .pi domain guard rows =>
    exact piModel (CodeCert.dependencyModel domain closed (suppliedLeft supplied))
      (PiRows.dependencyModel rows closed (suppliedRight supplied))
  | .union left right =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).union (Obs.dependencyModel left closed (suppliedLeft supplied))
      (Obs.dependencyModel right closed (suppliedRight supplied))
  | .view child change =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed (.view change) (Obs.dependencyModel child closed supplied)
  | .pad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (Obs.dependencyModel child closed supplied)
  | .unpad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).unpad (Obs.dependencyModel child closed supplied)
  | .rowShift child =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed (.view (.commutePadFn _ _))
      ((RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (Obs.dependencyModel child closed supplied))
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem CodeCert.dependencyModel
    (query : CodeCert env U registry target locals σ expression profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .seed child _ => exact Obs.dependencyModel child closed supplied
  | .union left right =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).union (CodeCert.dependencyModel left closed (suppliedLeft supplied))
      (CodeCert.dependencyModel right closed (suppliedRight supplied))
  | .pad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (CodeCert.dependencyModel child closed supplied)
  | .unpad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).unpad (CodeCert.dependencyModel child closed supplied)
  | .down child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed .down child.formed (CodeCert.dependencyModel child closed supplied)
  | .familyPad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed .familyPad child.formed (CodeCert.dependencyModel child closed supplied)
  | .map change child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.map change) child.formed (CodeCert.dependencyModel child closed supplied)
  | .select child member => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).select closed (CodeCert.dependencyModel child closed supplied) member
  | .focusMinimal child minimal bound =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.focusMinimal minimal bound) child.formed (CodeCert.dependencyModel child closed supplied)
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem PiRows.dependencyModel
    (query : PiRows env U registry target locals σ A B support rows footprint)
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
      exact CodeCert.dependencyModel body (recipeDependencyInputs.closed closed)
        (BinderPack.dependencySupply pack covered (suppliedLeft supplied))
    · exact PiRows.dependencyModel tail closed (suppliedRight supplied) key result member
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega
end

mutual
 theorem SortableCert.dependencyModel
    (query : SortableCert env U registry target locals σ expression relevant profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .ofCode child _ => exact CodeCert.dependencyModel child closed supplied
  | .observe child _ => exact SortableObs.dependencyModel child closed supplied
  | .seed child _ => exact Obs.dependencyModel child closed supplied
  | .pi domain guard rows =>
    exact piModel (SortableCert.dependencyModel domain closed (suppliedLeft supplied))
      (SortableRows.dependencyModel rows closed (suppliedRight supplied))
  | .union left right =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).union (SortableCert.dependencyModel left closed (suppliedLeft supplied))
      (SortableCert.dependencyModel right closed (suppliedRight supplied))
  | .pad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (SortableCert.dependencyModel child closed supplied)
  | .unpad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).unpad (SortableCert.dependencyModel child closed supplied)
  | .down child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed .down child.formed (SortableCert.dependencyModel child closed supplied)
  | .sortPad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed .sortPad child.formed (SortableCert.dependencyModel child closed supplied)
  | .familyPad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed .familyPad child.formed (SortableCert.dependencyModel child closed supplied)
  | .map change child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.map change) child.formed (SortableCert.dependencyModel child closed supplied)
  | .support change child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.support change) child.formed (SortableCert.dependencyModel child closed supplied)
  | .select child member => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).select closed (SortableCert.dependencyModel child closed supplied) member
  | .focusMinimal child minimal bound =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).code closed (.focusMinimal minimal bound) child.formed (SortableCert.dependencyModel child closed supplied)
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem SortableObs.dependencyModel
    (query : SortableObs env U registry target locals σ expression profile footprint)
    (closed : available.AtomClosed)
    (supplied : RecipeFootprintDependency env U registry target available footprint) :
    RecipeDependencyProfile env U registry target expression profile available := by
  match query with
  | .family .. | .app .. | .lam .. => simp only [RecipeDependencyProfile]
  | .legacy child => exact Obs.dependencyModel child closed supplied
  | .code _ child => exact SortableCert.dependencyModel child closed supplied
  | .union left right =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).union (SortableObs.dependencyModel left closed (suppliedLeft supplied))
      (SortableObs.dependencyModel right closed (suppliedRight supplied))
  | .view child change =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed (.view change) (SortableObs.dependencyModel child closed supplied)
  | .action child change =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed change (SortableObs.dependencyModel child closed supplied)
  | .pad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (SortableObs.dependencyModel child closed supplied)
  | .unpad child => exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).unpad (SortableObs.dependencyModel child closed supplied)
  | .rowShift child =>
    exact (RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).action closed (.view (.commutePadFn _ _))
      ((RecipeDependencyProfile.laws (env := env) (U := U) (registry := registry) (target := target) _).pad (SortableObs.dependencyModel child closed supplied))
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega

 theorem SortableRows.dependencyModel
    (query : SortableRows env U registry target locals σ A B relevant support rows footprint)
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
      exact SortableCert.dependencyModel body (recipeDependencyInputs.closed closed)
        (BinderPack.dependencySupply pack covered (suppliedLeft supplied))
    · exact SortableRows.dependencyModel tail closed (suppliedRight supplied) key result member
 termination_by sizeOf query
 decreasing_by all_goals simp_wf <;> omega
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
