import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRealization

/-! Realization congruence for hereditary certificates uses only the actual
finite scope of the expression. Closed family plans retain their own tuples. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
private theorem agree_cons {σ τ : Subst}
    (agree : ∀ i < count, σ i = τ i) (anchor : VExpr) :
    ∀ i < count + 1, σ.cons anchor i = τ.cons anchor i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact agree i (by omega)

private theorem guard_realize
    (guard : LambdaGuard env U registry Γ σ A key support)
    (scope : A.ClosedN count) (agree : ∀ i < count, σ i = τ i) :
    LambdaGuard env U registry Γ τ A key support := by
  have he := subst_congr_closedN scope agree
  exact ⟨guard.inputTyped, guard.formed, he ▸ guard.path, he ▸ guard.domains, guard.anchor⟩

mutual
noncomputable def SortableObs.realizePrefix
    (observation : SortableObs env U registry Γ locals σ expression demand footprint)
    (scope : expression.ClosedN count) (τ : Subst)
    (agree : ∀ i < count, σ i = τ i) :
    SortableObs env U registry Γ locals τ expression demand footprint := by
  match observation with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    exact .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree
  | .legacy observation => exact .legacy (observation.realizePrefix scope τ agree)
  | .code relevant certificate => exact .code relevant (certificate.realizePrefix scope τ agree)
  | .action source action => exact .action (source.realizePrefix scope τ agree) action
  | .app fn arg arguments admitted =>
    have he := subst_congr_closedN scope.2 agree
    exact .app (fn.realizePrefix scope.1 τ agree) (arg.realizePrefix scope.2 τ agree)
      arguments (he ▸ admitted)
  | .lam domain guard body normal covered =>
    exact .lam (domain.realizePrefix scope.1 τ agree)
      (guard_realize guard scope.1 agree)
      (body.realizePrefix scope.2 _ (agree_cons agree _)) normal covered
  | .union left right => exact .union (left.realizePrefix scope τ agree) (right.realizePrefix scope τ agree)
  | .view source view => exact .view (source.realizePrefix scope τ agree) view
  | .pad source => exact .pad (source.realizePrefix scope τ agree)
  | .unpad source => exact .unpad (source.realizePrefix scope τ agree)
  | .rowShift source => exact .rowShift (source.realizePrefix scope τ agree)
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

noncomputable def SortableCert.realizePrefix
    (certificate : SortableCert env U registry Γ locals σ expression relevant demand footprint)
    (scope : expression.ClosedN count) (τ : Subst)
    (agree : ∀ i < count, σ i = τ i) :
    SortableCert env U registry Γ locals τ expression relevant demand footprint := by
  match certificate with
  | .pi domain guard bodies =>
    have ha := subst_congr_closedN scope.1 agree
    have hb : _ = _ := subst_congr_closedN scope.2 (σ := σ.lift) (σ' := τ.lift) (by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.lift]; rw [agree i (by omega)])
    exact .pi (domain.realizePrefix scope.1 τ agree)
      ⟨ha ▸ guard.domainPath, ha ▸ hb ▸ guard.bodyPath⟩
      (bodies.realizePrefix scope.1 scope.2 τ agree)
  | .ofCode source formed => exact .ofCode (source.realizePrefix scope τ agree) formed
  | .observe observation formed => exact .observe (observation.realizePrefix scope τ agree) formed
  | .sortPad source => exact .sortPad (source.realizePrefix scope τ agree)
  | .support action source => exact .support action (source.realizePrefix scope τ agree)
  | .seed observation formed => exact .seed (observation.realizePrefix scope τ agree) formed
  | .union left right => exact .union (left.realizePrefix scope τ agree) (right.realizePrefix scope τ agree)
  | .pad source => exact .pad (source.realizePrefix scope τ agree)
  | .familyPad source => exact .familyPad (source.realizePrefix scope τ agree)
  | .unpad source => exact .unpad (source.realizePrefix scope τ agree)
  | .down source => exact .down (source.realizePrefix scope τ agree)
  | .map view source => exact .map view (source.realizePrefix scope τ agree)
  | .select source member => exact .select (source.realizePrefix scope τ agree) member
  | .focusMinimal source minimal bound => exact .focusMinimal (source.realizePrefix scope τ agree) minimal bound
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

noncomputable def SortableRows.realizePrefix
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint)
    (scopeA : A.ClosedN count) (scopeB : B.ClosedN (count + 1)) (τ : Subst)
    (agree : ∀ i < count, σ i = τ i) :
    SortableRows env U registry Γ locals τ A B relevant ambient rows footprint := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    exact .cons (guard_realize guard scopeA agree)
      (body.realizePrefix scopeB _ (agree_cons agree _)) normal covered
      (tail.realizePrefix scopeA scopeB τ agree)
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)

end

end Lean4Lean.AnchoredSource.Adapted
