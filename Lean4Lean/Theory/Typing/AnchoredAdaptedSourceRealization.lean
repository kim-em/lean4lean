import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Finite source realization congruence. Native observations keep their
original internal telescope and descendants; the ambient substitution cannot
change a bare constant. -/
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
noncomputable def Obs.realizePrefix
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (scope : expression.ClosedN count) (τ : Subst)
    (agree : ∀ i < count, σ i = τ i) :
    Obs env U registry Γ locals τ expression demand footprint := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    exact .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    exact .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    exact .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree
  | .var locals _ i demand => exact .var locals τ i demand
  | .empty => exact .empty
  | .sort relevant => exact .sort relevant
  | .app fn arg arguments admitted =>
    have he := subst_congr_closedN scope.2 agree
    exact .app (fn.realizePrefix scope.1 τ agree) (arg.realizePrefix scope.2 τ agree)
      arguments (he ▸ admitted)
  | .lam domain guard body normal covered =>
    exact .lam (domain.realizePrefix scope.1 τ agree)
      (guard_realize guard scope.1 agree)
      (body.realizePrefix scope.2 _ (agree_cons agree _)) normal covered
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
  | .union left right => exact .union (left.realizePrefix scope τ agree) (right.realizePrefix scope τ agree)
  | .view source view => exact .view (source.realizePrefix scope τ agree) view
  | .pad source => exact .pad (source.realizePrefix scope τ agree)
  | .unpad source => exact .unpad (source.realizePrefix scope τ agree)
  | .rowShift source => exact .rowShift (source.realizePrefix scope τ agree)
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

noncomputable def CodeCert.realizePrefix
    (certificate : CodeCert env U registry Γ locals σ expression demand footprint)
    (scope : expression.ClosedN count) (τ : Subst)
    (agree : ∀ i < count, σ i = τ i) :
    CodeCert env U registry Γ locals τ expression demand footprint := by
  match certificate with
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
decreasing_by all_goals simp_wf; omega

noncomputable def PiRows.realizePrefix
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    (scopeA : A.ClosedN count) (scopeB : B.ClosedN (count + 1)) (τ : Subst)
    (agree : ∀ i < count, σ i = τ i) :
    PiRows env U registry Γ locals τ A B ambient rows footprint := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    exact .cons (guard_realize guard scopeA agree)
      (body.realizePrefix scopeB _ (agree_cons agree _)) normal covered
      (tail.realizePrefix scopeA scopeB τ agree)
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega

noncomputable def FamilyCaptures.realizePrefix
    (captures : FamilyCaptures env U registry Γ source locals σ expressions keys footprint)
    (scope : CtxClosed source) (τ : Subst)
    (agree : ∀ i < source.length, σ i = τ i) :
    FamilyCaptures env U registry Γ source locals τ expressions keys footprint := by
  match captures with
  | .nil => exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    have he := subst_congr_closedN (scope.lookup lookup) agree
    exact .cons lookup (value.realizePrefix lookup.lt τ agree) adapter (he ▸ alignment)
      (agree _ lookup.lt ▸ anchor) (tail.realizePrefix scope τ agree)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega
end


end Lean4Lean.AnchoredSource.Adapted
