import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationDomainBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalLocatedDirect
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationLineage

/-! The first family argument's domain query is reconstructed at the actual
function formation, then replayed through its original constant prefix to
the earlier declaration header. Both recursive ledgers are finite original
calls; neither declaration-domain equality nor a source code supplier is
assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem firstFamilyHeaderLeft
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    {node : EndpointState sourceEnv U source (.app (.const name levels) argument) assigned}
    {start : Located root node} (app : ApplicationPrefix start)
    (pi : PiPrefix (Located.assignedFormation (Located.appFunction app.view.location)))
    (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (otherWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (route : DirectPrefixRoute sourceEnv U source (.const name levels) app.view.function
      (.ref (.left (.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient))))
    (captured : List Closure)
    (calls : route.PeelCalls env registry target ordered captured locals σ available)
    (domainR : richSchedule .expressionReindex
      ((Closure.close (app.view.domain.dependencyOrigin ordered) captured).cost +
       (Closure.close (pi.view.domain.dependencyOrigin ordered) captured).cost) <
      richSchedule .fundamental (Closure.close (node.dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target app.view.domain pi.view.domain locals locals σ σ available available)
    (headerR : richSchedule .expressionReindex
      ((Closure.close (ambient.dependencyOrigin ordered) captured).cost +
       (Closure.close ((selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
         (selectOriginalHeader ordered lookup levelsWF).ordered) []).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
          captured).cost →
      RichCodeTransfer env U registry target (.ref (.left ambient))
        (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
        locals [] σ headerRealization available (fun _ => []))
    (certificate : RichCert sourceEnv env U registry target app.view.domain locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (RichCodeTransferResult env U registry target app.view.function.typeFormation.node
      (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original)) [] σ headerRealization (fun _ => []) true
      (Profile.pi (app.view.domainExpression.subst σ) (app.view.codomainExpression.subst σ.lift) support [])) := by
  obtain ⟨seedFootprint, ⟨seed⟩, seedResources⟩ :=
    AppView.seedFunctionPi ordered app pi captured certificate resources domainR
  obtain ⟨answer⟩ := route.replayConstantLeftPrefix henv ordered lookup levelsWF otherWF count equivalent
    levelWF closed ambient captured calls headerR seed seedResources
  exact ⟨answer⟩

theorem firstFamilyHeaderRight
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    {node : EndpointState sourceEnv U source (.app (.const name otherLevels) argument) assigned}
    {start : Located root node} (app : ApplicationPrefix start)
    (pi : PiPrefix (Located.assignedFormation (Located.appFunction app.view.location)))
    (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (otherWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (route : DirectPrefixRoute sourceEnv U source (.const name otherLevels) app.view.function
      (.ref (.right (.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient))))
    (captured : List Closure)
    (calls : route.PeelCalls env registry target ordered captured locals σ available)
    (domainR : richSchedule .expressionReindex
      ((Closure.close (app.view.domain.dependencyOrigin ordered) captured).cost +
       (Closure.close (pi.view.domain.dependencyOrigin ordered) captured).cost) <
      richSchedule .fundamental (Closure.close (node.dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target app.view.domain pi.view.domain locals locals σ σ available available)
    (headerR : richSchedule .expressionReindex
      ((Closure.close (ambient.dependencyOrigin ordered) captured).cost +
       (Closure.close ((selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
         (selectOriginalHeader ordered lookup levelsWF).ordered) []).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
          captured).cost →
      RichCodeTransfer env U registry target (.ref (.left ambient))
        (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
        locals [] σ headerRealization available (fun _ => []))
    (certificate : RichCert sourceEnv env U registry target app.view.domain locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (RichCodeTransferResult env U registry target app.view.function.typeFormation.node
      (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original)) [] σ headerRealization (fun _ => []) true
      (Profile.pi (app.view.domainExpression.subst σ) (app.view.codomainExpression.subst σ.lift) support [])) := by
  obtain ⟨seedFootprint, ⟨seed⟩, seedResources⟩ :=
    AppView.seedFunctionPi ordered app pi captured certificate resources domainR
  obtain ⟨answer⟩ := route.replayConstantRightPrefix henv ordered lookup levelsWF otherWF count equivalent
    levelWF closed ambient captured calls headerR seed seedResources
  exact ⟨answer⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
