import Lean4Lean.Theory.Typing.AnchoredOriginalGenericLambda
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalReplay

/-! Replay the full lambda query grammar while preserving both computational
channels, including original assigned certificates through every action. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: source) b B}
    {destination : EndpointState rightEnv U rightSource destinationExpression destinationType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (primitive : ∀ {n : Nat} {ambient : Profile n} {key : Key n} {output : Atom n}
      {domainFootprint bodyFootprint outside : Footprint} {packed : Profile n},
      RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint →
      LambdaGuard env U registry target σ A key ambient →
      RichObs sourceEnv env U registry target body (Locals.push locals) (σ.cons key.anchor)
        (.singleton output) bodyFootprint →
      BinderPack n packed bodyFootprint outside →
      (∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) →
      domainFootprint.Available available → outside.Available available →
      Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable
        (Profile.fn key output)))
include henv hscoped formed primitive

mutual
theorem _root_.Lean4Lean.AnchoredSource.Adapted.Obs.replayComputationalLambda
    (observation : Obs env U registry target locals σ (.lam A b) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable profile) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domainCode guard query pack covered =>
    exact primitive (.legacy (.ofCode domainCode domainCode.formed)) guard (.legacy (.legacy query)) pack covered
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
  | .union left right =>
    obtain ⟨a⟩ := left.replayComputationalLambda (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayComputationalLambda (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.unpad henv formed⟩
  | .view source view =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.action henv hscoped formed (.view view)
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact (answer.pad henv hscoped formed).action henv hscoped formed (.view (.commutePadFn key output))
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem _root_.Lean4Lean.AnchoredSource.Adapted.CodeCert.replayComputationalLambda
    (certificate : CodeCert env U registry target locals σ (.lam A b) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable profile) := by
  match certificate with
  | .seed source _ => exact source.replayComputationalLambda resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayComputationalLambda (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayComputationalLambda (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.unpad henv formed⟩
  | .familyPad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed .familyPad source.formed
  | .down source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed .down source.formed
  | .map view source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.map view) source.formed
  | .select source member =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.select member) source.formed
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.focusMinimal minimal bound) source.formed
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableObs.replayComputationalLambda
    (observation : SortableObs env U registry target locals σ (.lam A b) profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable profile) := by
  match observation with
  | .legacy source => exact source.replayComputationalLambda resources
  | .code _ source => exact source.replayComputationalLambda resources
  | .lam domainCode guard query pack covered =>
    exact primitive (.legacy domainCode) guard (.legacy query) pack covered
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
  | .union left right =>
    obtain ⟨a⟩ := left.replayComputationalLambda (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayComputationalLambda (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.unpad henv formed⟩
  | .view source view =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.action henv hscoped formed (.view view)
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact (answer.pad henv hscoped formed).action henv hscoped formed (.view (.commutePadFn key output))
  | .action source action =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.action henv hscoped formed action
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.replayComputationalLambda
    (certificate : SortableCert env U registry target locals σ (.lam A b) relevant profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable profile) := by
  match certificate with

  | .ofCode source _ => exact source.replayComputationalLambda resources
  | .observe source _ => exact source.replayComputationalLambda resources
  | .seed source _ => exact source.replayComputationalLambda resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayComputationalLambda (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayComputationalLambda (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact ⟨answer.unpad henv formed⟩
  | .familyPad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed .familyPad source.formed
  | .down source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed .down source.formed
  | .map view source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.map view) source.formed
  | .select source member =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.select member) source.formed
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.focusMinimal minimal bound) source.formed
  | .sortPad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed .sortPad source.formed
  | .support action source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda resources
    exact answer.codeAdapter henv hscoped formed (.support action) source.formed
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

private theorem replayComputationalNativeLambdaAt
    {actualDomain : EndpointState sourceEnv U source A (.sort actualU)}
    {actualCodomain : EndpointState sourceEnv U (A :: source) actualB (.sort actualV)}
    {actualBody : EndpointState sourceEnv U (A :: source) b actualB}
    (actualHu : actualU.WF U) (actualHv : actualV.WF U) (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.lam A b)
      (.lam actualHu actualHv actualDomain actualCodomain actualBody) (.lam hu hv domain codomain body))
    (domainCode : RichCert sourceEnv env U registry target actualDomain locals σ true (ambient : Profile n) domainFootprint)
    (guard : LambdaGuard env U registry target σ A (key : Key n) ambient)
    {output : Atom n}
    (query : RichObs sourceEnv env U registry target actualBody (Locals.push locals) (σ.cons key.anchor)
      (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (resources : outside.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable
      (Profile.fn key output)) := by
  have equal := (PrefixRoute.done (.lam actualHu actualHv actualDomain actualCodomain actualBody)).structural_unique
    (by trivial) route (by trivial)
  obtain ⟨_, _, _, _, huEq, assignedEq, hvEq, _, domainEq, codomainEq, bodyEq⟩ :=
    EndpointState.lam.hinj rfl rfl rfl rfl equal.1 equal.2
  cases huEq
  cases assignedEq
  cases hvEq
  have domainEq := eq_of_heq domainEq
  have codomainEq := eq_of_heq codomainEq
  have bodyEq := eq_of_heq bodyEq
  cases domainEq
  cases codomainEq
  cases bodyEq
  exact primitive domainCode guard query pack covered domainAvailable resources

mutual
theorem RichCert.replayComputationalLambda
    {node : EndpointState sourceEnv U source (.lam A b) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.lam A b) node (.lam hu hv domain codomain body))
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable profile) := by
  match certificate with
  | .legacy source => exact source.replayComputationalLambda henv hscoped formed primitive resources
  | .observe source _ => exact source.replayComputationalLambda hu hv route resources

  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.replayComputationalLambda hu hv suffix resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayComputationalLambda hu hv route (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayComputationalLambda hu hv route (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .down source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact answer.codeAdapter henv hscoped formed .down source.formed
  | .map view source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact answer.codeAdapter henv hscoped formed (.map view) source.formed
  | .support action source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact answer.codeAdapter henv hscoped formed (.support action) source.formed
  | .select source member =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact answer.codeAdapter henv hscoped formed (.select member) source.formed
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.replayComputationalLambda
    {node : EndpointState sourceEnv U source (.lam A b) assigned}
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.lam A b) node (.lam hu hv domain codomain body))
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue rightEnv env U registry target destination rightLocals destinationLeft τ rightAvailable profile) := by
  match observation with
  | .legacy source => exact source.replayComputationalLambda henv hscoped formed primitive resources
  | .code source => exact source.replayComputationalLambda hu hv route resources
  | .lam actualHu actualHv domainCode guard query pack covered =>
    exact replayComputationalNativeLambdaAt henv hscoped formed primitive actualHu actualHv hu hv route domainCode guard query pack covered
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
  | .route path source =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact source.replayComputationalLambda hu hv suffix resources
  | .union left right =>
    obtain ⟨a⟩ := left.replayComputationalLambda hu hv route (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.replayComputationalLambda hu hv route (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped formed b⟩
  | .pad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact ⟨answer.pad henv hscoped formed⟩
  | .unpad source =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact ⟨answer.unpad henv formed⟩
  | .view source view =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact answer.action henv hscoped formed (.view view)
  | .action source action =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact answer.action henv hscoped formed action
  | .select source member =>
    obtain ⟨answer⟩ := source.replayComputationalLambda hu hv route resources
    exact ⟨answer.restrict (fun atom present => (List.mem_singleton.mp present) ▸ member)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

end
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
