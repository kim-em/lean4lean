import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiDomainPreservation

/-! Exact requested Pi domains, including empty rows, are extracted with the
same surviving query provenance and a bound for every head-depth policy. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
variable {strata : EquationStratification env} {budget : WorldPiDomainBudget strata}
variable {domainNode : EndpointState sourceEnv U source A (.sort u)}
variable {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}

private theorem domainCertificateAt
    {actualDomain : EndpointState sourceEnv U source A (.sort actualU)}
    {actualBody : EndpointState sourceEnv U (A :: source) B (.sort actualV)}
    (actualHu : actualU.WF U) (actualHv : actualV.WF U) (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B)
      (.pi actualHu actualHv actualDomain actualBody) (.pi hu hv domainNode bodyNode))
    (domain : RichCert sourceEnv env U registry target actualDomain locals σ true ambient domainFootprint)
    (annotation : WorldCertProvenance strata domain)
    (resources : domainFootprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, domain.headDepth policy ≤ budget.depth policy) :
    Nonempty (ControlledRichDomainCertificate env budget U registry target domainNode locals σ available ambient) := by
  have equal := (PrefixRoute.done (.pi actualHu actualHv actualDomain actualBody)).structural_unique
    (by trivial) route (by trivial)
  obtain ⟨_, _, _, _, huEq, _, hvEq, domainEq, bodyEq⟩ :=
    EndpointState.pi.hinj rfl rfl rfl rfl equal.1 equal.2
  cases huEq
  cases hvEq
  have domainEq := eq_of_heq domainEq
  have bodyEq := eq_of_heq bodyEq
  cases domainEq
  cases bodyEq
  exact ⟨⟨⟨_, domain, resources⟩, annotation, worlds, depth⟩⟩

mutual
theorem WorldCertProvenance.piDomainOrigins
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (annotation : WorldCertProvenance strata certificate)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, certificate.headDepth policy ≤ budget.depth policy) :
    WorldPiDomainDeferredOrigins env budget U registry target locals σ available domainNode bodyNode profile := by
  match annotation with
  | .legacy _ child =>
    intro atom member
    exact ⟨⟨_, atom, .native (child.piDomainOrigins resources worlds
      (fun policy => by simpa only [RichCert.headDepth, RichObs.headDepth] using depth policy) atom member), .refl⟩⟩
  | .recipe child =>
    intro atom member
    exact ⟨⟨_, atom, .recipe (.action (.select member) _) resources
      (.action (.select member) child) worlds
      (fun policy => by simpa only [RichCert.headDepth, RichCodeRecipe.headDepth] using depth policy), .refl⟩⟩
  | .observe child _ =>
    exact child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichCert.headDepth, RichObs.headDepth] using depth policy)
  | .pi actualHu actualHv domain guard rows domainAnnotation rowsAnnotation =>
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨⟨_, _, .native ?_, .refl⟩⟩
    exact domainCertificateAt actualHu actualHv hu hv route domain domainAnnotation
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun _ member => worlds (List.mem_append_left _ member))
      (fun policy => Nat.le_trans (Nat.le_max_left _ _) (by simpa only [RichCert.headDepth] using depth policy))
  | .route path child =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact child.piDomainOrigins hu hv suffix resources worlds
      (fun policy => by simpa only [RichCert.headDepth] using depth policy)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_left _ hm))
        (fun _ hm => worlds (List.mem_append_left _ hm))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (by simpa only [RichCert.headDepth] using depth policy)) atom member
    · exact right.piDomainOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun _ hm => worlds (List.mem_append_right _ hm))
        (fun policy => Nat.le_trans (Nat.le_max_right _ _) (by simpa only [RichCert.headDepth] using depth policy)) atom member
  | .pad (certificate := childCode) child =>
    exact WorldPiDomainDeferredOrigins.code .pad childCode.formed
      (child.piDomainOrigins hu hv route resources worlds
        (fun policy => by simpa only [RichCert.headDepth] using depth policy))
  | .down (certificate := childCode) child =>
    exact WorldPiDomainDeferredOrigins.code .down childCode.formed
      (child.piDomainOrigins hu hv route resources worlds
        (fun policy => by simpa only [RichCert.headDepth] using depth policy))
  | .support (certificate := childCode) action child =>
    exact WorldPiDomainDeferredOrigins.code (.support action) childCode.formed
      (child.piDomainOrigins hu hv route resources worlds
        (fun policy => by simpa only [RichCert.headDepth] using depth policy))
  | .map (certificate := childCode) change child =>
    exact WorldPiDomainDeferredOrigins.code (.map change) childCode.formed
      (child.piDomainOrigins hu hv route resources worlds
        (fun policy => by simpa only [RichCert.headDepth] using depth policy))
  | .select child member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichCert.headDepth] using depth policy) _ member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldObsProvenance.piDomainOrigins
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {observation : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata observation)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available)
    (worlds : annotation.worlds ⊆ budget.worlds)
    (depth : ∀ policy, observation.headDepth policy ≤ budget.depth policy) :
    WorldPiDomainDeferredOrigins env budget U registry target locals σ available domainNode bodyNode profile := by
  match annotation with
  | .empty =>
    exact fun _ member => nomatch member
  | .legacy _ child =>
    intro atom member
    exact ⟨⟨_, atom, .native (child.piDomainOrigins resources worlds
      (fun policy => by simpa only [RichCert.headDepth, RichObs.headDepth] using depth policy) atom member), .refl⟩⟩
  | .code child =>
    exact child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy)
  | .route path child =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact child.piDomainOrigins hu hv suffix resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piDomainOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_left _ hm))
        (fun _ hm => worlds (List.mem_append_left _ hm))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (by simpa only [RichObs.headDepth] using depth policy)) atom member
    · exact right.piDomainOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun _ hm => worlds (List.mem_append_right _ hm))
        (fun policy => Nat.le_trans (Nat.le_max_right _ _) (by simpa only [RichObs.headDepth] using depth policy)) atom member
  | .action child action =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path action }⟩
  | .view child change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .select child member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy) _ member
  | .pad child =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy) old present
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad child =>
    intro atom member
    obtain ⟨origin⟩ := child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth] using depth policy) (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
  | .castProfile equal child =>
    have previous := child.piDomainOrigins hu hv route resources worlds
      (fun policy => by
        have bounded := depth policy
        rw [RichObs.headDepth_mp policy rfl rfl equal rfl] at bounded
        exact bounded)
    exact equal ▸ previous
  | .lowerRaised (profile := profile) (N := N) (bound := bound) child =>
    intro atom member
    have oldMember : raiseAtom N bound atom ∈ (raiseProfile N bound profile).atoms := by
      have selected : List.Subset (Profile.singleton atom).atoms profile.atoms := by
        intro a present
        cases List.mem_singleton.mp present
        exact member
      apply raiseProfile_subset bound selected
      simp only [raiseProfile_singleton]
      exact List.mem_singleton_self _
    obtain ⟨origin⟩ := child.piDomainOrigins hu hv route resources worlds
      (fun policy => by simpa only [RichObs.headDepth_lowerRaised] using depth policy) _ oldMember
    exact ⟨{ origin with path := GeneralOutputPath.lowerRaisedPi bound origin.path }⟩
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega
end

/-- One computed domain certificate at exactly the requested support, including
empty row tables. Its annotation is extracted along the same actual visitor. -/
theorem RichCert.piDomain_controlled
    {support : Profile n} {rows : List (Key n × Profile n)}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.pi prototypeDomain prototypeBody support rows) footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available)
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ result : RichDomainCertificate env U registry target domainNode locals σ available support,
      ∃ output : ControlledStoredQuery controls frontier (.certificate result.certificate),
        output.annotation.worlds ⊆ ready.annotation.worlds ∧
        ∀ policy, result.certificate.headDepth policy ≤ certificate.headDepth policy := by
  let budget : WorldPiDomainBudget strata := ⟨ready.annotation.worlds, fun policy => certificate.headDepth policy⟩
  obtain ⟨origin⟩ := ready.annotation.piDomainOrigins (budget := budget) hu hv route resources
    (fun _ member => member) (fun _ => Nat.le_refl _) _ (List.mem_singleton_self _)
  obtain ⟨result⟩ := origin.resolve
  refine ⟨result.toRichDomainCertificate, ⟨result.annotation, ?_, ?_⟩, result.worlds_subset, result.depth_le⟩
  · intro control active
    exact Nat.le_trans (result.depth_le _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (result.worlds_subset member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
