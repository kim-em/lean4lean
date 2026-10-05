import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDeferredOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiRowPreservation

/-! Pi-origin traversal retains native rows or charged recipe leaves together
with their exact finite output paths. Requested rows are resolved using the
actual whole-Pi interpretation and actual argument admission. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
variable {domainNode : EndpointState sourceEnv U source A (.sort u)}
variable {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}

private theorem rowCertificateAt
    {actualDomain : EndpointState sourceEnv U source A (.sort actualU)}
    {actualBody : EndpointState sourceEnv U (A :: source) B (.sort actualV)}
    (actualHu : actualU.WF U) (actualHv : actualV.WF U) (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B)
      (.pi actualHu actualHv actualDomain actualBody) (.pi hu hv domainNode bodyNode))
    (domain : RichCert sourceEnv env U registry target actualDomain locals σ true ambient domainFootprint)
    {rows : RichRows sourceEnv env U registry target actualDomain actualBody locals σ relevant ambient table footprint}
    (annotation : WorldRowsProvenance strata rows)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domain))
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (member : (key, result) ∈ table) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      Nonempty (row.Controlled controls frontier) := by
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
  exact annotation.selectPiRow domain domainReady domainAvailable resources within sponsored member

section
variable
  (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
  (closed : available.AtomClosed)
  (reanchorRow : ∀ {relevant : Bool} {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
    (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) →
    row.Controlled controls frontier →
    Admitted env U registry target key anchor anchor →
    ∃ next : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
      (reanchorKey key anchor) result, Nonempty (next.Controlled controls frontier))
include henv hscoped hTarget closed reanchorRow

mutual
theorem WorldCertProvenance.piRowOrigins
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (annotation : WorldCertProvenance strata certificate)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available)
    (worlds : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (depth : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WorldPiDeferredOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
  match annotation with
  | .legacy _ child =>
    intro atom member
    exact ⟨⟨_, atom, .native (child.piRowOrigins henv hscoped hTarget closed reanchorRow resources worlds
      (fun control active => by simpa only [RichCert.headDepth, RichObs.headDepth] using depth control active) atom member), .refl⟩⟩
  | .recipe child =>
    intro atom member
    exact ⟨⟨_, atom, .recipe (.action (.select member) _)
      (.action (.select member) child) resources worlds
      (fun control active => by
        simpa only [RichCert.headDepth, RichCodeRecipe.headDepth] using depth control active), .refl⟩⟩
  | .observe child _ =>
    exact child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichCert.headDepth, RichObs.headDepth] using depth control active)
  | .pi actualHu actualHv domain guard rows domainAnnotation rowsAnnotation =>
    intro atom member
    cases List.mem_singleton.mp member
    refine ⟨⟨_, _, .native ?_, .refl⟩⟩
    intro key result selected
    obtain ⟨row, ready⟩ := rowCertificateAt actualHu actualHv hu hv route domain rowsAnnotation
      ⟨domainAnnotation,
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active)),
        (fun world member => worlds world (List.mem_append_left _ member))⟩
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
      (fun control active => Nat.le_trans (Nat.le_max_right _ _) (by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active))
      (fun world member => worlds world (List.mem_append_right _ member)) selected
    exact ⟨_, row, ready⟩
  | .route path child =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact child.piRowOrigins hu hv suffix resources worlds
      (fun control active => by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piRowOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_left _ hm))
        (fun _ hm => worlds _ (List.mem_append_left _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active)) atom member
    · exact right.piRowOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun _ hm => worlds _ (List.mem_append_right _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active)) atom member
  | .pad (certificate := childCode) child =>
    exact WorldPiDeferredOrigins.code .pad childCode.formed
      (child.piRowOrigins hu hv route resources worlds
        (fun control active => by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active))
  | .down (certificate := childCode) child =>
    exact WorldPiDeferredOrigins.code .down childCode.formed
      (child.piRowOrigins hu hv route resources worlds
        (fun control active => by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active))
  | .support (certificate := childCode) action child =>
    exact WorldPiDeferredOrigins.code (.support action) childCode.formed
      (child.piRowOrigins hu hv route resources worlds
        (fun control active => by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active))
  | .map (certificate := childCode) change child =>
    exact WorldPiDeferredOrigins.code (.map change) childCode.formed
      (child.piRowOrigins hu hv route resources worlds
        (fun control active => by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active))
  | .select child member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using depth control active) _ member
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

theorem WorldObsProvenance.piRowOrigins
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {observation : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata observation)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available)
    (worlds : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (depth : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => observation.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    WorldPiDeferredOrigins env controls frontier U registry target locals σ available domainNode bodyNode profile := by
  match annotation with
  | .empty =>
    exact fun _ member => nomatch member
  | .legacy _ child =>
    intro atom member
    exact ⟨⟨_, atom, .native (child.piRowOrigins henv hscoped hTarget closed reanchorRow resources worlds
      (fun control active => by simpa only [RichCert.headDepth, RichObs.headDepth] using depth control active) atom member), .refl⟩⟩
  | .code child =>
    exact child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active)
  | .route path child =>
    obtain ⟨suffix⟩ := PrefixRoute.structuralSuffix path route (by trivial)
    exact child.piRowOrigins hu hv suffix resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piRowOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_left _ hm))
        (fun _ hm => worlds _ (List.mem_append_left _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_left _ _) (by simpa only [RichObs.headDepth] using depth control active)) atom member
    · exact right.piRowOrigins hu hv route
        (fun i need hm => resources i need (List.mem_append_right _ hm))
        (fun _ hm => worlds _ (List.mem_append_right _ hm))
        (fun control active => Nat.le_trans (Nat.le_max_right _ _) (by simpa only [RichObs.headDepth] using depth control active)) atom member
  | .action child action =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active)
      _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path action }⟩
  | .view child change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active)
      _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .select child member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active) _ member
  | .pad child =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active) old present
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad child =>
    intro atom member
    obtain ⟨origin⟩ := child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth] using depth control active)
      (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
  | .castProfile equal child =>
    have previous := child.piRowOrigins hu hv route resources worlds
      (fun control active => by
        have bounded := depth control active
        dsimp only at bounded
        rw [RichObs.headDepth_mp _ rfl rfl equal rfl] at bounded
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
    obtain ⟨origin⟩ := child.piRowOrigins hu hv route resources worlds
      (fun control active => by simpa only [RichObs.headDepth_lowerRaised] using depth control active)
      _ oldMember
    exact ⟨{ origin with path := GeneralOutputPath.lowerRaisedPi bound origin.path }⟩
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega
end

/-- Resolve the requested row and retain its exact domain/body annotations.
Charged leaves compute domain alignment from the interpreted whole Pi; their
body keeps the explicit binder demand and the original root charge. -/
theorem RichCert.piRow_controlled
    {n : Nat} {profile : Profile (n + 1)} {support : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (hu : u.WF U) (hv : v.WF U)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode bodyNode))
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (atomMember : (.pi prototypeDomain prototypeBody support rows) ∈ profile.atoms)
    (rowMember : (key, result) ∈ rows)
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      (.forallE C D) profile)
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      Nonempty (row.Controlled controls frontier) := by
  obtain ⟨origin⟩ := ready.annotation.piRowOrigins henv hscoped hTarget closed reanchorRow hu hv route resources
    ready.sponsored ready.within _ atomMember
  have sorted := certificate.formed.singleton_of_mem atomMember
  have selectedWhole := (SortableCodeAction.select (relevant := relevant) atomMember).codeMap henv hscoped whole
  exact origin.resolve henv hscoped hTarget closed reanchorRow selectedWhole sorted rowMember admitted

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
