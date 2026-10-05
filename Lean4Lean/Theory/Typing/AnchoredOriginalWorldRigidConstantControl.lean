import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantObservation

/-! Recover the exact stored rigid-header annotation from an arbitrary
annotation of the shared leaf. Stored site controls are not assumed to agree
with the caller: child fuel comes from the actual outer query bound, while its
nested sponsorship is the literal subset of the original annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def RichObs.RigidHeaderAnnotation
    {strata : EquationStratification env}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (worlds : List (World strata.rules.length)) : Prop :=
  match query with
  | .rigidFamily (name := name) (levels := levels) (node := node)
      _ _ _ _ _ _ _ _ _ _ _ certificate _ _ =>
      ∃ child : WorldCertProvenance strata certificate, child.worlds ⊆ worlds
  | _ => True

private theorem rigidHeaderAnnotation_cast
    {strata : EquationStratification env}
    {profile next : Profile n} (equal : profile = next)
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    {worlds : List (World strata.rules.length)}
    (present : query.RigidHeaderAnnotation worlds) :
    ((congrArg (fun p => RichObs sourceEnv env U registry target node locals σ p footprint)
      equal).mp query).RigidHeaderAnnotation worlds := by
  cases equal
  exact present

private theorem rigidHeaderAnnotation_lowerRaised
    {strata : EquationStratification env}
    {n N : Nat} {profile : Profile n} {bound : n ≤ N}
    (query : RichObs sourceEnv env U registry target node locals σ
      (raiseProfile N bound profile) footprint)
    {worlds : List (World strata.rules.length)}
    (present : query.RigidHeaderAnnotation worlds) :
    query.lowerRaised.RigidHeaderAnnotation worlds := by
  induction N generalizing n with
  | zero =>
    have same : n = 0 := by omega
    subst n
    exact present
  | succ N ih =>
    by_cases same : n = N + 1
    · subst n
      simp only [RichObs.lowerRaised, dif_pos]
      exact rigidHeaderAnnotation_cast (by rw [raiseProfile_self]) _ present
    · have previous : n ≤ N := by omega
      simp only [RichObs.lowerRaised, dif_neg same]
      apply ih
      trivial

private theorem WorldObsProvenance.rigidHeaderAnnotation
    {strata : EquationStratification env}
    {query : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (annotation : WorldObsProvenance strata query) :
    query.RigidHeaderAnnotation annotation.worlds :=
  match annotation with
  | .rigidFamily (name := name) (levels := levels) (node := node)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ child _ _ =>
      ⟨child, fun _ member => List.mem_append_right _ member⟩
  | .castProfile equal child =>
      rigidHeaderAnnotation_cast equal _ child.rigidHeaderAnnotation
  | .lowerRaised child =>
      rigidHeaderAnnotation_lowerRaised _ child.rigidHeaderAnnotation
  | .var | .empty | .sort _ | .canonicalDelta .. | .canonicalConst .. | .code ..
    | .projection .. | .projectionSortable .. | .app .. | .route .. | .union .. | .view .. | .action ..
    | .select .. | .pad .. | .unpad .. | .family .. | .constructor .. | .legacy .. | .lam .. => True.intro
termination_by structural annotation

/-- Exact child readiness is obtained from the full leaf's actual annotation,
including profile casts and zero-step lowering. A stored site's independently
chosen controls are irrelevant to this newly funded opening. -/
noncomputable def RichRigidConstantInput.certificateControlled
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (ready : ControlledStoredQuery controls frontier (.observation (input.observation node locals σ))) :
    ControlledStoredQuery (controls.atHeader input.origin) frontier (.certificate input.certificate) := by
  have extracted := ready.annotation.rigidHeaderAnnotation
  let annotation := Classical.choose extracted
  have contained := Classical.choose_spec extracted
  exact {
    annotation := annotation
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichRigidConstantInput.observation,
        RichObs.headDepth, OriginalWorldControls.atHeader] using ready.within control active
    sponsored := fun world member => ready.sponsored world (contained member) }

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
