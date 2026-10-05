import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSpine

/-! Exact native projection leaves through all rich code and value wrappers.
Each retained head carries a finite original route, and each output atom
carries its concrete generalized action path. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem codeNoAtom
    (action : SortableCodeAction env U registry target relevant p next q)
    (none : ∀ a ∈ p.atoms, False) (member : b ∈ q.atoms) : False := by
  obtain ⟨a, ha, _⟩ := action.atom member
  exact none a ha

mutual
private theorem CodeCert.projectionNoAtom
    {demand : Profile n}
    (query : CodeCert env U registry target locals σ (.proj name index value) demand footprint)
    (member : atom ∈ demand.atoms) : False := by
  match n, demand, footprint, query with
  | _, _, _, .seed source _ => rw [legacyProjectionEmpty source] at member; cases member
  | _, _, _, .union left right =>
    exact (List.mem_append.mp member).elim (left.projectionNoAtom) (right.projectionNoAtom)
  | _, _, _, .pad source =>
    obtain ⟨a, ha, _⟩ := List.mem_map.mp member
    exact source.projectionNoAtom ha
  | _, _, _, .unpad source =>
    exact source.projectionNoAtom (List.mem_map.mpr ⟨_, member, rfl⟩)
  | _, _, _, .familyPad source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) .familyPad (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .down source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) .down (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .map view source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) (.map view) (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .select source selected => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) (.select selected) (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .focusMinimal source minimal bound => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := true) (.focusMinimal minimal bound) (fun _ h => source.projectionNoAtom h) member
termination_by sizeOf query
decreasing_by all_goals (simp_wf <;> omega)

private theorem SortableObs.projectionNoAtom
    {demand : Profile n}
    (query : SortableObs env U registry target locals σ (.proj name index value) demand footprint)
    (member : atom ∈ demand.atoms) : False := by
  match n, demand, footprint, query with
  | _, _, _, .legacy source => rw [legacyProjectionEmpty source] at member; cases member
  | _, _, _, .code _ source => exact source.projectionNoAtom member
  | _, _, _, .union left right =>
    exact (List.mem_append.mp member).elim (left.projectionNoAtom) (right.projectionNoAtom)
  | _, _, _, .pad source =>
    obtain ⟨a, ha, _⟩ := List.mem_map.mp member
    exact source.projectionNoAtom ha
  | _, _, _, .unpad source =>
    exact source.projectionNoAtom (List.mem_map.mpr ⟨_, member, rfl⟩)
  | _, _, _, .view source _ | _, _, _, .action source _ | _, _, _, .rowShift source =>
    exact source.projectionNoAtom (List.mem_singleton_self _)
termination_by sizeOf query
decreasing_by all_goals (simp_wf <;> omega)

private theorem SortableCert.projectionNoAtom
    {demand : Profile n}
    (query : SortableCert env U registry target locals σ (.proj name index value) relevant demand footprint)
    (member : atom ∈ demand.atoms) : False := by
  match n, demand, footprint, query with
  | _, _, _, .ofCode source _ => exact source.projectionNoAtom member
  | _, _, _, .observe source _ => exact source.projectionNoAtom member
  | _, _, _, .seed source _ => rw [legacyProjectionEmpty source] at member; cases member
  | _, _, _, .union left right =>
    exact (List.mem_append.mp member).elim (left.projectionNoAtom) (right.projectionNoAtom)
  | _, _, _, .pad source =>
    obtain ⟨a, ha, _⟩ := List.mem_map.mp member
    exact source.projectionNoAtom ha
  | _, _, _, .unpad source =>
    exact source.projectionNoAtom (List.mem_map.mpr ⟨_, member, rfl⟩)
  | _, _, _, .familyPad source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) .familyPad (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .down source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) .down (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .map view source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.map view) (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .select source selected => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.select selected) (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .focusMinimal source minimal bound => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.focusMinimal minimal bound) (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .sortPad source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) .sortPad (fun _ h => source.projectionNoAtom h) member
  | _, _, _, .support action source => exact codeNoAtom (env := env) (U := U) (registry := registry) (target := target) (relevant := relevant) (.support action) (fun _ h => source.projectionNoAtom h) member
termination_by sizeOf query
decreasing_by all_goals (simp_wf <;> omega)

end

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

structure RichProjectionOrigin
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (name : Name) (index : Nat) (value : VExpr) where
  assigned : VExpr
  node : EndpointState sourceEnv U source (.proj name index value) assigned
  head : ProjectionHead node
  rank : Nat
  record : RecordData (Profile rank)
  request : DataRequest (Profile rank)
  nameEq : record.family.name = name
  member : (index, request) ∈ record.fields
  support : Profile rank
  majorFootprint : Footprint
  fieldFootprint : Footprint
  majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
    (Profile.singleton (n := rank + 1) (.record record)) majorFootprint
  fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint
  typed : request.input.HasType support
  alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ)
  atom : Atom rank
  atomMember : atom ∈ request.input.atoms

def RichProjectionOrigin.RootedAt
    {assigned : VExpr}
    (origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value)
    (start : EndpointState sourceEnv U source (.proj name index value) assigned) : Prop :=
  Nonempty (PrefixRoute sourceEnv U source (.proj name index value) start (projectionNatural origin.head))

private theorem projectionCodeOrigin
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (origins : ∀ a ∈ p.atoms,
      ∃ origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value,
        Nonempty (GeneralOutputPath env U registry target origin.atom a) ∧
        List.Subset (origin.majorFootprint ++ origin.fieldFootprint) footprint ∧ origin.RootedAt node)
    (member : b ∈ q.atoms) :
    ∃ origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value,
      Nonempty (GeneralOutputPath env U registry target origin.atom b) ∧
      List.Subset (origin.majorFootprint ++ origin.fieldFootprint) footprint ∧ origin.RootedAt node := by
  obtain ⟨a, ha, ⟨action⟩⟩ := action.atom member
  obtain ⟨origin, ⟨path⟩, included, rooted⟩ := origins a ha
  exact ⟨origin, ⟨.code path action (formed.singleton_of_mem ha)⟩, included, rooted⟩

mutual
theorem RichObs.projectionOrigin
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value,
      Nonempty (GeneralOutputPath env U registry target origin.atom atom) ∧
      List.Subset (origin.majorFootprint ++ origin.fieldFootprint) footprint ∧ origin.RootedAt node := by
  match n, demand, footprint, assigned, node, query with
  | _, _, _, _, _, .legacy source => exact False.elim (source.projectionNoAtom member)
  | _, _, _, _, _, .code source => exact source.projectionOrigin member
  | _, _, _, _, _, .projection head nameEq fieldMember majorQuery fieldCode typed alignment =>
    exact ⟨⟨_, _, head, _, _, _, nameEq, fieldMember, _, _, _, majorQuery, fieldCode, typed, alignment,
      _, member⟩, ⟨.refl⟩, (fun _ h => h), ⟨head.route⟩⟩
  | _, _, _, _, _, .route route source =>
    obtain ⟨origin, path, included, ⟨rooted⟩⟩ := source.projectionOrigin member
    exact ⟨origin, path, included, ⟨route.append rooted⟩⟩
  | _, _, _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, rooted⟩ := left.projectionOrigin h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), rooted⟩
    · obtain ⟨origin, path, included, rooted⟩ := right.projectionOrigin h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), rooted⟩
  | _, _, _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := source.projectionOrigin ha
    exact ⟨origin, ⟨.pad path⟩, included, rooted⟩
  | _, _, _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := source.projectionOrigin (List.mem_map.mpr ⟨_, member, rfl⟩)
    exact ⟨origin, ⟨.unpad path⟩, included, rooted⟩
  | _, _, _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := source.projectionOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path (.view change)⟩, included, rooted⟩
  | _, _, _, _, _, .select source selected =>
    cases List.mem_singleton.mp member
    exact source.projectionOrigin selected
  | _, _, _, _, _, .action source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := source.projectionOrigin (List.mem_singleton_self _)
    exact ⟨origin, ⟨.action path change⟩, included, rooted⟩
termination_by sizeOf query

theorem RichCert.projectionOrigin
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {demand : Profile n}
    (query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint)
    (member : atom ∈ demand.atoms) :
    ∃ origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value,
      Nonempty (GeneralOutputPath env U registry target origin.atom atom) ∧
      List.Subset (origin.majorFootprint ++ origin.fieldFootprint) footprint ∧ origin.RootedAt node := by
  match n, demand, footprint, assigned, node, query with
  | _, _, _, _, _, .legacy source => exact False.elim (source.projectionNoAtom member)
  | _, _, _, _, _, .observe source _ => exact source.projectionOrigin member
  | _, _, _, _, _, .route route source =>
    obtain ⟨origin, path, included, ⟨rooted⟩⟩ := source.projectionOrigin member
    exact ⟨origin, path, included, ⟨route.append rooted⟩⟩
  | _, _, _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path, included, rooted⟩ := left.projectionOrigin h
      exact ⟨origin, path, (fun _ h => List.mem_append_left _ (included h)), rooted⟩
    · obtain ⟨origin, path, included, rooted⟩ := right.projectionOrigin h
      exact ⟨origin, path, (fun _ h => List.mem_append_right _ (included h)), rooted⟩
  | _, _, _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := source.projectionOrigin ha
    exact ⟨origin, ⟨.pad path⟩, included, rooted⟩
  | _, _, _, _, _, .down source => exact projectionCodeOrigin .down source.formed (fun _ h => source.projectionOrigin h) member
  | _, _, _, _, _, .map view source => exact projectionCodeOrigin (.map view) source.formed (fun _ h => source.projectionOrigin h) member
  | _, _, _, _, _, .support action source => exact projectionCodeOrigin (.support action) source.formed (fun _ h => source.projectionOrigin h) member
  | _, _, _, _, _, .select source selected => exact projectionCodeOrigin (.select selected) source.formed (fun _ h => source.projectionOrigin h) member
termination_by sizeOf query

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
