import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePendingNativeRows

/-! Actual profile selection for the input/reanchor/output action slice.
The input action's HasType test is decided here; no extra input-typing
hypothesis is imposed on the original native row. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- Invert the actual support maps, including their inactive input branch.
This is the profile supplied by the corresponding recipe action chain. -/
theorem PendingNativeRow.selectActions
    {n : Nat} {table : List (Key n × Profile n)}
    {ambient newInput support : Profile n} {selected : List (Key n × Profile n)} {wanted key : Key n} {result : Profile n}
    (forward : ProfileView env U registry target newInput wanted.input)
    (backward : ProfileView env U registry target wanted.input newInput)
    (admitted : Admitted env U registry target (inputKey wanted newInput) anchor anchor)
    (action : SupportAction env U registry target n)
    (present : AtomData.pi newDomain newBody support selected ∈
      (outputTypes (reanchorKey (inputKey wanted newInput) anchor) action.apply
        (reanchorTypes (inputKey wanted newInput) (reanchorKey (inputKey wanted newInput) anchor)
          (inputTypes wanted newInput backward.mapType
            (Profile.singleton (AtomData.pi prototypeDomain prototypeBody ambient table))))).atoms)
    (member : (key, result) ∈ selected) :
    Nonempty (PendingNativeRow env U registry target table relevant relevant key result) := by
  classical
  have initial := fun key result (member : (key, result) ∈ table) =>
    (⟨PendingNativeRow.direct member⟩ : Nonempty
      (PendingNativeRow env U registry target table relevant relevant key result))
  simp only [inputTypes, Profile.singleton, Profile.mk, List.map_cons, List.map_nil] at present
  split at present
  · simp only [reanchorTypes, outputTypes, List.map_cons, List.map_nil,
      List.mem_singleton] at present
    cases List.mem_singleton.mp present
    have inputs := fun key result member => PendingNativeRow.inputRows initial forward backward
      (key := key) (result := result) member
    have anchors := fun key result member => PendingNativeRow.reanchorRows inputs admitted
      (key := key) (result := result) member
    exact PendingNativeRow.supportRows anchors action member
  · simp only [reanchorTypes, outputTypes, List.map_cons, List.map_nil,
      List.mem_singleton] at present
    cases List.mem_singleton.mp present
    have anchors := fun key result member => PendingNativeRow.reanchorRows initial admitted
      (key := key) (result := result) member
    exact PendingNativeRow.supportRows anchors action member

/-- The action-selected recipe row executes the SAME original native body.
All its local resources, BinderPack, and old anchor remain in the result. -/
theorem RichRows.actionNativeCursor
    {n : Nat} {ambient result newInput support : Profile n} {selected : List (Key n × Profile n)} {wanted key : Key n}
    {table : List (Key n × Profile n)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (forward : ProfileView env U registry target newInput wanted.input)
    (backward : ProfileView env U registry target wanted.input newInput)
    (admitted : Admitted env U registry target (inputKey wanted newInput) anchor anchor)
    (action : SupportAction env U registry target n)
    (present : AtomData.pi newDomain newBody support selected ∈
      (outputTypes (reanchorKey (inputKey wanted newInput) anchor) action.apply
        (reanchorTypes (inputKey wanted newInput) (reanchorKey (inputKey wanted newInput) anchor)
          (inputTypes wanted newInput backward.mapType
            (Profile.singleton (AtomData.pi prototypeDomain prototypeBody ambient table))))).atoms)
    (member : (key, result) ∈ selected) :
    ∃ pending : PendingNativeRow env U registry target table relevant relevant key result,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy) := by
  obtain ⟨pending⟩ := PendingNativeRow.selectActions forward backward admitted action present member
  obtain ⟨row, same, smaller, bounded⟩ := rows.nativeCursor domain domainAvailable resources pending.member
  exact ⟨pending, row, same, smaller, bounded⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
