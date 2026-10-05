import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeNativeCursor
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedBetaForward

/-! Pending row changes retain the actual old table occurrence. Their body
is never replaced by the result of F or variable replay. The key view and
code action are executable existing syntax, not a semantic output supplier. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- Fixed-grade row provenance through input, anchor, and output changes. -/
structure PendingNativeRow (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : List (Key n × Profile n))
    (relevant nextRelevant : Bool) (key : Key n) (result : Profile n) where
  oldKey : Key n
  oldResult : Profile n
  member : (oldKey, oldResult) ∈ original
  witness : Atom n
  keyView : AtomView env U registry target (n := n + 1) (.fn oldKey witness) (.fn key witness)
  output : SortableCodeAction env U registry target relevant oldResult nextRelevant result

namespace PendingNativeRow

noncomputable def direct
    {n : Nat} {original : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (member : (key, result) ∈ original) :
    PendingNativeRow env U registry target original relevant relevant key result :=
  let witness : Atom n := match n with | 0 => true | _ + 1 => .sort true
  ⟨key, result, member, witness, .refl _, .id⟩

noncomputable def input
    {n : Nat} {original : List (Key n × Profile n)} {key : Key n} {result : Profile n} {newInput : Profile n}
    (row : PendingNativeRow env U registry target original relevant nextRelevant key result)
    (forward : ProfileView env U registry target newInput key.input)
    (backward : ProfileView env U registry target key.input newInput) :
    PendingNativeRow env U registry target original relevant nextRelevant (inputKey key newInput) result :=
  { row with keyView := .trans row.keyView (.input forward backward) }

noncomputable def reanchor
    {n : Nat} {original : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (row : PendingNativeRow env U registry target original relevant nextRelevant key result)
    (admitted : Admitted env U registry target key anchor anchor) :
    PendingNativeRow env U registry target original relevant nextRelevant (reanchorKey key anchor) result :=
  { row with keyView := .trans row.keyView (.reanchor admitted) }

noncomputable def support
    {n : Nat} {original : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (row : PendingNativeRow env U registry target original relevant nextRelevant key result)
    (action : SupportAction env U registry target n) :
    PendingNativeRow env U registry target original relevant nextRelevant key (action.apply result) :=
  { row with output := .comp row.output (.support action) }

/-- Recover the real old-input demand from the pending key program. -/
theorem argumentAdapter
    {n : Nat} {original : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (row : PendingNativeRow env U registry target original relevant nextRelevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    Nonempty (GeneralNormalProfileAdapter env U registry target key.input row.oldKey.input) := by
  have change := row.keyView.toGeneralAdapter henv hscoped formed
  change GeneralAtomAdapter env U registry target (n := n + 1)
    (.fn (AdapterNormal.key row.oldKey) (AdapterNormal.atom row.witness))
    (.fn (AdapterNormal.key key) (AdapterNormal.atom row.witness)) at change
  obtain ⟨old, output, equal, ⟨keys⟩, _⟩ := change.fn_inv
  cases equal
  exact ⟨keys.arguments⟩

/-- Execute pending key changes at the new argument pair while keeping the
actual old native row. The native anchor supplies the seed required by
reanchor; no certificate is rebuilt and no semantic answer is assumed. -/
theorem oldAdmission
    {n : Nat} {original : List (Key n × Profile n)} {key : Key n} {result : Profile n}
    (row : PendingNativeRow env U registry target original relevant nextRelevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (seed : Admitted env U registry target row.oldKey row.oldKey.anchor row.oldKey.anchor)
    (admitted : Admitted env U registry target key x y) :
    Admitted env U registry target row.oldKey x y := by
  have change := row.keyView.toGeneralAdapter henv hscoped formed
  change GeneralAtomAdapter env U registry target (n := n + 1)
    (.fn (AdapterNormal.key row.oldKey) (AdapterNormal.atom row.witness))
    (.fn (AdapterNormal.key key) (AdapterNormal.atom row.witness)) at change
  obtain ⟨old, output, equal, ⟨keys⟩, _⟩ := change.fn_inv
  cases equal
  have normalized := keys.pull henv hscoped formed
    (AdapterNormal.normalizeAdmission henv hscoped formed seed)
    (AdapterNormal.normalizeAdmission henv hscoped formed admitted)
  have view := (AdapterNormal.profileView (U := U) (registry := registry)
    (Γ := target) henv row.oldKey.input).inverse henv
  exact view.admissionMapWith (key := AdapterNormal.key row.oldKey) formed
    (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
    (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h) normalized

/-- Every selected transformed row points to a literal original row. -/
theorem inputRows
    {n : Nat} {original rows : List (Key n × Profile n)}
    {key wanted : Key n} {result newInput : Profile n}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (PendingNativeRow env U registry target original relevant nextRelevant key result))
    (forward : ProfileView env U registry target newInput wanted.input)
    (backward : ProfileView env U registry target wanted.input newInput)
    (member : (key, result) ∈ reanchorRows wanted (inputKey wanted newInput) rows) :
    Nonempty (PendingNativeRow env U registry target original relevant nextRelevant key result) := by
  rcases mem_reanchorRows.mp member with unchanged | ⟨rfl, selected⟩
  · exact origins _ _ unchanged
  · obtain ⟨row⟩ := origins _ _ selected
    exact ⟨row.input forward backward⟩

theorem reanchorRows
    {n : Nat} {original rows : List (Key n × Profile n)}
    {key wanted : Key n} {result : Profile n}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (PendingNativeRow env U registry target original relevant nextRelevant key result))
    (admitted : Admitted env U registry target wanted anchor anchor)
    (member : (key, result) ∈ Lean4Lean.AnchoredSemantics.reanchorRows wanted (reanchorKey wanted anchor) rows) :
    Nonempty (PendingNativeRow env U registry target original relevant nextRelevant key result) := by
  rcases mem_reanchorRows.mp member with unchanged | ⟨rfl, selected⟩
  · exact origins _ _ unchanged
  · obtain ⟨row⟩ := origins _ _ selected
    exact ⟨row.reanchor admitted⟩

theorem supportRows
    {n : Nat} {original rows : List (Key n × Profile n)}
    {key wanted : Key n} {result : Profile n}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (PendingNativeRow env U registry target original relevant nextRelevant key result))
    (action : SupportAction env U registry target n)
    (member : (key, result) ∈ outputRows wanted action.apply rows) :
    Nonempty (PendingNativeRow env U registry target original relevant nextRelevant key result) := by
  rcases mem_outputRows.mp member with unchanged | ⟨rfl, previous, selected, rfl⟩
  · exact origins _ _ unchanged
  · obtain ⟨row⟩ := origins _ _ selected
    exact ⟨row.support action⟩

end PendingNativeRow

/-- Execute the hard input-view/reanchor/support row path against the actual
native table. The emitted cursor retains the exact old body and BinderPack;
only finite key/output programs are pending. -/
theorem RichRows.pendingNativeCursor
    {n : Nat} {ambient result newInput : Profile n} {wanted key : Key n}
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
    (selected : (key, result) ∈ outputRows (reanchorKey (inputKey wanted newInput) anchor) action.apply
      (reanchorRows (inputKey wanted newInput) (reanchorKey (inputKey wanted newInput) anchor)
        (reanchorRows wanted (inputKey wanted newInput) table))) :
    ∃ pending : PendingNativeRow env U registry target table relevant relevant key result,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy) := by
  have initial := fun key result (member : (key, result) ∈ table) =>
    (⟨PendingNativeRow.direct member⟩ : Nonempty
      (PendingNativeRow env U registry target table relevant relevant key result))
  have inputs := fun key result member => PendingNativeRow.inputRows initial forward backward
    (key := key) (result := result) member
  have anchors := fun key result member => PendingNativeRow.reanchorRows inputs admitted
    (key := key) (result := result) member
  obtain ⟨pending⟩ := PendingNativeRow.supportRows anchors action selected
  obtain ⟨row, domainEq, smaller, depth⟩ := rows.nativeCursor domain domainAvailable resources pending.member
  exact ⟨pending, row, domainEq, smaller, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
