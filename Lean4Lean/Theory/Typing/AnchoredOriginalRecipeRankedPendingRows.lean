import Lean4Lean.Theory.Typing.AnchoredOriginalRecipePendingNativeRows

/-! Grade-changing continuations retain the old native row. Padding and
unshifting act on demands and eventual code output, never on the stored body
certificate used for recursive descent. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

inductive RankedPendingNativeRow (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (original : List (Key n × Profile n)) (relevant : Bool) :
    {m : Nat} → Key m → Profile m → Type where
  | fixed (row : PendingNativeRow env U registry target original relevant relevant key result) :
      RankedPendingNativeRow env U registry target original relevant key result
  | change {key nextKey : Key m} {result nextResult : Profile m} {witness : Atom m}
      (row : RankedPendingNativeRow env U registry target original relevant key result)
      (view : AtomView env U registry target (n := m + 1) (.fn key witness) (.fn nextKey witness))
      (action : SortableCodeAction env U registry target relevant result relevant nextResult) :
      RankedPendingNativeRow env U registry target original relevant nextKey nextResult
  | pad (row : RankedPendingNativeRow env U registry target original relevant key result) :
      RankedPendingNativeRow env U registry target original relevant key.pad result.pad
  | down {key : Key m} {result : Profile (m + 1)}
      (row : RankedPendingNativeRow env U registry target original relevant key.pad result) :
      RankedPendingNativeRow env U registry target original relevant key result.down

namespace RankedPendingNativeRow

variable {n m : Nat} {original : List (Key n × Profile n)} {key : Key m} {result : Profile m}

def oldKey : {m : Nat} → {key : Key m} → {result : Profile m} →
    RankedPendingNativeRow env U registry target original relevant key result → Key n
  | _, _, _, .fixed row => row.oldKey
  | _, _, _, .change row _ _ => row.oldKey
  | _, _, _, .pad row => row.oldKey
  | _, _, _, .down row => row.oldKey

def oldResult : {m : Nat} → {key : Key m} → {result : Profile m} →
    RankedPendingNativeRow env U registry target original relevant key result → Profile n
  | _, _, _, .fixed row => row.oldResult
  | _, _, _, .change row _ _ => row.oldResult
  | _, _, _, .pad row => row.oldResult
  | _, _, _, .down row => row.oldResult

theorem member (row : RankedPendingNativeRow env U registry target original relevant key result) :
    (row.oldKey, row.oldResult) ∈ original := by
  induction row with
  | fixed row => exact row.member
  | pad row ih | down row ih | change row _ _ ih => exact ih

def output : {m : Nat} → {key : Key m} → {result : Profile m} →
    (row : RankedPendingNativeRow env U registry target original relevant key result) →
    SortableCodeAction env U registry target relevant row.oldResult relevant result
  | _, _, _, .fixed row => row.output
  | _, _, _, .change row _ action => .comp row.output action
  | _, _, _, .pad row => .comp row.output .pad
  | _, _, _, .down row => .comp row.output .down

private theorem keyForward
    {a b : Key m} {witness : Atom m}
    (view : AtomView env U registry target (n := m + 1) (.fn a witness) (.fn b witness))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (seed : Admitted env U registry target a a.anchor a.anchor) :
    Admitted env U registry target b b.anchor b.anchor := by
  have change := view.toGeneralAdapter henv hscoped formed
  change GeneralAtomAdapter env U registry target (n := m + 1)
    (.fn (AdapterNormal.key a) (AdapterNormal.atom witness))
    (.fn (AdapterNormal.key b) (AdapterNormal.atom witness)) at change
  obtain ⟨old, output, equal, ⟨keys⟩, _⟩ := change.fn_inv
  cases equal
  have normalized := keys.forward henv hscoped formed
    (AdapterNormal.normalizeAdmission henv hscoped formed seed)
  have back := (AdapterNormal.profileView (U := U) (registry := registry)
    (Γ := target) henv b.input).inverse henv
  exact back.admissionMapWith (key := AdapterNormal.key b) formed
    (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
    (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h) normalized

/-- Intermediate anchor guards are computed from the real native guard,
including after rank changes. -/
theorem currentAnchor
    (row : RankedPendingNativeRow env U registry target original relevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (seed : Admitted env U registry target row.oldKey row.oldKey.anchor row.oldKey.anchor) :
    Admitted env U registry target key key.anchor key.anchor := by
  induction row with
  | fixed row => exact keyForward row.keyView henv hscoped formed seed
  | change row view action ih => exact keyForward view henv hscoped formed (ih seed)
  | pad row ih => exact (ih seed).pad henv
  | down row ih => exact (ih seed).unpad henv formed

/-- The old anchor is always the original native guard's anchor. -/
theorem oldAdmission
    (row : RankedPendingNativeRow env U registry target original relevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (seed : Admitted env U registry target row.oldKey row.oldKey.anchor row.oldKey.anchor)
    (admitted : Admitted env U registry target key x y) :
    Admitted env U registry target row.oldKey x y := by
  induction row with
  | fixed row => exact row.oldAdmission henv hscoped formed seed admitted
  | change row view action ih =>
    let step : PendingNativeRow env U registry target [(_, _)] relevant relevant _ _ :=
      ⟨_, _, List.mem_singleton_self _, _, view, action⟩
    exact ih seed (step.oldAdmission henv hscoped formed
      (row.currentAnchor henv hscoped formed seed) admitted)
  | pad row ih => exact ih seed (admitted.unpad henv formed)
  | down row ih => exact ih seed (admitted.pad henv)

/-- Fixed-grade operations may occur after any number of grade changes. -/
noncomputable def input
    (row : RankedPendingNativeRow env U registry target original relevant key result)
    (forward : ProfileView env U registry target newInput key.input)
    (backward : ProfileView env U registry target key.input newInput) :
    RankedPendingNativeRow env U registry target original relevant (inputKey key newInput) result :=
  let witness : Atom m := match m with | 0 => true | _ + 1 => .sort true
  .change row (witness := witness) (.input forward backward) .id

noncomputable def reanchor
    (row : RankedPendingNativeRow env U registry target original relevant key result)
    (admitted : Admitted env U registry target key anchor anchor) :
    RankedPendingNativeRow env U registry target original relevant (reanchorKey key anchor) result :=
  let witness : Atom m := match m with | 0 => true | _ + 1 => .sort true
  .change row (witness := witness) (.reanchor admitted) .id

noncomputable def support
    (row : RankedPendingNativeRow env U registry target original relevant key result)
    (action : SupportAction env U registry target m) :
    RankedPendingNativeRow env U registry target original relevant key (action.apply result) :=
  let witness : Atom m := match m with | 0 => true | _ + 1 => .sort true
  .change row (witness := witness) (.refl _) (.support action)

theorem inputRows
    {rows : List (Key m × Profile m)} {wanted : Key m}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (RankedPendingNativeRow env U registry target original relevant key result))
    (forward : ProfileView env U registry target newInput wanted.input)
    (backward : ProfileView env U registry target wanted.input newInput)
    (selected : (key, result) ∈ reanchorRows wanted (inputKey wanted newInput) rows) :
    Nonempty (RankedPendingNativeRow env U registry target original relevant key result) := by
  rcases mem_reanchorRows.mp selected with unchanged | ⟨rfl, sourceMember⟩
  · exact origins _ _ unchanged
  · obtain ⟨row⟩ := origins _ _ sourceMember
    exact ⟨row.input forward backward⟩

theorem anchorRows
    {rows : List (Key m × Profile m)} {wanted : Key m}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (RankedPendingNativeRow env U registry target original relevant key result))
    (admitted : Admitted env U registry target wanted anchor anchor)
    (selected : (key, result) ∈ reanchorRows wanted (reanchorKey wanted anchor) rows) :
    Nonempty (RankedPendingNativeRow env U registry target original relevant key result) := by
  rcases mem_reanchorRows.mp selected with unchanged | ⟨rfl, sourceMember⟩
  · exact origins _ _ unchanged
  · obtain ⟨row⟩ := origins _ _ sourceMember
    exact ⟨row.reanchor admitted⟩

theorem outputRows
    {rows : List (Key m × Profile m)} {wanted : Key m}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (RankedPendingNativeRow env U registry target original relevant key result))
    (action : SupportAction env U registry target m)
    (selected : (key, result) ∈ AnchoredSemantics.outputRows wanted action.apply rows) :
    Nonempty (RankedPendingNativeRow env U registry target original relevant key result) := by
  rcases mem_outputRows.mp selected with unchanged | ⟨rfl, previous, sourceMember, rfl⟩
  · exact origins _ _ unchanged
  · obtain ⟨row⟩ := origins _ _ sourceMember
    exact ⟨row.support action⟩

/-- Actual rankShift rows, as used by commutePadFn. -/
theorem rankShiftRows
    {m : Nat} {rows : List (Key m × Profile m)} {key : Key (m+1)} {result : Profile (m+1)}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (RankedPendingNativeRow env U registry target original relevant key result))
    (selected : (key, result) ∈ Rows.rankShift rows) :
    Nonempty (RankedPendingNativeRow env U registry target original relevant key result) := by
  obtain ⟨⟨oldKey, oldResult⟩, member, equal⟩ := List.mem_map.mp selected
  cases equal
  obtain ⟨row⟩ := origins oldKey oldResult member
  exact ⟨.pad row⟩

/-- Actual unshift rows, as used by uncommutePadFn. -/
theorem unshiftRows
    {m : Nat} {rows : List (Key (m+1) × Profile (m+1))} {wanted key : Key m} {result : Profile m}
    (origins : ∀ key result, (key, result) ∈ rows →
      Nonempty (RankedPendingNativeRow env U registry target original relevant key result))
    (selected : (key, result) ∈ Rows.unshift wanted rows) :
    Nonempty (RankedPendingNativeRow env U registry target original relevant key result) := by
  obtain ⟨rfl, oldResult, member, rfl⟩ := Rows.mem_unshift.mp selected
  obtain ⟨row⟩ := origins key.pad oldResult member
  exact ⟨.down row⟩

end RankedPendingNativeRow

/-- Grade-changing continuations select the exact old body with its unchanged
BinderPack. Recursive descent is measured there, not on a padded/replayed body. -/
theorem RichRows.rankedPendingCursor
    {n m : Nat} {ambient : Profile n} {result : Profile m} {key : Key m}
    {table : List (Key n × Profile n)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (pending : RankedPendingNativeRow env U registry target table relevant key result) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult,
      HEq row.domain domain ∧ sizeOf row.body < sizeOf rows ∧
      ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy) := by
  exact rows.nativeCursor domain domainAvailable resources pending.member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
