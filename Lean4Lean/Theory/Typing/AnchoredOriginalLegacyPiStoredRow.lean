import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyPiProgramCursor

/-! Select the literal legacy body before attaching it to actual original
Pi children. Its recursion budget measures the retained syntax, not wrappers
introduced by the attachment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive LegacyRowBody (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (B : VExpr) :
    Bool → {n : Nat} → Profile n → Footprint → Type where
  | plain (body : CodeCert env U registry target locals σ B result footprint) :
      LegacyRowBody env U registry target locals σ B true result footprint
  | sortable (body : SortableCert env U registry target locals σ B relevant result footprint) :
      LegacyRowBody env U registry target locals σ B relevant result footprint

noncomputable def LegacyRowBody.programSize
    (body : LegacyRowBody env U registry target locals σ B relevant result footprint) : Nat :=
  match body with
  | .plain body => sizeOf body
  | .sortable body => sizeOf body

def LegacyRowBody.certificate
    (body : LegacyRowBody env U registry target locals σ B relevant result footprint) :
    SortableCert env U registry target locals σ B relevant result footprint :=
  match body with
  | .plain body => .ofCode body body.formed
  | .sortable body => body

structure LegacyStoredPiRow (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (relevant : Bool) (key : Key n) (result : Profile n) where
  ambient : Profile n
  domainFootprint : Footprint
  domain : SortableCert env U registry target locals σ A true ambient domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A key ambient
  bodyFootprint : Footprint
  body : LegacyRowBody env U registry target (Locals.push locals) (σ.cons key.anchor) B relevant result bodyFootprint
  packed : Profile n
  outside : Footprint
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms
  outsideAvailable : outside.Available available

def LegacyStoredPiRow.attach
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (row : LegacyStoredPiRow env U registry target locals σ A B available relevant key result) :
    RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result := {
  domainSupport := row.ambient, domainFootprint := row.domainFootprint
  domain := .legacy row.domain, domainAvailable := row.domainAvailable
  inputTyped := row.guard.inputTyped
  alignment := .step row.guard.path row.guard.inputTyped row.guard.formed row.guard.domains (.refl _)
  anchor := row.guard.anchor
  bodyFootprint := row.bodyFootprint, body := .legacy row.body.certificate
  packed := row.packed, outside := row.outside, pack := row.pack
  covered := row.covered, outsideAvailable := row.outsideAvailable }

theorem _root_.Lean4Lean.AnchoredSource.Adapted.PiRows.storedCursor
    (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
    (rows : PiRows env U registry target locals σ A B ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) (member : (key, result) ∈ table) :
    ∃ row : LegacyStoredPiRow env U registry target locals σ A B available true key result,
      row.body.programSize < sizeOf rows := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨⟨_, _, .ofCode domain domain.formed, domainAvailable, guard, _, .plain body,
        _, _, pack, covered, fun i need hm => resources i need (List.mem_append_left _ hm)⟩, ?_⟩
      simp only [LegacyRowBody.programSize]
      simp_wf
      omega
    · obtain ⟨row, smaller⟩ := tail.storedCursor domain domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, ?_⟩
      simp_wf
      omega
termination_by sizeOf rows

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableRows.storedCursor
    (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
    (rows : SortableRows env U registry target locals σ A B relevant ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available) (member : (key, result) ∈ table) :
    ∃ row : LegacyStoredPiRow env U registry target locals σ A B available relevant key result,
      row.body.programSize < sizeOf rows := by
  match rows with
  | .nil => cases member
  | .cons guard body pack covered tail =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      refine ⟨⟨_, _, domain, domainAvailable, guard, _, .sortable body,
        _, _, pack, covered, fun i need hm => resources i need (List.mem_append_left _ hm)⟩, ?_⟩
      simp only [LegacyRowBody.programSize]
      simp_wf
      omega
    · obtain ⟨row, smaller⟩ := tail.storedCursor domain domainAvailable
        (fun i need hm => resources i need (List.mem_append_right _ hm)) member
      refine ⟨row, ?_⟩
      simp_wf
      omega
termination_by sizeOf rows

inductive LegacyPiSelection (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (budget : Nat) (key : Key n) (result : Profile n) : Type where
  | selected
      (pending : RankedPendingNativeRow env U registry target table relevant key result)
      (row : LegacyStoredPiRow env U registry target locals σ A B available relevant pending.oldKey pending.oldResult)
      (smaller : row.body.programSize < budget) :
      LegacyPiSelection env U registry target locals σ A B available budget key result

private def appendPath {r s : Nat} {a : Atom r} {b : Atom s}
    (first : GeneralOutputPath env U registry target a b) :
    {n : Nat} → {c : Atom n} → GeneralOutputPath env U registry target b c →
      GeneralOutputPath env U registry target a c
  | _, _, .refl => first
  | _, _, .action path change => .action (appendPath first path) change
  | _, _, .code path change formed => .code (appendPath first path) change formed
  | _ + 1, .pad _, .pad path => .pad (appendPath first path)
  | _, _, .unpad path => .unpad (appendPath first path)

theorem LegacyPiOrigin.selectRow
    {n : Nat} {key : Key n} {result support : Profile n} {table : List (Key n × Profile n)}
    (origin : LegacyPiOrigin env U registry target locals σ A B available budget atom)
    (continuation : GeneralOutputPath env U registry target atom (n := n+1)
      (.pi selectedDomain selectedBody support table))
    (member : (key, result) ∈ table) :
    Nonempty (LegacyPiSelection env U registry target locals σ A B available budget key result) := by
  obtain ⟨rank, atom, leaf, path, bounded⟩ := origin
  let path := appendPath path continuation
  cases leaf with
  | plain domain guard rows resources =>
    obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result member
    obtain ⟨row, smaller⟩ := rows.storedCursor domain
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) pending.member
    refine ⟨.selected pending row ?_⟩
    simp only [LegacyPiLeaf.programSize] at bounded
    have : sizeOf rows < sizeOf (Obs.pi domain guard rows) := by simp_wf; omega
    omega
  | sortable domain guard rows resources =>
    obtain ⟨pending⟩ := RankedPiProfile.nativePath path key result member
    obtain ⟨row, smaller⟩ := rows.storedCursor domain
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm)) pending.member
    refine ⟨.selected pending row ?_⟩
    simp only [LegacyPiLeaf.programSize] at bounded
    have : sizeOf rows < sizeOf (SortableCert.pi domain guard rows) := by simp_wf; omega
    omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
