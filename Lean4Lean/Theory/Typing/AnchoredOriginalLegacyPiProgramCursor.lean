import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedRowActions

/-! Legacy Pi program extraction retains actual finite syntax and a pending
output path; wrappers never rebuild the stored row body. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive LegacyPiLeaf (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation) :
    {n : Nat} → Atom n → Type where
  | plain {n : Nat} {ambient : Profile n} {table : List (Key n × Profile n)} (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (rows : PiRows env U registry target locals σ A B ambient table footprint)
      (resources : (domainFootprint ++ footprint).Available available) :
      LegacyPiLeaf env U registry target locals σ A B available (n := n + 1)
        (.pi prototypeDomain prototypeBody ambient table)
  | sortable {n : Nat} {ambient : Profile n} {table : List (Key n × Profile n)} (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (rows : SortableRows env U registry target locals σ A B relevant ambient table footprint)
      (resources : (domainFootprint ++ footprint).Available available) :
      LegacyPiLeaf env U registry target locals σ A B available (n := n + 1)
        (.pi prototypeDomain prototypeBody ambient table)

noncomputable def LegacyPiLeaf.programSize {n : Nat} {atom : Atom n}
    (leaf : LegacyPiLeaf env U registry target locals σ A B available atom) : Nat :=
  match n, atom, leaf with
  | _ + 1, .pi _ _ _ _, .plain domain guard rows _ => sizeOf (Obs.pi domain guard rows)
  | _ + 1, .pi _ _ _ _, .sortable domain guard rows _ => sizeOf (SortableCert.pi domain guard rows)

structure LegacyPiOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (budget : Nat) (atom : Atom n) where
  rank : Nat
  original : Atom rank
  leaf : LegacyPiLeaf env U registry target locals σ A B available original
  path : GeneralOutputPath env U registry target original atom
  bounded : leaf.programSize ≤ budget

abbrev LegacyPiOrigins (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (A B : VExpr) (available : Valuation)
    (budget : Nat) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, Nonempty (LegacyPiOrigin env U registry target locals σ A B available budget atom)

private theorem LegacyPiOrigins.code
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : LegacyPiOrigins env U registry target locals σ A B available budget p) :
    LegacyPiOrigins env U registry target locals σ A B available budget q := by
  intro atom member
  obtain ⟨old, present, ⟨step⟩⟩ := action.atom member
  obtain ⟨origin⟩ := origins old present
  exact ⟨{ origin with path := .code origin.path step (formed.singleton_of_mem present) }⟩

mutual
theorem _root_.Lean4Lean.AnchoredSource.Adapted.Obs.legacyPiPrograms
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) (budget : Nat) (bounded : sizeOf observation ≤ budget) :
    LegacyPiOrigins env U registry target locals σ A B available budget profile := by
  match observation with
  | .empty => exact fun _ member => nomatch member
  | .pi domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, .plain domain guard rows resources, .refl, by simpa only [LegacyPiLeaf.programSize] using bounded⟩⟩
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_left _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
    · exact right.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_right _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
  | .view query change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .pad query =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) old present
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad query =>
    intro atom member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
  | .rowShift query =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action (.pad origin.path) (.view (.commutePadFn _ _)) }⟩
termination_by sizeOf observation

theorem _root_.Lean4Lean.AnchoredSource.Adapted.CodeCert.legacyPiPrograms
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) (budget : Nat) (bounded : sizeOf certificate ≤ budget) :
    LegacyPiOrigins env U registry target locals σ A B available budget profile := by
  match certificate with
  | .seed query _ => exact query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_left _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
    · exact right.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_right _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
  | .pad query => exact LegacyPiOrigins.code .pad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .familyPad query => exact LegacyPiOrigins.code .familyPad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .unpad query => exact LegacyPiOrigins.code .unpad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .down query => exact LegacyPiOrigins.code .down query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .map change query => exact LegacyPiOrigins.code (.map change) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .select query member => exact LegacyPiOrigins.code (.select member) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .focusMinimal query minimal bound => exact LegacyPiOrigins.code (.focusMinimal minimal bound) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
termination_by sizeOf certificate

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableObs.legacyPiPrograms
    (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) (budget : Nat) (bounded : sizeOf observation ≤ budget) :
    LegacyPiOrigins env U registry target locals σ A B available budget profile := by
  match observation with
  | .legacy query => exact query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega)
  | .code _ query => exact query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_left _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
    · exact right.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_right _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
  | .view query change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .action query change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (change) }⟩
  | .pad query =>
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) old present
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad query =>
    intro atom member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
  | .rowShift query =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action (.pad origin.path) (.view (.commutePadFn _ _)) }⟩
termination_by sizeOf observation

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.legacyPiPrograms
    (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
    (resources : footprint.Available available) (budget : Nat) (bounded : sizeOf certificate ≤ budget) :
    LegacyPiOrigins env U registry target locals σ A B available budget profile := by
  match certificate with
  | .pi domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, .sortable domain guard rows resources, .refl, by simpa only [LegacyPiLeaf.programSize] using bounded⟩⟩
  | .ofCode query _ => exact query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega)
  | .observe query _ => exact query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega)
  | .seed query _ => exact query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_left _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
    · exact right.legacyPiPrograms (fun i need hm => resources i need (List.mem_append_right _ hm)) budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega) atom member
  | .pad query => exact LegacyPiOrigins.code .pad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .familyPad query => exact LegacyPiOrigins.code .familyPad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .unpad query => exact LegacyPiOrigins.code .unpad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .down query => exact LegacyPiOrigins.code .down query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .map change query => exact LegacyPiOrigins.code (.map change) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .select query member => exact LegacyPiOrigins.code (.select member) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .focusMinimal query minimal bound => exact LegacyPiOrigins.code (.focusMinimal minimal bound) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .sortPad query => exact LegacyPiOrigins.code .sortPad query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
  | .support action query => exact LegacyPiOrigins.code (.support action) query.formed (query.legacyPiPrograms resources budget (by apply Nat.le_trans ?_ bounded; simp_wf <;> omega))
termination_by sizeOf certificate

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
