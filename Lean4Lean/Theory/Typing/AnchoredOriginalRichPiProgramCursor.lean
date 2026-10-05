import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecipeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction

/-! Pi program extraction retains syntax, not a function producing rows.
All output actions remain pending. Legacy leaves and charged leaves retain
their actual input program for the next cursor step. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

inductive RichPiProgramLeaf (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target source : List VExpr)
    (A B : VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) :
    {n : Nat} → Atom n → Type where
  | native {n : Nat} {ambient : Profile n} {values : List (Key n × Profile n)}
      {domainNode : EndpointState sourceEnv U source A (.sort u)}
      {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
      (hu : u.WF U) (hv : v.WF U)
      (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient values rowFootprint)
      (resources : (domainFootprint ++ rowFootprint).Available available) :
      RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available (n := n + 1)
        (.pi prototypeDomain prototypeBody ambient values)
  | legacyCode (certificate : SortableCert env U registry target locals σ (.forallE A B) relevant profile footprint)
      (resources : footprint.Available available) (member : atom ∈ profile.atoms) :
      RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom
  | legacyObs (observation : SortableObs env U registry target locals σ (.forallE A B) profile footprint)
      (resources : footprint.Available available) (member : atom ∈ profile.atoms) :
      RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom
  | recipe (code : RichCodeRecipe env U registry target source locals σ (.forallE A B) relevant profile footprint)
      (resources : footprint.Available available) (member : atom ∈ profile.atoms) :
      RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom

noncomputable def RichPiProgramLeaf.programSize {n : Nat} {atom : Atom n}
    (leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available atom) : Nat :=
  match n, atom, leaf with
  | _ + 1, .pi _ _ _ _, .native hu hv domain guard rows _ => sizeOf (RichCert.pi hu hv domain guard rows)
  | _, _, .legacyCode certificate _ _ => sizeOf certificate
  | _, _, .legacyObs observation _ _ => sizeOf observation
  | _, _, .recipe code _ _ => sizeOf code

structure RichPiProgramOrigin (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target source : List VExpr)
    (A B : VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) (budget : Nat) (atom : Atom n) where
  rank : Nat
  original : Atom rank
  leaf : RichPiProgramLeaf sourceEnv env U registry target source A B locals σ available original
  path : GeneralOutputPath env U registry target original atom
  bounded : leaf.programSize ≤ budget

def RichPiProgramOrigins (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target source : List VExpr)
    (A B : VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) (budget : Nat) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms,
    Nonempty (RichPiProgramOrigin sourceEnv env U registry target source A B locals σ available budget atom)

private theorem RichPiProgramOrigins.code
    (_henv : env.Ordered)
    (change : SortableCodeAction env U registry target relevant p next q)
    (typed : p.HasType (.sort relevant))
    (origins : RichPiProgramOrigins sourceEnv env U registry target source A B locals σ available budget p) :
    RichPiProgramOrigins sourceEnv env U registry target source A B locals σ available budget q := by
  intro atom member
  obtain ⟨old, present, ⟨step⟩⟩ := change.atom member
  obtain ⟨origin⟩ := origins old present
  exact ⟨{ origin with path := .code origin.path step (typed.singleton_of_mem present) }⟩

mutual
 theorem RichCert.piProgramOrigins
    (henv : env.Ordered)
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (budget : Nat) (sizeBound : sizeOf certificate ≤ budget) :
    RichPiProgramOrigins sourceEnv env U registry target source A B locals σ available budget profile := by
  match certificate with
  | .legacy query =>
    intro atom member
    exact ⟨⟨_, atom, .legacyCode query resources member, .refl, by simp only [RichPiProgramLeaf.programSize]; apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega⟩⟩
  | .recipe code =>
    intro atom member
    exact ⟨⟨_, atom, .recipe code resources member, .refl, by simp only [RichPiProgramLeaf.programSize]; apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega⟩⟩
  | .observe observation _ => exact observation.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega)
  | .pi hu hv domain guard rows =>
    intro atom member
    cases List.mem_singleton.mp member
    exact ⟨⟨_, _, .native hu hv domain guard rows resources, .refl, by simp only [RichPiProgramLeaf.programSize]; apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega⟩⟩
  | .route _ query => exact query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piProgramOrigins henv (fun i need hm => resources i need (List.mem_append_left _ hm)) budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) atom member
    · exact right.piProgramOrigins henv (fun i need hm => resources i need (List.mem_append_right _ hm)) budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) atom member
  | .pad query => exact RichPiProgramOrigins.code henv .pad query.formed (query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega))
  | .down query => exact RichPiProgramOrigins.code henv .down query.formed (query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega))
  | .support action query => exact RichPiProgramOrigins.code henv (.support action) query.formed (query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega))
  | .map change query => exact RichPiProgramOrigins.code henv (.map change) query.formed (query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega))
  | .select query member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) _ member
termination_by sizeOf certificate

theorem RichObs.piProgramOrigins
    (henv : env.Ordered)
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (resources : footprint.Available available)
    (budget : Nat) (sizeBound : sizeOf observation ≤ budget) :
    RichPiProgramOrigins sourceEnv env U registry target source A B locals σ available budget profile := by
  match observation with
  | .legacy query =>
    intro atom member
    exact ⟨⟨_, atom, .legacyObs query resources member, .refl, by simp only [RichPiProgramLeaf.programSize]; apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega⟩⟩
  | .code query => exact query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega)
  | .route _ query => exact query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega)
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.piProgramOrigins henv (fun i need hm => resources i need (List.mem_append_left _ hm)) budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) atom member
    · exact right.piProgramOrigins henv (fun i need hm => resources i need (List.mem_append_right _ hm)) budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) atom member
  | .action query action =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path action }⟩
  | .view query change =>
    intro atom member
    cases List.mem_singleton.mp member
    obtain ⟨origin⟩ := query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) _ (List.mem_singleton_self _)
    exact ⟨{ origin with path := .action origin.path (.view change) }⟩
  | .select query member =>
    intro atom selected
    cases List.mem_singleton.mp selected
    exact query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) _ member
  | .pad query =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin⟩ := query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) old ho
    exact ⟨{ origin with path := .pad origin.path }⟩
  | .unpad query =>
    intro atom member
    obtain ⟨origin⟩ := query.piProgramOrigins henv resources budget (by apply Nat.le_trans ?_ sizeBound; simp_wf <;> omega) (.pad atom) (List.mem_map_of_mem member)
    exact ⟨{ origin with path := .unpad origin.path }⟩
termination_by sizeOf observation
end

/-- Expose the stored canonical input at its actual source and empty table.
Only its literal shape is transported; the original node is not replaced. -/
theorem RichRecipeRootInput.piPrograms
    (input : RichRecipeRootInput env U registry target)
    (henv : env.Ordered)
    (shape : input.canonicalExpression = VExpr.forallE A B) :
    RichPiProgramOrigins input.owner.selected.origin.source env U registry target [] A B
      [] input.realization (fun _ => []) (sizeOf input.certificate) input.profile := by
  cases input with
  | mk strata name owner expression canonicalExpression level node closed expressionEq
      source locals substitution realization relevant rank profile footprint certificate resources =>
    dsimp only at shape ⊢
    cases shape
    exact certificate.piProgramOrigins henv resources _ (Nat.le_refl _)

private theorem canonicalPiShape
    (equal : EqUpToLevels U expression (.forallE A B)) :
    ∃ C D, expression = VExpr.forallE C D := by
  cases equal with
  | forallE domainEq bodyEq => exact ⟨_, _, rfl⟩

/-- The next cursor program is obtained from the actual root certificate,
with every wrapper/action pending. In the charged-leaf case its stored recipe
is bounded by this strictly smaller input certificate, so recursive opening
cannot return the unchanged `.body parent` state. -/
theorem RichCodeRecipe.focusPiPrograms
    (henv : env.Ordered)
    (recipe : RichCodeRecipe env U registry target source locals σ (.forallE A B)
      relevant profile footprint) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧
      sizeOf input.certificate < sizeOf recipe ∧
      ∃ canonicalA canonicalB,
        input.canonicalExpression = VExpr.forallE canonicalA canonicalB ∧
        RichPiProgramOrigins input.owner.selected.origin.source env U registry target [] canonicalA canonicalB
          [] input.realization (fun _ => []) (sizeOf input.certificate) input.profile := by
  obtain ⟨input, ⟨pending⟩, smaller⟩ := recipe.focusInput
  obtain ⟨rootA, rootB, shape⟩ := pending.rootIsPi ⟨_, _, rfl⟩
  have canonical : ∃ canonicalA canonicalB,
      input.canonicalExpression = VExpr.forallE canonicalA canonicalB := by
    have equal := input.expressionEq
    rw [shape] at equal
    exact canonicalPiShape equal
  obtain ⟨canonicalA, canonicalB, canonicalShape⟩ := canonical
  exact ⟨input, ⟨pending⟩, smaller, canonicalA, canonicalB, canonicalShape,
    input.piPrograms henv canonicalShape⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
