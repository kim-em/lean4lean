import Lean4Lean.Theory.Typing.AnchoredBoundedStage

/-! A header may need its own native-depth control while preserving budgets
of newer declarations. These finite budgets use the SAME observation and
valuation-entry certificates. This is the strengthened induction contract,
not a declaration-stage fundamental theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted.Budgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

abbrev Budgets := List ((Name → Bool) × Nat)

def Within (budgets : Budgets) (depth : (Name → Bool) → Nat) : Prop :=
  ∀ filter fuel, (filter, fuel) ∈ budgets → depth filter ≤ fuel

structure Fits (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation) : Prop where
  entry : ∀ index need, need ∈ available index → ∀ sourceType, Lookup source index sourceType →
    ∃ entry : ValuationEntry env U registry target locals σ τ available index need sourceType,
      Within budgets entry.certificate.nativeDepth

structure PairedFits (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation) : Prop where
  forward : Fits budgets env U registry source target locals σ τ available
  backward : Fits budgets env U registry source target locals τ σ available

structure Result (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (left right sourceType : VExpr) (demand : Profile n)
    extends GradedTransferResult env U registry target locals σ τ available left right sourceType demand where
  observationBound : Within budgets observation.nativeDepth
  certificateBound : Within budgets certificate.nativeDepth

def Transfer (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (left right sourceType : VExpr) : Prop :=
  ∀ {n} {demand : Profile n} {footprint}
    (observation : Obs env U registry target locals σ left demand footprint),
    Within budgets observation.nativeDepth → footprint.Available available →
      Nonempty (Result budgets env U registry target locals σ τ available left right sourceType demand)

def SortCorrect (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression sourceType : VExpr) : Prop :=
  ∀ level relevant, sourceType = .sort level → Relevant level relevant →
    ∀ {n} {demand : Profile n} {footprint}
      (observation : Obs env U registry target locals σ expression demand footprint),
      Within budgets observation.nativeDepth → footprint.Available available → demand.HasType (.sort relevant)

def Joint (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right sourceType : VExpr) : Prop :=
  ∀ target locals σ τ available, available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source → PairedFits budgets env U registry source target locals σ τ available →
      Transfer budgets env U registry target locals σ τ available left right sourceType ∧
      Transfer budgets env U registry target locals σ τ available right left sourceType ∧
      SortCorrect budgets env U registry target locals σ available left sourceType ∧
      SortCorrect budgets env U registry target locals σ available right sourceType

variable {budgets : Budgets} {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}

/-- Every typed context has only finitely many relevant available entries.
Each selected certificate retains its original protected budgets; the extra
control bound is a maximum over those very witnesses. -/
theorem Fits.finiteControl (control : Name → Bool)
    (fits : Fits budgets env U registry source target locals σ τ available) :
    ∃ fuel, Fits ((control, fuel) :: budgets) env U registry source target locals σ τ available := by
  have atIndex (index : Nat) (hi : index < source.length) :
      ∃ fuel, ∀ need ∈ available index, ∀ sourceType, Lookup source index sourceType →
        ∃ entry : ValuationEntry env U registry target locals σ τ available index need sourceType,
          Within budgets entry.certificate.nativeDepth ∧ entry.certificate.nativeDepth control ≤ fuel := by
    let canonical := Lookup.ofLt hi
    have collect : ∀ requests : List Need, requests ⊆ available index →
        ∃ fuel, ∀ need ∈ requests, ∀ sourceType, Lookup source index sourceType →
          ∃ entry : ValuationEntry env U registry target locals σ τ available index need sourceType,
            Within budgets entry.certificate.nativeDepth ∧ entry.certificate.nativeDepth control ≤ fuel := by
      intro requests included
      induction requests with
      | nil => exact ⟨0, by intro _ h; cases h⟩
      | cons need rest ih =>
        obtain ⟨entry, bounded⟩ := fits.entry index need (included List.mem_cons_self) canonical.val canonical.property
        obtain ⟨fuel, tail⟩ := ih (fun _ h => included (List.mem_cons_of_mem _ h))
        refine ⟨max (entry.certificate.nativeDepth control) fuel, ?_⟩
        intro other member type lookup
        rcases List.mem_cons.mp member with rfl | member
        · have same := lookup.uniq canonical.property
          subst type
          exact ⟨entry, bounded, Nat.le_max_left _ _⟩
        · obtain ⟨entry, bounded, controlled⟩ := tail other member type lookup
          exact ⟨entry, bounded, Nat.le_trans controlled (Nat.le_max_right _ _)⟩
    exact collect _ (fun _ h => h)
  have collect : ∀ count, count ≤ source.length →
      ∃ fuel, ∀ index, index < count → ∀ need ∈ available index, ∀ sourceType,
        Lookup source index sourceType →
          ∃ entry : ValuationEntry env U registry target locals σ τ available index need sourceType,
            Within budgets entry.certificate.nativeDepth ∧ entry.certificate.nativeDepth control ≤ fuel := by
    intro count bounded
    induction count with
    | zero => exact ⟨0, by intro _ h; omega⟩
    | succ count ih =>
      obtain ⟨previous, tail⟩ := ih (by omega)
      obtain ⟨next, head⟩ := atIndex count (by omega)
      refine ⟨max previous next, ?_⟩
      intro index hi need member type lookup
      by_cases equal : index = count
      · subst index
        obtain ⟨entry, bounded, controlled⟩ := head need member type lookup
        exact ⟨entry, bounded, Nat.le_trans controlled (Nat.le_max_right _ _)⟩
      · obtain ⟨entry, bounded, controlled⟩ := tail index (by omega) need member type lookup
        exact ⟨entry, bounded, Nat.le_trans controlled (Nat.le_max_left _ _)⟩
  obtain ⟨fuel, entries⟩ := collect source.length (Nat.le_refl _)
  refine ⟨fuel, ⟨?_⟩⟩
  intro index need member type lookup
  obtain ⟨entry, bounded, controlled⟩ := entries index lookup.lt need member type lookup
  refine ⟨entry, ?_⟩
  intro filter limit present
  rcases List.mem_cons.mp present with equal | present
  · cases equal; exact controlled
  · exact bounded filter limit present

theorem Fits.enlargeControl {control : Name → Bool} {a b : Nat} (bound : a ≤ b)
    (fits : Fits ((control, a) :: budgets) env U registry source target locals σ τ available) :
    Fits ((control, b) :: budgets) env U registry source target locals σ τ available := by
  constructor
  intro index need member type lookup
  obtain ⟨entry, bounded⟩ := fits.entry index need member type lookup
  refine ⟨entry, ?_⟩
  intro filter fuel present
  rcases List.mem_cons.mp present with equal | present
  · cases equal; exact Nat.le_trans (bounded _ _ List.mem_cons_self) bound
  · exact bounded _ _ (List.mem_cons_of_mem _ present)

theorem PairedFits.finiteControl (control : Name → Bool)
    (fits : PairedFits budgets env U registry source target locals σ τ available) :
    ∃ fuel, PairedFits ((control, fuel) :: budgets) env U registry source target locals σ τ available := by
  obtain ⟨left, forward⟩ := fits.forward.finiteControl control
  obtain ⟨right, backward⟩ := fits.backward.finiteControl control
  exact ⟨max left right, forward.enlargeControl (Nat.le_max_left _ _),
    backward.enlargeControl (Nat.le_max_right _ _)⟩

/-- Forget only budget proof fields; the semantic result, observer and type
certificate are the SAME witnesses. -/
def Result.toStaged
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right type : VExpr} {demand : Profile n}
    {budgets : Budgets} {filter : Name → Bool} {fuel : Nat}
    (member : (filter, fuel) ∈ budgets)
    (result : Result budgets env U registry target locals σ τ available left right type demand) :
    Staged.Result filter fuel env U registry target locals σ τ available left right type demand where
  toGradedTransferResult := result.toGradedTransferResult
  observationBound := result.observationBound filter fuel member
  certificateBound := result.certificateBound filter fuel member

end Lean4Lean.AnchoredSource.Adapted.Budgeted
