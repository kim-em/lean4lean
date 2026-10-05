import Lean4Lean.Theory.Typing.AnchoredNativeInitialRouting

/-! Finite source observation ledgers for actual native/capture arguments.
Each entry is an actual observer at the original realization. Projection,
merging and prefix embedding preserve these witnesses literally. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive NativeArgumentLedger (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) : Footprint → Type where
  | nil : NativeArgumentLedger env U registry target locals σ available arguments []
  | cons {index : Nat} {need : Need} {footprint required : Footprint}
      (bound : index < arguments.length)
      (observation : Obs env U registry target locals σ
        arguments[arguments.length - 1 - index] need.profile footprint)
      (resources : footprint.Available available)
      (tail : NativeArgumentLedger env U registry target locals σ available arguments required) :
      NativeArgumentLedger env U registry target locals σ available arguments ((index, need) :: required)

def NativeArgumentLedger.append
    (left : NativeArgumentLedger env U registry target locals σ available arguments first)
    (right : NativeArgumentLedger env U registry target locals σ available arguments second) :
    NativeArgumentLedger env U registry target locals σ available arguments (first ++ second) :=
  match left with
  | .nil => right
  | .cons bound observation resources tail => .cons bound observation resources (tail.append right)

theorem NativeArgumentLedger.observation
    (ledger : NativeArgumentLedger env U registry target locals σ available arguments required)
    (member : (index, need) ∈ required) :
    ∃ bound : index < arguments.length, ∃ footprint,
      Nonempty (Obs env U registry target locals σ
        arguments[arguments.length - 1 - index] need.profile footprint) ∧
        footprint.Available available := by
  induction ledger with
  | nil => cases member
  | cons bound observation resources tail ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨bound, _, ⟨observation⟩, resources⟩
    · exact ih member

theorem NativeArgumentLedger.scoped
    (ledger : NativeArgumentLedger env U registry target locals σ available arguments required) :
    Footprint.Scoped arguments.length required := by
  intro index need member
  exact (ledger.observation member).choose

/-- Actual cut observers, not target semantics, populate the finite ledger. -/
theorem ParamsFootprint.argumentLedger
    (cuts : ParamsFootprint env U registry target locals σ arguments before after)
    (resources : before.Available available)
    (scope : Footprint.Scoped arguments.length after) :
    Nonempty (NativeArgumentLedger env U registry target locals σ available arguments after) := by
  suffices ∀ part, (∀ entry ∈ part, entry ∈ after) →
      Nonempty (NativeArgumentLedger env U registry target locals σ available arguments part) from
    this after (fun _ h => h)
  intro part included
  induction part with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨index, need⟩ := entry
    have member := included _ List.mem_cons_self
    obtain ⟨footprint, ⟨observation⟩, leaves⟩ := cuts.argument (scope index need member) member
    obtain ⟨tail⟩ := ih (fun entry hm => included entry (List.mem_cons_of_mem _ hm))
    exact ⟨.cons (scope index need member) observation
      (fun i n hm => resources i n (leaves i n hm)) tail⟩

/-- Shift a prefix ledger into the full native tuple without changing a
single original source observation. -/
noncomputable def NativeArgumentLedger.intoPrefix
    {arguments prefixArguments : List VExpr}
    (prefix_eq : prefixArguments = arguments.take count) (count_le : count ≤ arguments.length)
    (ledger : NativeArgumentLedger env U registry target locals σ available prefixArguments required) :
    NativeArgumentLedger env U registry target locals σ available arguments
      (Footprint.sourceLift (.skipN .refl (arguments.length - count)) required) := by
  subst prefixArguments
  induction ledger with
  | nil => exact .nil
  | @cons index need footprint required bound observation resources tail ih =>
    have small : index < count := by simpa only [List.length_take, Nat.min_eq_left count_le] using bound
    have hi : index + (arguments.length - count) < arguments.length := by omega
    have position : arguments.length - 1 - (index + (arguments.length - count)) = count - 1 - index := by omega
    have observed : Obs env U registry target locals σ
        arguments[arguments.length - 1 - (index + (arguments.length - count))] need.profile footprint := by
      simpa only [List.length_take, Nat.min_eq_left count_le, List.getElem_take, position] using observation
    simpa only [Footprint.sourceLift, List.map_cons, Lift.liftVar_skipN, Lift.liftVar,
      Nat.zero_add, Nat.add_comm] using NativeArgumentLedger.cons hi observed resources ih

/-- Requirements on the removed final argument are consumed; preceding
argument positions decrease by one. -/
def externalArguments : Footprint → Footprint
  | [] => []
  | (0, _) :: rest => externalArguments rest
  | (index + 1, need) :: rest => (index, need) :: externalArguments rest

/-- The outside of a binder pack is fixed by its actual ordered leaves. -/
theorem BinderPack.externalArguments (pack : BinderPack n input required outside) :
    outside = externalArguments required := by
  induction pack with
  | nil => rfl
  | «local» need bound pack ih => exact ih
  | external index need pack ih => exact congrArg ((index, need) :: ·) ih

noncomputable def NativeArgumentLedger.withoutLast
    (ledger : NativeArgumentLedger env U registry target locals σ available (arguments ++ [last]) required) :
    NativeArgumentLedger env U registry target locals σ available arguments (externalArguments required) := by
  induction ledger with
  | nil => exact .nil
  | @cons index need footprint required bound observation resources tail ih =>
    cases index with
    | zero => exact ih
    | succ index =>
      have hi : index < arguments.length := by simpa only [List.length_append, List.length_singleton,
        Nat.add_lt_add_iff_right] using bound
      have position : (arguments ++ [last]).length - 1 - (index + 1) = arguments.length - 1 - index := by
        simp only [List.length_append, List.length_singleton]; omega
      have observed : Obs env U registry target locals σ arguments[arguments.length - 1 - index]
          need.profile footprint := by
        have beforeBound : (arguments ++ [last]).length - 1 - (index + 1) < arguments.length := by
          simp only [List.length_append, List.length_singleton]; omega
        have same : (arguments ++ [last])[(arguments ++ [last]).length - 1 - (index + 1)] =
            arguments[arguments.length - 1 - index] := by
          simp only [position]
          exact List.getElem_append_left (by omega)
        exact same ▸ observation
      exact .cons hi observed resources ih

theorem NativeArgumentLedger.lastSeed
    (ledger : NativeArgumentLedger env U registry target locals σ available (arguments ++ [last]) required)
    (minimum : Nat) :
    Nonempty (NativeSeedCover env U registry target locals σ available last
      (argumentNeeds required 0) minimum) := by
  apply NativeArgumentSeed.collect
  intro need member
  obtain ⟨bound, footprint, ⟨observation⟩, resources⟩ := ledger.observation (mem_argumentNeeds.mp member)
  exact ⟨footprint, ⟨by simpa using observation⟩, resources⟩

/-- Concrete packing follows the exact required list. Its local demand is
covered by the collected field seed, and its outside is the retained ledger. -/
theorem NativeSeedCover.packLast
    (cover : NativeSeedCover env U registry target locals σ available argument
      (argumentNeeds required 0) minimum) :
    ∃ packed, BinderPack cover.seed.rank packed required (externalArguments required) ∧
      ∀ atom ∈ packed.atoms, atom ∈ cover.seed.demand.atoms := by
  suffices ∀ part, (∀ need, (0, need) ∈ part →
      need.rank ≤ cover.seed.rank ∧ ∀ atom ∈ (need.atGrade cover.seed.rank).atoms,
        atom ∈ cover.seed.demand.atoms) →
      ∃ packed, BinderPack cover.seed.rank packed part (externalArguments part) ∧
        ∀ atom ∈ packed.atoms, atom ∈ cover.seed.demand.atoms from
    this required (fun need member => cover.covered need (mem_argumentNeeds.mpr member))
  intro part included
  induction part with
  | nil => exact ⟨.empty, .nil, fun _ h => nomatch h⟩
  | cons entry rest ih =>
    obtain ⟨index, need⟩ := entry
    obtain ⟨packed, pack, covered⟩ := ih (fun need hm => included need (List.mem_cons_of_mem _ hm))
    cases index with
    | zero =>
      have demanded := included need List.mem_cons_self
      exact ⟨(need.atGrade cover.seed.rank).union packed, .local need demanded.1 pack,
        fun atom hm => (List.mem_append.mp hm).elim (demanded.2 atom) (covered atom)⟩
    | succ index => exact ⟨packed, .external index need pack, covered⟩

/-- The initial equation-context ledger comes directly from the actual
variable leaves of the body observation. Each original leaf is retained. -/
theorem NativeArgumentLedger.variables
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (scope : Footprint.Scoped count required) (resources : required.Available available) :
    Nonempty (NativeArgumentLedger env U registry target locals σ available
      (InductiveSignature.vars count 0) required) := by
  induction required with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨index, need⟩ := entry
    have bound := scope index need List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun i n hm => scope i n (List.mem_cons_of_mem _ hm))
      (fun i n hm => resources i n (List.mem_cons_of_mem _ hm))
    have length_eq : (InductiveSignature.vars count 0).length = count := by
      simp [InductiveSignature.vars]
    have position : count - 1 - (count - 1 - index) = index := by omega
    have observation : Obs env U registry target locals σ
        (InductiveSignature.vars count 0)[(InductiveSignature.vars count 0).length - 1 - index]
        need.profile [(index, need)] := by
      simpa only [InductiveSignature.vars, List.length_map, List.length_reverse,
        List.length_range, List.getElem_map, List.getElem_reverse,
        List.getElem_range, Nat.zero_add, position] using
          Obs.var (env := env) (U := U) (registry := registry) (target := target)
            locals σ index need.profile
    refine ⟨.cons (by simpa only [length_eq] using bound) observation ?_ tail⟩
    intro i n hm
    have same := List.mem_singleton.mp hm
    cases same
    exact resources index need List.mem_cons_self

end Lean4Lean.AnchoredSource.Adapted
