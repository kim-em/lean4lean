import Lean4Lean.Theory.Typing.AnchoredFamilySeededAlignment

/-! Retained family rows keep their complete frozen argument requests. At
the terminal source context each request is an actual variable leaf, in
reverse declaration order. These leaves are available in the exact ledger
used by the original declaration children. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Source positions are counted from the end of the declared telescope;
the demands retain their original, possibly different, finite ranks. -/
def FamilyKey.captureFootprint : List FamilyKey → Footprint
  | [] => []
  | key :: keys => (keys.length, ⟨key.rank, key.key.input⟩) :: FamilyKey.captureFootprint keys

/-- Every old ledger entry survives all subsequent declared binders at its
literal shifted source position. -/
theorem FamilySeededCodeRows.terminal_mem
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys)
    {index : Nat} {need : Need} (member : need ∈ available index) :
    need ∈ rows.terminalValuation (keys.length + index) := by
  induction rows generalizing index with
  | nil => simpa only [FamilySeededCodeRows.terminalValuation, List.length_nil, Nat.zero_add] using member
  | cons original row admission extra bounded covered inputPresent tail ih =>
    have later := ih (index := index + 1) member
    simpa only [FamilySeededCodeRows.terminalValuation, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later

/-- Availability covers the full argument demand, not merely whichever
atoms appeared in the terminal type certificate. -/
theorem FamilySeededCodeRows.captureAvailable
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys) :
    (FamilyKey.captureFootprint keys).Available rows.terminalValuation := by
  induction rows with
  | nil => intro index need member; cases member
  | cons original row admission extra bounded covered inputPresent tail ih =>
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      simpa only [Nat.add_zero, FamilySeededCodeRows.terminalValuation] using
        tail.terminal_mem (index := 0) inputPresent
    · exact ih index need member

theorem FamilySeededCodeRows.terminalLocals_eq
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys)
    (count : Nat) (localNames : locals = List.range count) :
    rows.terminalLocals = List.range (count + keys.length) := by
  induction rows generalizing count with
  | nil => simpa only [FamilySeededCodeRows.terminalLocals, List.length_nil, Nat.add_zero] using localNames
  | cons original row admission extra bounded covered inputPresent tail ih =>
    have names := (congrArg Locals.push localNames).trans
      (show Locals.push (List.range count) = List.range (count + 1) by
        simp only [List.range_succ_eq_map, Locals.push])
    simpa only [FamilySeededCodeRows.terminalLocals, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (count + 1) names

end Lean4Lean.AnchoredSource.Adapted
