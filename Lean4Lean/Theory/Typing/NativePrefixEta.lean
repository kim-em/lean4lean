import Lean4Lean.Theory.Typing.NativePrefixSpecialization

/-! Opening one native argument with a fresh variable is exactly the next
residual binder of the same generated prefix program. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema VEnv
variable {type : VExpr} {levels : List VLevel}

private theorem supplyType_open (args : List VExpr) (type : VExpr) :
    supplyType (args.map VExpr.lift ++ [VExpr.bvar 0]) type.lift =
      (supplyType args type).bind (fun residual => match residual with
        | .forallE _ body => some body
        | _ => none) := by
  rw [supplyType_append]
  have hr := supplyType_rename args type (.skip .refl)
  simp only [← lift_eq_lift'] at hr
  rw [hr]
  cases supplyType args type with
  | none => rfl
  | some residual =>
    cases residual <;> try rfl
    simp only [Option.map_some, Option.bind_some, supplyType, liftN]
    rw [inst_liftN_bvar]

private theorem vars_succ (n : Nat) : vars (n+1) 0 = .bvar n :: vars n 0 := by
  simp only [vars, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, Nat.zero_add]

/-- Success after opening the next argument with a fresh variable comes
from the previous prefix. Every reconstruction and capture is identical;
only the next domain moves from the caller context to the program telescope. -/
theorem prefixProgram_open_inv {data : NativeRecursorData}
    {args : List VExpr} {late : PrefixProgram}
    (htype : data.recursorType = some type) (hclosed : type.Closed)
    (hLate : data.prefixProgram U levels (args.map VExpr.lift ++ [VExpr.bvar 0]) = some late) :
    ∃ domain, data.prefixProgram U levels args =
      some { late with domains := domain :: late.domains } := by
  have hbound := (prefixProgram_spec hLate).1
  simp only [List.length_append, List.length_map, List.length_singleton] at hbound
  let n := data.majorOffset - args.length
  have hearlyLen : data.majorOffset + 1 - args.length = n + 1 := by dsimp [n]; omega
  have hlateLen : data.majorOffset + 1 - (args.map VExpr.lift ++ [VExpr.bvar 0]).length = n := by
    simp only [List.length_append, List.length_map, List.length_singleton]; dsimp [n]; omega
  have htypeClosed : (type.instL levels).lift = type.instL levels := hclosed.instL.lift_eq
  have hsupply := supplyType_open args (type.instL levels)
  rw [htypeClosed] at hsupply
  unfold prefixProgram at hLate ⊢
  dsimp only at hLate ⊢
  split at hLate <;> try contradiction
  rename_i hguard
  have hearlyGuard : (levels.length != data.uvars || args.length > data.majorOffset) = false := by
    simp at hguard ⊢
    exact ⟨hguard.1, by omega⟩
  rw [if_neg (by simp [hearlyGuard])]
  simp only [bind, htype, Option.bind_some, hsupply, hlateLen] at hLate
  cases hs : supplyType args (type.instL levels) with
  | none => simp [hs] at hLate
  | some residual =>
    cases residual <;> simp only [hs, Option.bind_some] at hLate <;> try contradiction
    rename_i domain body
    simp only [bind, Option.bind_eq_some_iff] at hLate
    obtain ⟨⟨domains, result⟩, hdomains, constructor, hconstructor, source, hsource,
      fields, hfields, equation, hequation, eqbody, hbody, hLate⟩ := hLate
    split at hLate <;> try contradiction
    rename_i hcapture
    cases hLate
    refine ⟨domain, ?_⟩
    have hall : (args.map VExpr.lift ++ [VExpr.bvar 0]).map (·.liftN n) ++ vars n 0 =
        args.map (·.liftN (n+1)) ++ vars (n+1) 0 := by
      simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons,
        List.map_nil, liftN, liftVar_base', List.singleton_append, List.append_assoc,
        vars_succ, liftN_liftN, Nat.add_comm 1, Nat.zero_add]
    simp only [hall] at hconstructor hcapture
    simp only [bind, htype, Option.bind_some, hs, hearlyLen, takeForalls, hdomains,
      Option.pure_def, hconstructor, hsource, hfields, hequation, hbody]
    simp only [if_neg hcapture, hall]

end Lean4Lean.InductiveSignature.NativeRecursorData
