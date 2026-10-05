import Lean4Lean.Theory.Typing.SingletonReconstructionLemmas
import Lean4Lean.Theory.Inductive.NativePrefixProgram
import Lean4Lean.Theory.Typing.NativePrefixTyping

/-! Term renaming of the actual native prefix generator and its remaining
binder telescope. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema
variable {levels : List VLevel} {args : List VExpr} {type : VExpr}

/-- Rename only the outer context of a telescope, fixing each preceding
binder as its domain is visited. -/
def renameDomains : Lift → List VExpr → List VExpr
  | _, [] => []
  | ρ, d :: ds => d.lift' ρ :: renameDomains ρ.cons ds

@[simp] theorem renameDomains_length (ρ : Lift) (ds : List VExpr) :
    (renameDomains ρ ds).length = ds.length := by
  induction ds generalizing ρ <;> simp [renameDomains, *]

private theorem consN_cons (ρ : Lift) (n : Nat) :
    ρ.cons.consN n = ρ.consN (n + 1) := by
  change (ρ.consN 1).consN n = _
  rw [Lift.consN_consN, Nat.add_comm]

theorem supplyType_lift' (H : supplyType args type = some output) :
    supplyType (args.map (·.lift' ρ)) (type.lift' ρ) = some (output.lift' ρ) := by
  induction args generalizing type with
  | nil => cases H; rfl
  | cons arg args ih =>
    cases type <;> try contradiction
    simp only [supplyType, List.map_cons, lift']
    rw [← lift'_inst_hi]
    exact ih H

theorem takeForalls_lift' (H : takeForalls count type = some (domains, result)) :
    takeForalls count (type.lift' ρ) =
      some (renameDomains ρ domains, result.lift' (ρ.consN count)) := by
  induction count generalizing type domains result ρ with
  | zero => cases H; rfl
  | succ count ih =>
    cases type <;> try contradiction
    simp only [takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, hb, he⟩ := H
    cases he
    simp only [lift', takeForalls, bind, ih hb, Option.bind_some, Option.pure_def,
      renameDomains, consN_cons]


/-- Term renaming preserves both success and failure of native telescope
specialization. It cannot create a forall node where none existed. -/
theorem supplyType_rename (args : List VExpr) (type : VExpr) (ρ : Lift) :
    supplyType (args.map (·.lift' ρ)) (type.lift' ρ) =
      (supplyType args type).map (·.lift' ρ) := by
  induction args generalizing type with
  | nil => rfl
  | cons arg args ih =>
    cases type <;> try rfl
    simp only [supplyType, List.map_cons, lift']
    rw [← lift'_inst_hi]
    exact ih _

theorem takeForalls_rename (count : Nat) (type : VExpr) (ρ : Lift) :
    takeForalls count (type.lift' ρ) = (takeForalls count type).map
      (fun (ds, body) => (renameDomains ρ ds, body.lift' (ρ.consN count))) := by
  induction count generalizing type ρ with
  | zero => rfl
  | succ count ih =>
    cases type <;> try rfl
    simp only [lift', takeForalls, ih]
    cases takeForalls count _ <;> simp [bind, renameDomains, consN_cons]

/-- Every term field records its exact position relative to the remaining
native telescope. The stored equation and universe occurrence stay fixed. -/
def PrefixProgram.rename (program : PrefixProgram) (ρ : Lift) : PrefixProgram :=
  { program with
    domains := renameDomains ρ program.domains
    result := program.result.lift' (ρ.consN program.domains.length)
    constructor := program.constructor.lift' (ρ.consN program.domains.length)
    captures := program.captures.map (·.lift' (ρ.consN program.domains.length)) }

private theorem liftN_lift'_consN (e : VExpr) (n : Nat) (ρ : Lift) :
    (e.lift' ρ).liftN n = (e.liftN n).lift' (ρ.consN n) := by
  simp only [← lift'_consN_skipN (k := 0), Lift.consN]
  rw [← lift'_comp, ← lift'_comp, Lift.skipN_comp_consN]
  simp only [Lift.comp_skipN, Lift.refl_comp, Lift.comp]

private theorem vars_lift'_consN (n : Nat) (ρ : Lift) :
    (vars n 0).map (·.lift' (ρ.consN n)) = vars n 0 := by
  have hfix : (ρ.consN n).Fixes n := by
    induction n <;> simp [Lift.consN, Lift.Fixes, *]
  conv => rhs; rw [← List.map_id (l := vars n 0)]
  apply List.map_congr_left
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  apply VExpr.ClosedN.lift'_eq (k := n)
  · simpa only [VExpr.ClosedN, Nat.zero_add] using hi
  · exact hfix

private theorem vars_length (n k : Nat) : (vars n k).length = n := by simp [vars]

private theorem mkApps_lift' (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).lift' ρ = mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih => exact ih (.app fn arg)

/-- Renaming supplied arguments renames the entire generated residual
program under its own remaining binders. The original native type is closed;
all selector closure facts are derived from successful source extraction. -/
theorem prefixProgram_lift' {data : NativeRecursorData} {nativeType : VExpr}
    (htype : data.recursorType = some nativeType) (hclosed : nativeType.Closed)
    (H : data.prefixProgram U levels args = some program) :
    data.prefixProgram U levels (args.map (·.lift' ρ)) = some (program.rename ρ) := by
  unfold prefixProgram at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, htype, Option.bind_some, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake,
    constructor, hconstructor, source, hsource, fields, hfields,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptureCount
  cases H
  have hlen := takeForalls_length htake
  have hsupply' := supplyType_lift' (ρ := ρ) hsupply
  rw [(hclosed.instL (ls := levels)).lift'_eq Lift.Fixes.zero] at hsupply'
  have htake' := takeForalls_lift' (ρ := ρ) htake
  let remaining := data.majorOffset + 1 - args.length
  have hall :
      (args.map (·.lift' ρ)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (·.lift' (ρ.consN remaining)) := by
    simp only [List.map_append, List.map_map, Function.comp_def,
      liftN_lift'_consN, vars_lift'_consN]
  have hconstructor' := reconstructCanonical_lift' (ρ := ρ.consN remaining) hconstructor
  rw [← hall] at hconstructor'
  dsimp only [remaining] at hconstructor'
  simp only [bind, htype, Option.bind_some, hsupply', htake', hconstructor', hsource,
    hfields, hequation, hbody, List.length_map, List.length_append, List.length_take,
    List.length_drop, List.length_cons, List.length_nil, vars_length] at hcaptureCount ⊢
  have hscoped := projectionData_scoped hsource
  have hselectors := source.reconstructionPrefix_closed hscoped (by simp)
    (by simpa using hscoped.fields) (by simp) hfields
  rw [if_neg hcaptureCount]
  simp only [Option.pure_def, Option.some.injEq, PrefixProgram.rename, PrefixProgram.mk.injEq,
    hlen, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_map, Function.comp_def, List.map_take]
  congr 1
  apply List.map_congr_left
  intro field hf
  rw [mkApps_lift', (hselectors field hf).lift'_eq Lift.Fixes.zero]
  have hn : args.length ≤ data.majorOffset := by
    by_cases hn : args.length ≤ data.majorOffset
    · exact hn
    · exact (hguard (by simp [show data.majorOffset < args.length by omega])).elim
  have hzero : (.bvar 0 : VExpr).lift' (ρ.consN (data.majorOffset + 1 - args.length)) = .bvar 0 := by
    have heq : data.majorOffset + 1 - args.length = (data.majorOffset - args.length) + 1 := by omega
    rw [heq]
    rfl
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_drop, hzero, List.map_map, Function.comp_def]

/-- Lifting does not turn a rejected native prefix into a generated one. -/
theorem prefixProgram_isSome_lift' {data : NativeRecursorData} {nativeType : VExpr}
    (htype : data.recursorType = some nativeType) (hclosed : nativeType.Closed) :
    (data.prefixProgram U levels (args.map (·.lift' ρ))).isSome =
      (data.prefixProgram U levels args).isSome := by
  have hsupply := supplyType_rename args (nativeType.instL levels) ρ
  rw [(hclosed.instL (ls := levels)).lift'_eq Lift.Fixes.zero] at hsupply
  unfold prefixProgram
  simp only [List.length_map]
  split
  · rfl
  · simp only [bind, htype, Option.bind_some, hsupply]
    cases hs : supplyType args (nativeType.instL levels) with
    | none => rfl
    | some residual =>
      simp only [Option.map_some, Option.bind_some, takeForalls_rename]
      cases ht : takeForalls (data.majorOffset + 1 - args.length) residual with
      | none => rfl
      | some pair =>
        obtain ⟨domains, result⟩ := pair
        simp only [Option.map_some, Option.bind_some]
        have hall :
            (args.map (·.lift' ρ)).map (·.liftN (data.majorOffset + 1 - args.length)) ++
              vars (data.majorOffset + 1 - args.length) 0 =
            (args.map (·.liftN (data.majorOffset + 1 - args.length)) ++
              vars (data.majorOffset + 1 - args.length) 0).map
                (·.lift' (ρ.consN (data.majorOffset + 1 - args.length))) := by
          simp only [List.map_append, List.map_map, Function.comp_def,
            liftN_lift'_consN, vars_lift'_consN]
        rw [hall, reconstructCanonical_rename]
        cases data.reconstructCanonical U levels
          (args.map (·.liftN (data.majorOffset + 1 - args.length)) ++
            vars (data.majorOffset + 1 - args.length) 0) with
        | none => rfl
        | some ctor =>
          simp only [Option.map_some, Option.bind_some]
          cases hsource : data.schema.projectionData data.owner (data.sourceLevels levels) with
          | none => rfl
          | some source =>
            simp only [Option.bind_some]
            cases source.reconstructionPrefix data.block data.owner.val (data.sourceLevels levels)
              source.fields (List.replicate source.fields.length .zero) [] with
            | none => rfl
            | some fields =>
              simp only [Option.bind_some]
              cases data.singletonEquation with
              | none => rfl
              | some equation =>
                simp only [Option.bind_some]
                cases EquationBody.extract equation.lhs equation.rhs equation.type with
                | none => rfl
                | some body =>
                  simp only [Option.bind_some, List.length_append, List.length_map,
                    List.length_take]
                  split <;> rfl

/-- Both successful output and failure commute with occurrence renaming. -/
theorem prefixProgram_rename {data : NativeRecursorData} {nativeType : VExpr}
    (htype : data.recursorType = some nativeType) (hclosed : nativeType.Closed) :
    data.prefixProgram U levels (args.map (·.lift' ρ)) =
      (data.prefixProgram U levels args).map (·.rename ρ) := by
  cases h : data.prefixProgram U levels args with
  | none =>
    have hh := prefixProgram_isSome_lift' (U := U) (levels := levels) (args := args) (ρ := ρ) htype hclosed
    rw [h] at hh
    cases he : data.prefixProgram U levels (args.map (·.lift' ρ)) <;> simp_all
  | some program => exact prefixProgram_lift' htype hclosed h

theorem wrapLams_renameDomains (domains : List VExpr) (body : VExpr) (ρ : Lift) :
    (wrapLams domains body).lift' ρ =
      wrapLams (renameDomains ρ domains) (body.lift' (ρ.consN domains.length)) := by
  induction domains generalizing ρ with
  | nil => rfl
  | cons domain domains ih =>
    change VExpr.lam (domain.lift' ρ) ((wrapLams domains body).lift' ρ.cons) =
      VExpr.lam (domain.lift' ρ) (wrapLams (renameDomains ρ.cons domains)
        (body.lift' (ρ.consN (domains.length + 1))))
    rw [ih, consN_cons]

theorem wrapForalls_renameDomains (domains : List VExpr) (body : VExpr) (ρ : Lift) :
    (wrapForalls domains body).lift' ρ =
      wrapForalls (renameDomains ρ domains) (body.lift' (ρ.consN domains.length)) := by
  induction domains generalizing ρ with
  | nil => rfl
  | cons domain domains ih =>
    change VExpr.forallE (domain.lift' ρ) ((wrapForalls domains body).lift' ρ.cons) =
      VExpr.forallE (domain.lift' ρ) (wrapForalls (renameDomains ρ.cons domains)
        (body.lift' (ρ.consN (domains.length + 1))))
    rw [ih, consN_cons]

theorem PrefixProgram.rename_type (program : PrefixProgram) (ρ : Lift) :
    (program.rename ρ).type = program.type.lift' ρ := by
  simp only [PrefixProgram.rename, PrefixProgram.type, wrapForalls_renameDomains]

theorem PrefixProgram.rename_rhs {program : PrefixProgram}
    (hbody : program.equationBody.rhs.ClosedN program.captures.length) :
    (program.rename ρ).rhs = program.rhs.lift' ρ := by
  simp only [PrefixProgram.rename, PrefixProgram.rhs, wrapLams_renameDomains]
  rw [instantiateParams_lift' (hbody.instL (ls := program.levels))]

/-- Context renaming follows exactly the generated residual telescope. -/
theorem renameDomains_context (domains : List VExpr) (W : Ctx.Lift' ρ Γ Γ') :
    Ctx.Lift' (ρ.consN domains.length)
      (domains.reverse ++ Γ) ((renameDomains ρ domains).reverse ++ Γ') := by
  induction domains generalizing ρ Γ Γ' with
  | nil => exact W
  | cons domain domains ih =>
    simpa only [renameDomains, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, consN_cons] using ih (ρ := ρ.cons) W.cons

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData

theorem nativeEtaBody_lift' (n : Nat) (e : VExpr) (ρ : Lift) :
    nativeEtaBody n (e.lift' ρ) = (nativeEtaBody n e).lift' (ρ.consN n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nativeEtaBody_succ, nativeEtaBody_succ, ih]
    simp only [VExpr.lift', Lift.consN, Lift.liftVar]
    exact congrArg (fun fn => fn.app (.bvar 0)) (liftN_lift'_consN _ 1 _)

end Lean4Lean.VEnv
