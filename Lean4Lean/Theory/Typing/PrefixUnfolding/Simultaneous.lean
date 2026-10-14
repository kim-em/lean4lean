import Lean4Lean.Theory.Typing.PrefixUnfolding.Abstraction
import Lean4Lean.Theory.Typing.PrefixUnfolding.Layout
import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping

/-! # Simultaneous substitution of generated singleton programs

Generation commutes with arbitrary simultaneous substitutions. This is a syntax
theorem: it does not require the substituted arguments to be typed or the family
guard to hold. Every residual annotation is substituted at its own binder depth.
-/
namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv RecursorSchema
variable {levels : List VLevel}

/-- Supply through a Pi telescope commutes with simultaneous substitution. -/
theorem supplyType_subst (H : supplyType args type = some output) :
    supplyType (args.map (·.subst σ)) (type.subst σ) = some (output.subst σ) := by
  induction args generalizing type with
  | nil => cases H; rfl
  | cons a args ih =>
    cases type <;> try contradiction
    simpa only [supplyType, List.map_cons, VExpr.subst, subst_inst] using ih H

/-- Peeling a telescope commutes with substitution beneath each preceding binder. -/
theorem takeForalls_subst
    (H : VExpr.takeForalls count type = some (domains, result)) :
    VExpr.takeForalls count (type.subst σ) =
      some (domains.mapIdx fun i A => A.subst (σ.liftN i),
        result.subst (σ.liftN domains.length)) := by
  have hl := VExpr.takeForalls_domains_length H
  rw [takeForalls_sound H, subst_wrapForalls, ← hl]
  simpa only [List.length_mapIdx] using takeForalls_wrapForalls
    (domains.mapIdx fun i A => A.subst (σ.liftN i)) (result.subst (σ.liftN domains.length))

/-- Substitute through all open components of a generated program. -/
def PrefixUnfolding.subst (program : PrefixUnfolding) (σ : VExpr.Subst) : PrefixUnfolding :=
  { program with
    domains := program.domains.mapIdx fun i A => A.subst (σ.liftN i)
    result := program.result.subst (σ.liftN program.domains.length)
    constructor := program.constructor.subst (σ.liftN program.domains.length)
    captures := program.captures.map (·.subst (σ.liftN program.domains.length)) }

/-- Simultaneous program substitution preserves its literal wrapped type. -/
theorem PrefixUnfolding.subst_type (program : PrefixUnfolding) :
    (program.subst σ).type = program.type.subst σ := by
  simp only [PrefixUnfolding.subst, PrefixUnfolding.type, subst_wrapForalls]

/-- A scoped stored RHS commutes exactly with simultaneous program substitution. -/
theorem PrefixUnfolding.subst_rhs (program : PrefixUnfolding)
    (hc : program.equationBody.rhs.ClosedN program.captures.length) :
    (program.subst σ).rhs = program.rhs.subst σ := by
  simp only [PrefixUnfolding.subst, PrefixUnfolding.rhs, subst_wrapLams,
    instantiateParams_subst (hc.instL (ls := program.levels))]

/-- The fresh residual variable vector is fixed by a substitution lifted under
the whole residual telescope. -/
theorem vars_subst_liftN (count : Nat) (σ : VExpr.Subst) :
    (vars count 0).map (·.subst (σ.liftN count)) = vars count 0 := by
  simp only [vars, List.map_map, Function.comp_def, VExpr.subst_bvar, Nat.zero_add]
  apply List.map_congr_left
  intro i hi
  have hi : i < count := List.mem_range.mp (List.mem_reverse.mp hi)
  simp only [VExpr.Subst.liftN_apply, if_pos hi]

/-- Opened source providers substitute under the exact residual binder count. -/
theorem openedArguments_subst (data : RecursorData) (args : List VExpr) (σ : VExpr.Subst) :
    data.openedArguments (args.map (·.subst σ)) =
      (data.openedArguments args).map
        (·.subst (σ.liftN (data.majorOffset + 1 - args.length))) := by
  simp only [openedArguments, List.length_map, List.map_append, List.map_map,
    Function.comp_def, VExpr.liftN_subst_liftN', vars_subst_liftN]

/-- The actual singleton generator commutes with arbitrary simultaneous
substitution; the fixed equation and body remain the registered ones. -/
theorem singletonUnfolding_subst {data : RecursorData} {recType : VExpr} {env : VEnv}
    {packed : List VLevel} (henv : env.WF) (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (htype : data.recursorType = some recType) (hclosed : recType.Closed)
    (H : data.singletonUnfolding env U levels args = some program) :
    data.singletonUnfolding env U levels (args.map (·.subst σ)) = some (program.subst σ) := by
  unfold singletonUnfolding at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, htype, Option.bind_some, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, ⟨constructor, fields⟩, hrecon,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptureCount
  cases H
  have hlen := VExpr.takeForalls_domains_length htake
  have hsupply' := supplyType_subst (σ := σ) hsupply
  rw [(hclosed.instL (ls := levels)).subst_eq .zero] at hsupply'
  have htake' := takeForalls_subst (σ := σ) htake
  have hn : args.length ≤ data.majorOffset := by
    by_contra hn
    exact hguard (by simp [show data.majorOffset < args.length by omega])
  let remaining := data.majorOffset + 1 - args.length
  have hpos : 0 < remaining := by dsimp [remaining]; omega
  have hall :
      (args.map (·.subst σ)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (·.subst (σ.liftN remaining)) := by
    simp only [List.map_append, List.map_map, Function.comp_def,
      VExpr.liftN_subst_liftN', vars_subst_liftN]
  have hallLen : (args.map (·.liftN remaining) ++ vars remaining 0).length = data.majorOffset + 1 := by
    simp only [List.length_append, List.length_map, vars, List.length_reverse, List.length_range]
    dsimp [remaining]; omega
  have hrecon' := singletonReconstruction_subst (σ := σ.liftN remaining)
    henv hr hlarge hzero hallLen (by simp [VExpr.Subst.liftN_apply, hpos]) hrecon
  rw [← hall] at hrecon'
  dsimp only [remaining] at hrecon'
  have hvarslen (n j : Nat) : (vars n j).length = n := by simp [vars]
  simp only [bind, htype, Option.bind_some, hsupply', htake', hrecon', hequation, hbody,
    List.length_map, List.length_append, List.length_take, hvarslen] at hcaptureCount ⊢
  rw [if_neg hcaptureCount]
  simp only [Option.pure_def, Option.some.injEq, PrefixUnfolding.subst,
    PrefixUnfolding.mk.injEq, hlen, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_take]

end Lean4Lean.InductiveSignature.RecursorData
