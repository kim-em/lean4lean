import Lean4Lean.Theory.Typing.PrefixUnfolding.Abstraction
import Lean4Lean.Theory.Typing.PrefixUnfolding.GenerationSupply

/-! # Reabstracting a checked fresh argument

A prefix check under its supplied fresh binder can be closed by restoring that
binder to the residual telescope. The fully opened checking context is unchanged,
so this operation does not descend its family guard through an unused binder.
The restored program agrees exactly with actual generation at the shorter prefix.
-/
namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr

/-- Restore one supplied fresh binder to the residual telescope. All fully
opened terms and the stored equation are retained exactly. -/
def PrefixUnfolding.prepend (A : VExpr) (program : PrefixUnfolding) : PrefixUnfolding :=
  { program with domains := A :: program.domains }

@[simp] theorem PrefixUnfolding.prepend_type {program : PrefixUnfolding} {A : VExpr} :
    (program.prepend A).type = .forallE A program.type := rfl

@[simp] theorem PrefixUnfolding.prepend_rhs {program : PrefixUnfolding} {A : VExpr} :
    (program.prepend A).rhs = .lam A program.rhs := rfl

@[simp] theorem PrefixUnfolding.prepend_context {program : PrefixUnfolding} {A : VExpr} :
    (program.prepend A).domains.reverse ++ Γ = program.domains.reverse ++ A :: Γ := by
  simp [prepend, List.append_assoc]

/-- Supplying the next fresh variable moves the first residual domain into
the ambient context. The fully opened generated fields remain identical. -/
theorem singletonUnfolding_open_one {env : VEnv} {data : RecursorData}
    {levels : List VLevel} {args : List VExpr} {early late : PrefixUnfolding}
    (henv : env.WF) (hr : VEnv.RecursorRegistered env data)
    (hEarly : data.singletonUnfolding env U levels args = some early)
    (hLate : data.singletonUnfolding env U levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) = some late) :
    ∃ domain, early = late.prepend domain := by
  have hbound := (singletonUnfolding_spec hLate).1
  simp only [List.length_append, List.length_map, List.length_singleton] at hbound
  let n := data.majorOffset - args.length
  have hearlyLen : data.majorOffset + 1 - args.length = n + 1 := by dsimp [n]; omega
  have hlateLen : data.majorOffset + 1 - (args.map VExpr.lift ++ [VExpr.bvar 0]).length = n := by
    simp only [List.length_append, List.length_map, List.length_singleton]; dsimp [n]; omega
  unfold singletonUnfolding at hEarly hLate
  split at hEarly <;> try contradiction
  split at hLate <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hEarly
  obtain ⟨recType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, hrecon, equation, hequation, body, hbody, hEarly⟩ := hEarly
  split at hEarly <;> try contradiction
  rename_i hcaptures
  cases hEarly
  rw [hearlyLen] at htake
  cases residual <;> try contradiction
  rename_i domain residualBody
  simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at htake
  obtain ⟨⟨ds, result⟩, htake, he⟩ := htake
  cases he
  have hsupply' := supplyType_lift' (ρ := .skip .refl) hsupply
  rw [((hr.recursorType_closed henv htype).instL (ls := levels)).lift'_eq Lift.Fixes.zero] at hsupply'
  simp only [← VExpr.lift_eq_lift'] at hsupply'
  change supplyType (args.map VExpr.lift) (recType.instL levels) =
    some (.forallE domain.lift (residualBody.liftN 1 1)) at hsupply'
  have hall : (args.map VExpr.lift ++ [VExpr.bvar 0]).map (·.liftN n) ++ vars n 0 =
      args.map (·.liftN (n + 1)) ++ vars (n + 1) 0 := by
    have hvars : vars (n + 1) 0 = .bvar n :: vars n 0 := by
      simp [vars, List.range_succ, List.reverse_append]
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons,
      List.map_nil, VExpr.lift, VExpr.liftN_liftN, Nat.add_comm 1 n,
      VExpr.liftN, liftVar_base, Nat.add_zero, List.append_assoc,
      List.cons_append, List.nil_append, hvars]
  simp only [bind, htype, Option.bind_some, supplyType_append, hsupply', supplyType,
    VExpr.inst_liftN_bvar, hlateLen, htake, hall, ← hearlyLen, hrecon,
    hequation, hbody, if_neg hcaptures] at hLate
  cases hLate
  exact ⟨domain, rfl⟩

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

/-- Reabstract a supplied fresh variable. Source typing is reconstructed by eta;
every guard and capture typing stays in exactly the same fully opened context.
No strengthening premise is used. -/
theorem unfoldingCheck_prepend_fresh (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f (.forallE A B))
    (H : UnfoldingCheck env U (A :: Γ) (.app f.lift (.bvar 0)) program) :
    UnfoldingCheck env U Γ f (program.prepend A) := by
  obtain ⟨⟨u, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
  have hbody : env.HasType U (A :: Γ) (.app f.lift (.bvar 0)) program.type := H.source_typed
  have hlam : env.HasType U Γ (.lam A (.app f.lift (.bvar 0))) (.forallE A program.type) := .lam hA hbody
  have hf' : env.HasType U Γ f (.forallE A program.type) :=
    hlam.defeqU_l henv hΓ ⟨_, IsDefEq.eta hf⟩
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  have hopen : etaOpen program.domains.length f =
      etaOpen (program.domains.length - 1) (.app f.lift (.bvar 0)) := by
    conv => lhs; rw [show program.domains.length = (program.domains.length - 1) + 1 by omega]
    rfl
  refine { source_typed := hf'
           remaining_nonempty := by simp [PrefixUnfolding.prepend]
           equation_present := H.equation_present
           equation_body := H.equation_body
           levels_wf := H.levels_wf
           levels_length := H.levels_length
           captures_length := H.captures_length
           captures_typed := ?_
           major_prop := ?_
           recursor_lhs := ?_ }
  · simpa [PrefixUnfolding.prepend, List.reverse_cons, List.append_assoc] using H.captures_typed
  · simpa [PrefixUnfolding.prepend, List.reverse_cons, List.append_assoc] using H.major_prop
  · simpa [PrefixUnfolding.prepend, List.append_assoc, hopen] using H.recursor_lhs

/-- An actual prefix at a supplied fresh argument reflects to an actual shorter
prefix. Its restored domain is definitionally equal to the function's given
domain; no family-guard descent or strengthening principle is assumed. -/
theorem prefixUnfold_fresh_argument {name : Name} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ (mkApps (.const name levels) args) (.forallE A B))
    (H : PrefixUnfold env U registry (A :: Γ) name levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) out) :
    ∃ domain, env.IsDefEqU U Γ A domain ∧
      PrefixUnfold env U registry Γ name levels args (.lam domain out) := by
  cases H with
  | intro hreg hr hname hlarge hlevels hzero hg hc =>
    obtain ⟨early, hearly⟩ := singletonUnfolding_anyArity (args' := args) hg (by
      have := (singletonUnfolding_spec hg).1
      simp only [List.length_append, List.length_map, List.length_singleton] at this
      omega)
    obtain ⟨domain, rfl⟩ := singletonUnfolding_open_one henv hr hearly hg
    have ht := hr.prefixType henv hΓ hlevels hearly (by
      simpa only [hname] using
        (show VExpr.WF env U Γ (mkApps (.const name levels) args) from ⟨_, hf⟩))
    rw [hname] at ht
    obtain ⟨⟨_, hdom⟩, _⟩ := (hf.uniqU henv hΓ ht).forallE_inv henv hΓ
    have hc' := hc.defeqDFC henv hΓ (.succ .zero hdom)
    have hf' : env.HasType U Γ (mkApps (.const name levels) args)
        (.forallE domain _) := ht
    have hc'' := unfoldingCheck_prepend_fresh henv hΓ hf' (by
      simpa only [mkApps_append, mkApps_cons, mkApps_nil, lift, liftN_mkApps, liftN] using hc')
    exact ⟨domain, ⟨_, hdom⟩, .intro hreg hr hname hlarge hlevels hzero hearly hc''⟩

end Lean4Lean.VEnv.Strengthening
