import Lean4Lean.Theory.Typing.Strengthening.PrefixFreshAbstraction
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift

/-! # Fresh-argument abstraction for quotient prefixes

The quotient generator has the same opening identity as singleton recursors.
Its actual checked rule therefore reflects across one supplied fresh argument.
-/
namespace Lean4Lean.QuotPrefixUnfolding
open VExpr InductiveSignature InductiveSignature.RecursorData

/-- Opening the next quotient-lift binder retains all fully opened fields. -/
theorem generate_open_one {levels : List VLevel} {args : List VExpr}
    {early late : PrefixUnfolding}
    (hEarly : generate levels args = some early)
    (hLate : generate levels (args.map VExpr.lift ++ [VExpr.bvar 0]) = some late) :
    ∃ domain, early = late.prepend domain := by
  have hbound := (generate_spec hLate).2.1
  simp only [List.length_append, List.length_map, List.length_singleton] at hbound
  let n := 5 - args.length
  have hearlyLen : 6 - args.length = n + 1 := by dsimp [n]; omega
  have hlateLen : 6 - (args.map VExpr.lift ++ [VExpr.bvar 0]).length = n := by
    simp only [List.length_append, List.length_map, List.length_singleton]; dsimp [n]; omega
  unfold generate at hEarly hLate
  split at hEarly <;> try contradiction
  split at hLate <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hEarly
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, hbody, hEarly⟩ := hEarly
  cases hEarly
  rw [hearlyLen] at htake
  cases residual <;> try contradiction
  rename_i domain residualBody
  simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at htake
  obtain ⟨⟨ds, result⟩, htake, he⟩ := htake
  cases he
  have hclosed : quotLiftConst.type.Closed := by decide
  have hsupply' := supplyType_lift' (ρ := .skip .refl) hsupply
  rw [(hclosed.instL (ls := levels)).lift'_eq Lift.Fixes.zero] at hsupply'
  simp only [← VExpr.lift_eq_lift'] at hsupply'
  change supplyType (args.map VExpr.lift) (quotLiftConst.type.instL levels) =
    some (.forallE domain.lift (residualBody.liftN 1 1)) at hsupply'
  have hall : (args.map VExpr.lift ++ [VExpr.bvar 0]).map (·.liftN n) ++ vars n 0 =
      args.map (·.liftN (n + 1)) ++ vars (n + 1) 0 := by
    have hvars : vars (n + 1) 0 = .bvar n :: vars n 0 := by
      simp [vars, List.range_succ, List.reverse_append]
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons,
      List.map_nil, VExpr.lift, VExpr.liftN_liftN, Nat.add_comm 1 n,
      VExpr.liftN, liftVar_base, Nat.add_zero, List.append_assoc,
      List.cons_append, List.nil_append, hvars]
  simp only [bind, supplyType_append, hsupply', supplyType, Option.bind_some,
    VExpr.inst_liftN_bvar, hlateLen, htake, hall, ← hearlyLen, hbody] at hLate
  cases hLate
  exact ⟨domain, rfl⟩

end Lean4Lean.QuotPrefixUnfolding

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

/-- A generated quotient prefix has its declared residual telescope type. -/
theorem quotRegistered_prefixType {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hr : QuotRegistered env)
    (hw : ∀ level ∈ levels, level.WF U)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift levels) args)) :
    env.HasType U Γ (mkApps (.const ``Quot.lift levels) args) program.type := by
  have hlen := (QuotPrefixUnfolding.generate_spec hg).1
  unfold QuotPrefixUnfolding.generate at hg
  split at hg <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, _, hg⟩ := hg
  cases hg
  have hc : env.HasType U Γ (.const ``Quot.lift levels) (quotLiftConst.type.instL levels) :=
    .const hr.lift hw hlen
  have hh := hc.supply henv hΓ ht hsupply
  rw [takeForalls_sound htake] at hh
  exact hh

/-- Reabstract an actual quotient-prefix step at a supplied fresh variable.
The restored lambda domain is convertible to the given function domain. -/
theorem quotPrefixUnfold_fresh_argument {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ (mkApps (.const ``Quot.lift levels) args) (.forallE A B))
    (H : QuotPrefixUnfold env U (A :: Γ) levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) out) :
    ∃ domain, env.IsDefEqU U Γ A domain ∧
      QuotPrefixUnfold env U Γ levels args (.lam domain out) := by
  cases H with
  | intro hr hlevels hzero hg hc =>
    obtain ⟨early, hearly⟩ := QuotPrefixUnfolding.generate_anyArity (args' := args) hg (by
      have := (QuotPrefixUnfolding.generate_spec hg).2.1
      simp only [List.length_append, List.length_map, List.length_singleton] at this
      omega)
    obtain ⟨domain, rfl⟩ := QuotPrefixUnfolding.generate_open_one hearly hg
    have ht := quotRegistered_prefixType henv hΓ hr hlevels hearly ⟨_, hf⟩
    obtain ⟨⟨_, hdom⟩, _⟩ := (hf.uniqU henv hΓ ht).forallE_inv henv hΓ
    have hc' := hc.defeqDFC henv hΓ (.succ .zero hdom)
    have hf' : env.HasType U Γ (mkApps (.const ``Quot.lift levels) args)
        (.forallE domain _) := ht
    have hc'' := unfoldingCheck_prepend_fresh henv hΓ hf' (by
      simpa only [mkApps_append, mkApps_cons, mkApps_nil, lift, liftN_mkApps, liftN] using hc')
    exact ⟨domain, ⟨_, hdom⟩, .intro hr hlevels hzero hearly hc''⟩

end Lean4Lean.VEnv.Strengthening
