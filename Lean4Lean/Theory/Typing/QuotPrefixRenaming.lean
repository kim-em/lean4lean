import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Batteries.Tactic.OpenPrivate

namespace Lean4Lean.QuotPrefixProgram
open VExpr InductiveSignature InductiveSignature.NativeRecursorData
open private liftN_lift'_consN vars_lift'_consN
  from Lean4Lean.Theory.Typing.NativePrefixRenaming

private theorem getD_map_lift' (args : List VExpr) (i : Nat) (ρ : Lift) :
    (args.map (·.lift' ρ))[i]?.getD default = (args[i]?.getD default).lift' ρ := by
  simp only [List.getElem?_map]
  cases args[i]? <;> rfl

theorem generate_rename {levels : List VLevel}
    (H : generate levels args = some program) :
    generate levels (args.map (·.lift' ρ)) = some (program.rename ρ) := by
  unfold generate at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, hbody, H⟩ := H
  cases H
  have hclosed : quotLiftConst.type.Closed := by decide
  have hsupply' := supplyType_lift' (ρ := ρ) hsupply
  rw [(hclosed.instL (ls := levels)).lift'_eq Lift.Fixes.zero] at hsupply'
  have htake' := takeForalls_lift' (ρ := ρ) htake
  have hlen := takeForalls_length htake
  simp only [bind, hsupply', Option.bind_some, htake', hbody, Option.pure_def,
    Option.some.injEq, PrefixProgram.rename, PrefixProgram.mk.injEq, hlen]
  have hall : (args.map (fun e => (e.lift' ρ).liftN (6 - args.length)) ++ vars (6 - args.length) 0) =
      (args.map (·.liftN (6 - args.length)) ++ vars (6 - args.length) 0).map
        (·.lift' (ρ.consN (6 - args.length))) := by
    simp only [List.map_append, List.map_map, Function.comp_def, liftN_lift'_consN,
      vars_lift'_consN]
  simp only [List.map_map, Function.comp_def]
  rw [hall]
  simp only [getD_map_lift']
  simp only [VExpr.lift'_mkApps, List.map_cons, List.map_nil, List.map_append,
    List.map_take, VExpr.lift', (witness_closed _).lift'_eq Lift.Fixes.zero, and_self]

end Lean4Lean.QuotPrefixProgram

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData

theorem QuotDeltaRule.weak' {levels : List VLevel} (henv : env.WF)
    (W : Ctx.Lift' ρ Γ Γ') (H : QuotDeltaRule env U Γ levels args rhs) :
    QuotDeltaRule env U Γ' levels (args.map (·.lift' ρ)) (rhs.lift' ρ) := by
  cases H with
  | intro hr hw hz hg replay =>
    have hg' := QuotPrefixProgram.generate_rename (ρ := ρ) hg
    have replay' := replay.weak' henv W
    rw [VExpr.lift'_mkApps] at replay'
    rw [← PrefixProgram.rename_rhs (replay.templateScope henv).2.1]
    exact .intro hr hw hz hg' replay'

theorem QuotDeltaRule.weakN {levels : List VLevel} (henv : env.WF)
    (W : Ctx.LiftN n k Γ Γ') (H : QuotDeltaRule env U Γ levels args rhs) :
    QuotDeltaRule env U Γ' levels (args.map (·.liftN n k)) (rhs.liftN n k) := by
  simpa only [lift'_consN_skipN] using H.weak' henv (Ctx.liftN_iff_lift'.mp W)

end Lean4Lean.VEnv
