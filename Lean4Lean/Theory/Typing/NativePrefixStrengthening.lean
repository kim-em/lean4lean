import Lean4Lean.Theory.Typing.NativePrefixRenaming
import Lean4Lean.Theory.Typing.NativeDeltaReduction
import Batteries.Tactic.OpenPrivate

/-! Strengthening the concrete replay of a renamed native prefix. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema InductiveSignature.NativeRecursorData
open private closed_wrapLams_body closed_wrapForalls_domain spine_lift' case_rebuild_spine case_lift'_mkApps
  from Lean4Lean.Theory.Typing.CaseReduction

private theorem native_const_spine_lift'_inv {name : Name} {levels : List VLevel}
    (h : VExpr.mkApps (.const name levels) args = e.lift' ρ) :
    ∃ originalArgs, e = VExpr.mkApps (.const name levels) originalArgs ∧
      args = originalArgs.map (fun e => e.lift' ρ) := by
  have hs := congrArg VExpr.getAppFnArgs h
  rw [spine_mkApps_exact _ _ rfl, spine_lift'] at hs
  have hh := congrArg Prod.fst hs
  cases hf : e.getAppFnArgs.1 <;> simp only [hf, VExpr.lift'] at hh <;> try contradiction
  cases hh
  refine ⟨e.getAppFnArgs.2, ?_, congrArg Prod.snd hs⟩
  simpa only [hf] using (case_rebuild_spine e).symm

theorem NativeSpineMatch.weak'_inv (henv : env.WF)
    (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' ρ Γ Γ')
    (H : NativeSpineMatch env U Γ' (actual.lift' ρ) (expected.lift' ρ)) :
    NativeSpineMatch env U Γ actual expected := by
  obtain ⟨name, levels, levels', args, args', hactual, hexpected, hwf, hwf', heq, hargs⟩ := H
  obtain ⟨smallArgs, rfl, rfl⟩ := native_const_spine_lift'_inv hactual.symm
  obtain ⟨smallArgs', rfl, rfl⟩ := native_const_spine_lift'_inv hexpected.symm
  refine ⟨name, levels, levels', smallArgs, smallArgs', rfl, rfl, hwf, hwf', heq, ?_⟩
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => (IsDefEqU.weak'_iff henv hΓ W).1 h)
    (List.forall₂_map_left_iff.mp (List.forall₂_map_right_iff.mp hargs))


open private liftN_lift'_consN consN_cons
  from Lean4Lean.Theory.Typing.NativePrefixRenaming

private theorem renameDomains_getLast (domains : List VExpr)
    (h : domains.getLast? = some domain) :
    (renameDomains ρ domains).getLast? =
      some (domain.lift' (ρ.consN (domains.length - 1))) := by
  induction domains generalizing ρ with
  | nil => simp at h
  | cons d ds ih =>
    cases ds with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst d
      rfl
    | cons a ds =>
      have hh : (a :: ds).getLast? = some domain := by simpa using h
      simpa only [renameDomains, List.getLast?_cons_cons, List.length_cons,
        Nat.add_sub_cancel, consN_cons] using ih (ρ := ρ.cons) hh


theorem NativePrefixReplay.weak'_inv (henv : env.WF)
    (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' ρ Γ Γ')
    (H : NativePrefixReplay env U Γ' (source.lift' ρ) (program.rename ρ)) :
    NativePrefixReplay env U Γ source program := by
  have hctx := (HasType.wrapLams_inv henv hΓ
    (H.source_typed.native_eta henv hΓ).hasType.2).1
  have W' := renameDomains_context program.domains W
  have hscope := H.templateScope henv
  have hdomains : ∀ j (hj : j < program.equationBody.domains.length),
      program.equationBody.domains[j].ClosedN j := hscope.2.2
  have hclosed : program.equationBody.lhs.ClosedN program.captures.length := by
    simpa only [PrefixProgram.rename, List.length_map] using hscope.1
  have hlen : program.captures.length = program.equationBody.domains.length := by
    simpa only [PrefixProgram.rename, List.length_map] using H.captures_length
  have hnonempty : program.domains ≠ [] := by
    intro h
    apply H.remaining_nonempty
    simp [PrefixProgram.rename, h, renameDomains]
  refine {
    source_typed := (HasType.weak'_iff henv hΓ W).1 (by
      simpa only [PrefixProgram.rename_type] using H.source_typed)
    remaining_nonempty := hnonempty
    equation_present := H.equation_present
    equation_body := H.equation_body
    levels_wf := H.levels_wf
    levels_length := H.levels_length
    captures_length := hlen
    captures_typed := ?_
    major_prop := ?_
    native_lhs := ?_ }
  · intro j hj hd
    have hs : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using (hdomains j hd).instL
    apply (HasType.weak'_iff henv hctx W').1
    rw [← instantiateParams_eq_instOuter, VEnv.instantiateParams_lift' hs]
    have ht := H.captures_typed j (by simpa [PrefixProgram.rename] using hj) hd
    simpa only [PrefixProgram.rename, List.getElem_map, List.map_take,
      instantiateParams_eq_instOuter] using ht
  · obtain ⟨d, hd⟩ : ∃ d, program.domains.getLast? = some d := by
      cases h : program.domains.getLast? with
      | none => exact (hnonempty (List.getLast?_eq_none_iff.mp h)).elim
      | some d => exact ⟨d, rfl⟩
    have hlast := renameDomains_getLast program.domains hd (ρ := ρ)
    obtain ⟨hp, hm, hc⟩ := H.major_prop_at_last henv hΓ hlast
    have hpos : 0 < program.domains.length := List.length_pos_iff.mpr hnonempty
    have hcomm : (d.lift' (ρ.consN (program.domains.length - 1))).lift =
        d.lift.lift' (ρ.consN program.domains.length) := by
      have he := liftN_lift'_consN d 1 (ρ.consN (program.domains.length - 1))
      simpa only [Lift.consN_consN, Nat.sub_add_cancel (by omega : 1 ≤ program.domains.length)] using he
    rw [hcomm] at hp hm hc
    refine ⟨d.lift, (HasType.weak'_iff henv hctx W').1 hp, ?_,
      (HasType.weak'_iff henv hctx W').1 hc⟩
    apply (HasType.weak'_iff henv hctx W').1
    have hb : (VExpr.bvar 0).lift' (ρ.consN program.domains.length) = .bvar 0 := by
      have he : program.domains.length = (program.domains.length - 1) + 1 := by omega
      rw [he]
      rfl
    simpa only [hb] using hm
  · apply NativeSpineMatch.weak'_inv henv hctx W'
    have hleft : (VExpr.app (nativeEtaBody (program.domains.length - 1) source).lift
        program.constructor).lift' (ρ.consN program.domains.length) =
        VExpr.app (nativeEtaBody ((program.rename ρ).domains.length - 1) (source.lift' ρ)).lift
          (program.rename ρ).constructor := by
      simp only [PrefixProgram.rename, renameDomains_length, VExpr.lift', nativeEtaBody_lift']
      congr 1
      have he := liftN_lift'_consN (nativeEtaBody (program.domains.length - 1) source) 1
        (ρ.consN (program.domains.length - 1))
      have hpos : 1 ≤ program.domains.length := List.length_pos_iff.mpr hnonempty
      simpa only [Lift.consN_consN, Nat.sub_add_cancel hpos] using he.symm
    rw [hleft, ← instantiateParams_eq_instOuter,
      VEnv.instantiateParams_lift' hclosed.instL]
    simpa only [PrefixProgram.rename, instantiateParams_eq_instOuter] using H.native_lhs

/-- A native prefix reduction whose supplied arguments are renamed comes
from a reduction in the original context, including its exact output. -/
theorem NativeDeltaRule.weak'_inv {name : Name} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' ρ Γ Γ')
    (H : NativeDeltaRule env U registry Γ' name levels
      (arguments.map (·.lift' ρ)) rhs) :
    ∃ smallRhs, NativeDeltaRule env U registry Γ name levels arguments smallRhs ∧
      rhs = smallRhs.lift' ρ := by
  cases H with
  | @intro data program hl hr hn ht hw hz hg replay =>
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold prefixProgram at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    rw [prefixProgram_rename htype (hr.recursorType_closed henv htype)] at hg
    obtain ⟨small, hsmall, he⟩ := Option.map_eq_some_iff.mp hg
    cases he
    have hreplay : NativePrefixReplay env U Γ
        (mkApps (.const name levels) arguments) small := by
      apply NativePrefixReplay.weak'_inv henv hΓ W
      simpa only [case_lift'_mkApps, VExpr.lift'] using replay
    exact ⟨small.rhs, .intro hl hr hn ht hw hz hsmall hreplay,
      PrefixProgram.rename_rhs (hreplay.templateScope henv).2.1⟩

theorem NativeDeltaRule.weakN_inv {name : Name} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (H : NativeDeltaRule env U registry Γ' name levels
      (arguments.map (·.liftN n k)) rhs) :
    ∃ smallRhs, NativeDeltaRule env U registry Γ name levels arguments smallRhs ∧
      rhs = smallRhs.liftN n k := by
  simpa only [lift'_consN_skipN] using
    NativeDeltaRule.weak'_inv henv hΓ (Ctx.liftN_iff_lift'.mp W) (by simpa only [lift'_consN_skipN] using H)

end Lean4Lean.VEnv
