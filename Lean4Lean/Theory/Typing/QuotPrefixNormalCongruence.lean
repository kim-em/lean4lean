import Lean4Lean.Theory.Typing.NativePrefixArity
import Lean4Lean.Theory.Typing.NormalSubstitution
import Lean4Lean.Theory.Typing.NativePrefixNormalCongruence

namespace Lean4Lean.QuotPrefixProgram
open VExpr InductiveSignature InductiveSignature.NativeRecursorData
variable {levels : List VLevel}

def prefixArguments (args : List VExpr) : List VExpr :=
  args.map (·.liftN (6 - args.length)) ++ vars (6 - args.length) 0

def prefixProof (levels : List VLevel) (args : List VExpr) : VExpr :=
  let all := prefixArguments args
  mkApps (witness (levels[0]?.getD .zero))
    [all[0]?.getD default, all[1]?.getD default, all[5]?.getD default]

theorem prefixArguments_length (h : args.length ≤ 6) : (prefixArguments args).length = 6 := by
  simp [prefixArguments, vars]
  omega

theorem equationBody_head
    (H : CaseSchema.EquationBody.extract quotDefEq.lhs quotDefEq.rhs quotDefEq.type = some body) :
    ∃ n ls as, body.lhs = mkApps (.const n ls) as := by
  cases H
  exact ⟨``Quot.lift, VLevel.params 2,
    [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
      mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]], rfl⟩

theorem generate_layout (H : generate levels args = some program) :
    program.domains.length = 6 - args.length ∧
    program.constructor = mkApps (.const ``Quot.mk [levels[0]?.getD .zero])
      [(prefixArguments args)[0]?.getD default, (prefixArguments args)[1]?.getD default,
        prefixProof levels args] ∧
    program.captures = (prefixArguments args).take 5 ++ [prefixProof levels args] := by
  unfold generate at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, _, ⟨domains, result⟩, htake, body, _, H⟩ := H
  cases H
  exact ⟨takeForalls_length htake, rfl, rfl⟩

/-- The six displayed binders of Quot.lift fix prefix generation independently
of the supplied terms. This is only generation; replay retains its typing checks. -/
theorem generate_sameArity (H : generate levels args = some program)
    (hlen : args'.length = args.length) :
    ∃ program', generate levels args' = some program' := by
  obtain ⟨hlevels, hargs, _⟩ := generate_spec H
  obtain ⟨domains, body, hshape, hcount⟩ : ∃ domains body,
      quotLiftConst.type = wrapForalls domains body ∧ domains.length = 6 := by
    exact ⟨(quotLiftConst.type.takeForalls 6).getD ([], .bvar 0) |>.1,
      (quotLiftConst.type.takeForalls 6).getD ([], .bvar 0) |>.2, by decide, by decide⟩
  have hbound : args'.length ≤ (domains.map (VExpr.instL levels)).length := by
    simp only [List.length_map, hcount, hlen]
    omega
  obtain ⟨residual, remaining, result, hsupply, hresidual, hremaining⟩ :=
    supplyType_wrapForalls_exists (body := body.instL levels) hbound
  have hremaining' : remaining.length = 6 - args'.length := by
    simpa only [List.length_map, hcount] using hremaining
  have htake := NativeRecursorData.takeForalls_wrapForalls remaining result
  rw [hremaining'] at htake
  unfold generate
  rw [if_neg (by simp [hlevels, hlen, hargs])]
  rw [hshape, VExpr.instL_wrapForalls]
  simp only [bind, hsupply, Option.bind_some, hresidual, htake]
  exact ⟨_, rfl⟩

end Lean4Lean.QuotPrefixProgram

namespace Lean4Lean.VEnv
open VExpr Params InductiveSignature InductiveSignature.NativeRecursorData

/-- The fixed quotient telescope determines the type of every successful
generated prefix whose actual source occurrence is well formed. -/
theorem QuotRegistered.prefixType {env : VEnv} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotRegistered env) (hw : ∀ level ∈ levels, level.WF U)
    (hg : QuotPrefixProgram.generate levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift levels) args)) :
    env.HasType U Γ (mkApps (.const ``Quot.lift levels) args) program.type := by
  have hlen := (QuotPrefixProgram.generate_spec hg).1
  unfold QuotPrefixProgram.generate at hg
  split at hg <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, _, hg⟩ := hg
  cases hg
  have hf : env.HasType U Γ (.const ``Quot.lift levels) (quotLiftConst.type.instL levels) :=
    .const H.lift hw hlen
  have hh := hf.nativeSupply henv hΓ ht hsupply
  rw [native_takeForalls_sound htake] at hh
  exact hh

variable [Params]

/-- The concrete quotient selector and every installed-equation capture
respect normal equality of supplied arguments, in the original open telescope. -/
theorem NativePrefixReplay.quot_normal_components {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativePrefixReplay env univs Γ (mkApps (.const ``Quot.lift levels) args) program)
    (hg : QuotPrefixProgram.generate levels args = some program)
    (hg' : QuotPrefixProgram.generate levels args' = some program')
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      NormalEqF η (program.domains.reverse ++ Γ) program.constructor program'.constructor := by
  obtain ⟨hlen, hctor, hcaptures⟩ := QuotPrefixProgram.generate_layout hg
  obtain ⟨hlen', hctor', hcaptures'⟩ := QuotPrefixProgram.generate_layout hg'
  have hargs := (QuotPrefixProgram.generate_spec hg).2.1
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W : Ctx.LiftN (6 - args.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  have hall : List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ))
      (QuotPrefixProgram.prefixArguments args) (QuotPrefixProgram.prefixArguments args') := by
    unfold QuotPrefixProgram.prefixArguments
    rw [← halen]
    apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN W) ha
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact .refl (.bvar (Lookup.ofLt (by simp only [List.length_append, List.length_reverse]; omega)).2)
  have hnorm (i : Nat) (hi : i < 6) :
      NormalEqF η (program.domains.reverse ++ Γ)
        ((QuotPrefixProgram.prefixArguments args)[i]?.getD default)
        ((QuotPrefixProgram.prefixArguments args')[i]?.getD default) := by
    have hil : i < (QuotPrefixProgram.prefixArguments args).length := by
      rw [QuotPrefixProgram.prefixArguments_length (by omega)]
      exact hi
    have hir : i < (QuotPrefixProgram.prefixArguments args').length := by
      rw [← Lean4Lean.List.Forall₂.length_eq hall]
      exact hil
    simpa only [List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hir, Option.getD_some] using
      List.forall₂_getElem hall i hil hir
  have hp : NormalEqF η (program.domains.reverse ++ Γ)
      (QuotPrefixProgram.prefixProof levels args) (QuotPrefixProgram.prefixProof levels args') := by
    have hm : QuotPrefixProgram.prefixProof levels args ∈ program.captures := by
      rw [hcaptures]
      simp
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    have ht := H.captures_typed i hi (by rw [← H.captures_length]; exact hi)
    rw [he] at ht
    unfold QuotPrefixProgram.prefixProof at ht ⊢
    obtain ⟨_, hfn⟩ := VExpr.WF.of_mkApps henv.ordered hctx
      (show VExpr.WF env univs _ _ from ⟨_, ht⟩)
    exact NormalEqF.mkApps_spine hctx (.refl hfn)
      (.cons (hnorm 0 (by decide)) (.cons (hnorm 1 (by decide)) (.cons (hnorm 5 (by decide)) .nil))) ht
  constructor
  · rw [hcaptures, hcaptures']
    exact List.Forall₂.append' (List.forall₂_take hall 5) (.cons hp .nil)
  · obtain ⟨proposition, _, _, hc⟩ := H.major_prop
    rw [hctor] at hc
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hctx
      (show VExpr.WF env univs _ _ from ⟨_, hc⟩)
    rw [hctor, hctor']
    exact NormalEqF.mkApps_spine hctx (.refl hhead)
      (.cons (hnorm 0 (by decide)) (.cons (hnorm 1 (by decide)) (.cons hp .nil))) hc

/-- Normal changes to the actual supplied quotient arguments preserve the
generated delta rule and relate its two resulting lambda telescopes. -/
theorem QuotDeltaRule.congr_normal {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotDeltaRule env univs Γ levels args rhs)
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    ∃ rhs', QuotDeltaRule env univs Γ levels args' rhs' ∧ NormalEqF η Γ rhs rhs' := by
  cases H with
  | @intro program hr hw hz hg replay =>
    have halen := Lean4Lean.List.Forall₂.length_eq ha
    obtain ⟨program', hg'⟩ := QuotPrefixProgram.generate_sameArity hg halen.symm
    obtain ⟨_, _, _, hl, he, hb, _⟩ := QuotPrefixProgram.generate_spec hg
    obtain ⟨_, _, _, hl', he', hb', _⟩ := QuotPrefixProgram.generate_spec hg'
    have hlen : program.domains.length = program'.domains.length := by
      rw [(QuotPrefixProgram.generate_layout hg).1,
        (QuotPrefixProgram.generate_layout hg').1, halen]
    have heq : program.equation = program'.equation := he.trans he'.symm
    have hbody : program.equationBody = program'.equationBody := by
      rw [heq] at hb
      exact Option.some.inj (hb.symm.trans hb')
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, replay.source_typed⟩
    have hs := NormalEqF.mkApps_spine hΓ (.refl hhead) ha replay.source_typed
    have ht := hr.prefixType henv hΓ hw hg'
      ⟨_, ((hs.defeq hΓ).of_l henv hΓ replay.source_typed).hasType.2⟩
    obtain ⟨hcaptures, hctor⟩ := replay.quot_normal_components hΓ hg hg' ha
    have hnative : ∃ n ls as, program.equationBody.lhs = mkApps (.const n ls) as := by
      rw [he] at hb
      exact QuotPrefixProgram.equationBody_head hb
    obtain ⟨replay', hnormal⟩ := replay.congr_normal hΓ hlen heq hbody (hl.trans hl'.symm)
      ha hcaptures hctor ht hnative
    exact ⟨_, .intro hr hw hz hg' replay', hnormal⟩

end Lean4Lean.VEnv
