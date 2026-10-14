import Lean4Lean.Theory.Typing.Strengthening.PrefixFreshFunction

/-! # Supplying typed arguments to checked prefix programs

A prefix check remains valid after consuming a typed argument from its residual
telescope, provided the major binder remains unsupplied. This transports actual
checks, complementing the existing syntactic beta-specialization theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

private theorem etaOpen_supply_first (source arg : VExpr) (n : Nat) :
    (etaOpen (n + 1) source).inst arg n = etaOpen n (.app source arg) := by
  rw [etaOpen]
  have H := etaOpen_instN (.app source.lift (.bvar 0)) arg n 0
  simpa only [Nat.zero_add, inst, inst_lift, instVar_zero] using H

/-- Consume the first residual binder using an actual typed argument. All
checks are substituted in the opened telescope; the final major remains bound. -/
theorem unfoldingCheck_supply_first {program : PrefixUnfolding} (henv : env.WF)
    (H : UnfoldingCheck env U Γ source (program.prepend A))
    (ha : env.HasType U Γ arg A) (hn : program.domains ≠ []) :
    UnfoldingCheck env U Γ (.app source arg) (program.instN arg 0) := by
  have W := Ctx.InstN.reverse program.domains
    (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := arg) (A₀ := A))
  simp only [Nat.add_zero] at W
  have hscope := H.templateScope henv
  dsimp only [PrefixUnfolding.prepend] at hscope
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr hn
  have hmajor : (VExpr.bvar 0).inst arg program.domains.length = .bvar 0 := by
    simp only [inst, instVar, if_pos hpos]
  have hopenctx : (program.prepend A).domains.reverse ++ Γ =
      program.domains.reverse ++ A :: Γ := PrefixUnfolding.prepend_context
  refine { source_typed := ?_
           remaining_nonempty := ?_
           equation_present := H.equation_present
           equation_body := H.equation_body
           levels_wf := H.levels_wf
           levels_length := H.levels_length
           captures_length := by simpa only [PrefixUnfolding.instN, PrefixUnfolding.prepend, List.length_map] using H.captures_length
           captures_typed := ?_
           major_prop := ?_
           recursor_lhs := ?_ }
  · rw [PrefixUnfolding.type_instN]
    exact HasType.app H.source_typed ha
  · intro he
    have := congrArg List.length he
    simp only [PrefixUnfolding.instN, instDomains_length, List.length_nil] at this
    omega
  · intro j hj hd
    dsimp only [PrefixUnfolding.instN] at hj hd ⊢
    have hj' : j < program.captures.length := by
      simpa only [PrefixUnfolding.instN, List.length_map] using hj
    have ht := H.captures_typed j hj' hd
    rw [hopenctx] at ht
    have ht' := ht.instN henv.ordered W ha
    have hc : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      simpa only [PrefixUnfolding.prepend, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')] using
        (hscope.2.2 j hd).instL (ls := program.levels)
    change env.HasType U _ _ (((program.equationBody.domains[j].instL program.levels).instOuter
      (program.captures.take j)).inst arg program.domains.length) at ht'
    rw [← instantiateParams_eq_instOuter, instantiateParams_inst hc,
      instantiateParams_eq_instOuter] at ht'
    simpa only [PrefixUnfolding.instN, PrefixUnfolding.prepend, Nat.zero_add, List.getElem_map, List.map_take] using ht'
  · obtain ⟨T, hp, hm, hc⟩ := H.major_prop
    rw [hopenctx] at hp hm hc
    refine ⟨T.inst arg program.domains.length, ?_, ?_, ?_⟩
    · simpa only [PrefixUnfolding.instN, Nat.zero_add, inst] using hp.instN henv.ordered W ha
    · simpa only [PrefixUnfolding.instN, Nat.zero_add, hmajor] using hm.instN henv.ordered W ha
    · simpa only [PrefixUnfolding.instN, PrefixUnfolding.prepend, Nat.zero_add] using hc.instN henv.ordered W ha
  · have hr := H.recursor_lhs
    rw [hopenctx] at hr
    have hr' := hr.instN henv W ha
    have hn' : program.domains.length = (program.domains.length - 1) + 1 := by omega
    have he : ((etaOpen program.domains.length source).lift).inst arg program.domains.length =
        (etaOpen (program.domains.length - 1) (.app source arg)).lift := by
      conv => lhs; rw [hn']
      rw [← lift_instN_lo, etaOpen_supply_first]
    have hc : (program.equationBody.lhs.instL program.levels).ClosedN program.captures.length :=
      hscope.1.instL
    simp only [PrefixUnfolding.prepend, List.length_cons, Nat.add_sub_cancel, inst, he] at hr'
    rw [← instantiateParams_eq_instOuter, instantiateParams_inst hc,
      instantiateParams_eq_instOuter] at hr'
    simpa only [PrefixUnfolding.instN, instDomains_length, Nat.zero_add] using hr'

end Lean4Lean.VEnv.Strengthening

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv

/-- Adjacent singleton programs arise by restoring and then instantiating one
fresh residual domain. The intermediate program still retains the major binder. -/
theorem singletonUnfolding_supply_first_record {env : VEnv} {data : RecursorData}
    {levels : List VLevel} {args : List VExpr} {early late : PrefixUnfolding}
    (henv : env.WF) (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hEarly : data.singletonUnfolding env U levels args = some early)
    (hLate : data.singletonUnfolding env U levels (args ++ [arg]) = some late) :
    ∃ (domain : VExpr) (fresh : PrefixUnfolding), early = fresh.prepend domain ∧ late = fresh.instN arg 0 ∧ fresh.domains ≠ [] := by
  obtain ⟨fresh, hfresh⟩ := singletonUnfolding_anyArity
    (args' := args.map VExpr.lift ++ [VExpr.bvar 0]) hLate (by
      simpa only [List.length_append, List.length_map, List.length_singleton] using
        (singletonUnfolding_spec hLate).1)
  obtain ⟨domain, he⟩ := singletonUnfolding_open_one henv hr hEarly hfresh
  have hex : ∃ type, data.recursorType = some type := by
    cases hh : data.recursorType with
    | some type => exact ⟨type, rfl⟩
    | none =>
      unfold singletonUnfolding at hEarly
      split at hEarly <;> simp [hh] at hEarly
  obtain ⟨type, htype⟩ := hex
  have hsub := singletonUnfolding_inst (arg := arg) (k := 0) henv hr hlarge hzero
    htype (hr.recursorType_closed henv htype) hfresh
  simp only [List.map_append, List.map_map, Function.comp_def, inst_lift,
    List.map_cons, List.map_nil, List.map_id_fun', inst, instVar_zero] at hsub
  exact ⟨domain, fresh, he, singletonUnfolding_unique hLate hsub,
    (singletonUnfolding_spec hfresh).2.1⟩

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.QuotPrefixUnfolding
open VExpr InductiveSignature.RecursorData

/-- The complete-record supply identity for quotient prefixes. -/
theorem generate_supply_first_record {levels : List VLevel} {args : List VExpr}
    {early late : PrefixUnfolding}
    (hEarly : generate levels args = some early)
    (hLate : generate levels (args ++ [arg]) = some late) :
    ∃ (domain : VExpr) (fresh : PrefixUnfolding), early = fresh.prepend domain ∧ late = fresh.instN arg 0 ∧ fresh.domains ≠ [] := by
  obtain ⟨fresh, hfresh⟩ := generate_anyArity
    (args' := args.map VExpr.lift ++ [VExpr.bvar 0]) hLate (by
      simpa only [List.length_append, List.length_map, List.length_singleton] using
        (generate_spec hLate).2.1)
  obtain ⟨domain, he⟩ := generate_open_one hEarly hfresh
  have hsub := generate_inst (arg := arg) (k := 0) hfresh
  simp only [List.map_append, List.map_map, Function.comp_def, inst_lift,
    List.map_cons, List.map_nil, List.map_id_fun', inst, instVar_zero] at hsub
  exact ⟨domain, fresh, he, generate_unique hLate hsub, (generate_spec hfresh).2.2.1⟩

end Lean4Lean.QuotPrefixUnfolding

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

/-- The well-formed extended application supplies the next argument's typing
at the actual residual domain, by uniqueness of the prefix's Pi type. -/
theorem unfoldingCheck_supply_first_of_wf {program : PrefixUnfolding}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : UnfoldingCheck env U Γ source (program.prepend A))
    (ht : VExpr.WF env U Γ (.app source arg)) (hn : program.domains ≠ []) :
    UnfoldingCheck env U Γ (.app source arg) (program.instN arg 0) := by
  obtain ⟨T, ht⟩ := ht
  obtain ⟨_, _, hf, ha⟩ := HasType.app_inv henv hΓ ht
  obtain ⟨⟨_, hdom⟩, _⟩ := (H.source_typed.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact unfoldingCheck_supply_first henv H (ha.defeqU_r henv hΓ ⟨_, hdom.symm⟩) hn

/-- Supplying one more typed argument preserves the actual singleton prefix
rule as long as its major is still unsupplied. The two outputs meet by beta. -/
theorem prefixUnfold_supply_one {name : Name} {levels : List VLevel} {data : RecursorData}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hreg : registry name = some data)
    (hbound : args.length + 1 ≤ data.majorOffset)
    (H : PrefixUnfold env U registry Γ name levels args out)
    (ht : VExpr.WF env U Γ (mkApps (.const name levels) (args ++ [arg]))) :
    ∃ out', PrefixUnfold env U registry Γ name levels (args ++ [arg]) out' ∧
      BetaRed (.app out arg) out' := by
  cases H with
  | intro hreg' hr hname hlarge hlevels hzero hg hc =>
    cases Option.some.inj (hreg.symm.trans hreg')
    obtain ⟨late, hlate⟩ := singletonUnfolding_anyArity (args' := args ++ [arg]) hg
      (by simpa only [List.length_append, List.length_singleton] using hbound)
    obtain ⟨domain, fresh, rfl, rfl, hn⟩ :=
      singletonUnfolding_supply_first_record henv hr hlarge hzero hg hlate
    have ht' : VExpr.WF env U Γ (.app (mkApps (.const name levels) args) arg) := by
      simpa only [mkApps_snoc] using ht
    have hc' := unfoldingCheck_supply_first_of_wf henv hΓ hc ht' hn
    refine ⟨_, .intro hreg hr hname hlarge hlevels hzero hlate ?_, ?_⟩
    · simpa only [mkApps_snoc] using hc'
    · have hs : fresh.equationBody.rhs.ClosedN fresh.captures.length :=
        (hc.templateScope henv).2.1
      rw [PrefixUnfolding.prepend_rhs, PrefixUnfolding.rhs_instN _ hs]
      exact .beta

/-- One more admissible quotient argument preserves the checked primitive rule
and beta-specializes its generated output. -/
theorem quotPrefixUnfold_supply_one {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hbound : args.length + 1 ≤ 5)
    (H : QuotPrefixUnfold env U Γ levels args out)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift levels) (args ++ [arg]))) :
    ∃ out', QuotPrefixUnfold env U Γ levels (args ++ [arg]) out' ∧
      BetaRed (.app out arg) out' := by
  cases H with
  | intro hr hlevels hzero hg hc =>
    obtain ⟨late, hlate⟩ := QuotPrefixUnfolding.generate_anyArity (args' := args ++ [arg]) hg
      (by simpa only [List.length_append, List.length_singleton] using hbound)
    obtain ⟨domain, fresh, rfl, rfl, hn⟩ := QuotPrefixUnfolding.generate_supply_first_record hg hlate
    have ht' : VExpr.WF env U Γ (.app (mkApps (.const ``Quot.lift levels) args) arg) := by
      simpa only [mkApps_snoc] using ht
    have hc' := unfoldingCheck_supply_first_of_wf henv hΓ hc ht' hn
    refine ⟨_, .intro hr hlevels hzero hlate ?_, ?_⟩
    · simpa only [mkApps_snoc] using hc'
    · have hs : fresh.equationBody.rhs.ClosedN fresh.captures.length :=
        (hc.templateScope henv).2.1
      rw [PrefixUnfolding.prepend_rhs, PrefixUnfolding.rhs_instN _ hs]
      exact .beta

end Lean4Lean.VEnv.Strengthening
