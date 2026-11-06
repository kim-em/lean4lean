import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqFamilyReadout
import Lean4Lean.Theory.Typing.Strengthening.PrefixFreshAbstraction

/-! # Open guarded prefixes with fresh arguments before specializing

Fresh opening leaves a generated family guard in exactly the same context.
Only the endpoint equality obtained after removing the proof major is
specialized by an arbitrary typed substitution; guard substitution closure is
not required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature RecursorData
variable [Params]

omit [Params] in
/-- Moving the next fresh argument into the supplied prefix leaves the fully
opened argument vector unchanged. -/
theorem openedArguments_fresh {data : RecursorData} {args : List VExpr} (hbound : args.length < data.majorOffset) :
    data.openedArguments (args.map VExpr.lift ++ [VExpr.bvar 0]) = data.openedArguments args := by
  let n := data.majorOffset - args.length
  have he : data.majorOffset + 1 - args.length = n + 1 := by dsimp [n]; omega
  have hl : data.majorOffset + 1 - (args.map VExpr.lift ++ [VExpr.bvar 0]).length = n := by
    simp only [List.length_append, List.length_map, List.length_singleton]; dsimp [n]; omega
  have hvars : vars (n + 1) 0 = VExpr.bvar n :: vars n 0 := by
    simp [vars, List.range_succ, List.reverse_append]
  simp only [openedArguments, he, hl, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, VExpr.lift, VExpr.liftN_liftN, Nat.add_comm 1 n,
    VExpr.liftN, liftVar_base, Nat.add_zero, List.append_assoc, List.cons_append,
    List.nil_append, hvars]

omit [Params] in
/-- Opening a generated prefix at its next fresh variable changes neither
the guard endpoints nor their fully opened context. No property of Cmp is used. -/
theorem GuardedSingleton.FamilyGuard.open_fresh
    {data : RecursorData} {args : List VExpr} {levels : List VLevel}
    (hbound : args.length < data.majorOffset)
    (HG : GuardedSingleton.FamilyGuard Cmp Γ data levels args (late.prepend A) S E) :
    GuardedSingleton.FamilyGuard Cmp (A :: Γ) data levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) late S E := by
  simpa only [GuardedSingleton.FamilyGuard, openedArguments_fresh hbound,
    PrefixUnfolding.prepend_context] using HG

private theorem recovered_eq_family_reflect
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : w.WF univs)
    (hα : env.HasType univs Γ α (.sort w))
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (HG : CarrierRecoveredCompare Step (proofEraseCtx (eqApp w α a b :: Γ)) true
      (proofErase (eqApp w α a b :: Γ) (eqApp w α.lift a.lift a.lift))
      (proofErase (eqApp w α a b :: Γ) (eqApp w α.lift a.lift b.lift))) :
    env.IsDefEq univs Γ a b α := by
  have hP := HasType.eqApp heq hw hα ha ha
  have hQ := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have HG' : CarrierRecoveredCompare Step (proofEraseCtx (eqApp w α a b :: Γ)) true
      ((proofErase Γ (eqApp w α a a)).liftN 1)
      ((proofErase Γ (eqApp w α a b)).liftN 1) := by
    rw [← proofErase_liftN hΓ hΓE Ctx.LiftN.one hP,
      ← proofErase_liftN hΓ hΓE Ctx.LiftN.one hQ]
    exact HG
  have HF := (proofErase_carrier_recovered_compare_descend hstep hΓ hΓE
    Ctx.LiftN.one rfl hP hQ HG').1 ⟨_, HasType.sort (by trivial)⟩
  change env.IsDefEqU univs Γ (VExpr.mkApps (.const ``Eq [w]) [α,a,a])
    (VExpr.mkApps (.const ``Eq [w]) [α,a,b]) at HF
  obtain ⟨_, HA⟩ := HF.rigidApp_inv henv hΓ (heq.rigid henv) hP
  cases HA with | cons _ HA =>
    cases HA with | cons _ HA =>
      cases HA with | cons hab _ => exact hab.of_l henv hΓ ha

/-- Any generated Eq singleton guard forces index equality in every typed
completion to five arguments. Fresh opening keeps the entire guard unchanged;
only the reflected semantic equation is substituted. This covers all shorter
prefixes without assuming substitution closure of recovered comparisons. -/
theorem recovered_eq_prefix_completion
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E)
    (hw : ∀ l ∈ [v,w], l.WF univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M m b) T)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : data.singletonUnfolding env univs [v,w] args = some program)
    (hf : VExpr.WF env univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) args))
    (HG : GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Ξ => CarrierRecoveredCompare Step Ξ true)) Γ data [v,w] args program S E)
    (WS : Ctx.SubstEq env univs Δ σ σ Γ)
    (Eargs : args.map (·.subst σ) ++ pending = [α,a,M,m,b]) :
    env.IsDefEq univs Δ a b α := by
  induction pending generalizing Γ σ args program with
  | nil =>
    have hlen : args.length = 5 := by
      have := congrArg List.length Eargs
      simpa only [List.length_append, List.length_map, List.length_nil, Nat.add_zero,
        List.length_cons] using this
    cases args with | nil => simp at hlen | cons αs args =>
    cases args with | nil => simp at hlen | cons as args =>
    cases args with | nil => simp at hlen | cons Ms args =>
    cases args with | nil => simp at hlen | cons ms args =>
    cases args with | nil => simp at hlen | cons bs args =>
    have he : args = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons] at hlen; omega)
    subst args
    have hgen := eqRec_prefix_generated (U := univs) (α := αs) (a := as) (M := Ms) (m := ms) (b := bs) heq hr hn hz hS hE
    cases Option.some.inj (hg.symm.trans hgen)
    have HF := (eqRec_family_guard_iff heq hr hn hz hS hE).1 HG
    obtain ⟨_, hws, hαs, has, _, _, hbs⟩ := eqRecBeforeMajor_typings henv heq hΓ hf
    have HE := (recovered_eq_family_reflect heq hstep hΓ hws hαs has hbs HF).subst henv WS hΔ
    simp only [List.map_cons, List.map_nil, List.append_nil, List.cons.injEq] at Eargs
    rcases Eargs with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
    exact HE
  | cons x xs ih =>
    have hoff := (hr.eqRec_target heq hn).2.1
    have hbound : args.length < data.majorOffset := by
      have := congrArg List.length Eargs
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
      omega
    obtain ⟨late, hlate⟩ := singletonUnfolding_anyArity (args' := args.map VExpr.lift ++ [.bvar 0]) hg (by
      simp only [List.length_append, List.length_map, List.length_singleton]; omega)
    obtain ⟨A, rfl⟩ := singletonUnfolding_open_one henv hr hg hlate
    have hfA := hr.prefixType henv hΓ hw hg (hn.symm ▸ hf)
    rw [hn] at hfA
    change env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) args) (.forallE A late.type) at hfA
    obtain ⟨⟨u, hA⟩, _⟩ := (hfA.isType henv hΓ).choose_spec.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hfw : env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v,w]) args).lift
        (.forallE A.lift (late.type.liftN 1 1)) := hfA.weak henv
    have hfresh : env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v,w]) (args.map VExpr.lift ++ [.bvar 0])) late.type := by
      simpa only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
        VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN, VExpr.inst_liftN_bvar] using
        hfw.app (HasType.bvar (Lookup.zero (ty := A)))
    have hfsub := hfA.subst henv WS hΔ
    have hall : VExpr.WF env univs Δ
        (VExpr.mkApps (.app (VExpr.mkApps (.const ``Eq.rec [v,w]) (args.map (·.subst σ))) x) xs) := by
      rw [← VExpr.mkApps_cons, ← VExpr.mkApps_append, Eargs]
      exact ⟨_, ht⟩
    have happ := VExpr.WF.of_mkApps henv.orderedStrong hΔ hall
    obtain ⟨D, B, hfd, hx⟩ := happ.app_inv henv hΔ
    have hfsub' : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) (args.map (·.subst σ)))
        (.forallE (A.subst σ) (late.type.subst σ.lift)) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst] using hfsub
    obtain ⟨⟨_, HD⟩, _⟩ := (hfsub'.uniqU henv hΔ hfd).forallE_inv henv hΔ
    have hxA := hx.defeqU_r henv hΔ HD.toU.symm
    have WS' : Ctx.SubstEq env univs Δ (σ.cons x) (σ.cons x) (A :: Γ) :=
      .cons WS hA hxA
    apply ih hΓA hlate ⟨_, hfresh⟩ (HG.open_fresh hbound) WS'
    have Ezero : σ.cons x 0 = x := rfl
    simpa only [List.map_append, List.map_map, Function.comp_def, VExpr.lift_subst_cons,
      List.map_cons, List.map_nil, VExpr.subst, Ezero, List.append_assoc,
      List.cons_append, List.nil_append] using Eargs

open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment

/-- A raw recovered singleton at any prefix of a typed five-argument Eq term
forces the endpoint equation of that completion. The original prefix's guard
is opened and reflected, rather than substituted as a raw certificate. -/
theorem proofErase_recovered_singleton_eq_prefix_reflect
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (Eargs : pre ++ pending = [α,a,M,m,b])
    (H : SingletonPrimitiveWith (fun Ξ => CarrierRecoveredCompare Step Ξ true) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) (pre.map (proofErase Γ))) out) :
    env.IsDefEq univs Γ a b α := by
  have hall : VExpr.WF env univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) pending) := by
    rw [← VExpr.mkApps_append, Eargs]; exact ⟨_, ht⟩
  have hf := VExpr.WF.of_mkApps henv.orderedStrong hΓ hall
  generalize ES : ProofShape.mkApps (.const ``Eq.rec [v,w]) (pre.map (proofErase Γ)) = source at H
  cases H with
  | @intro C raw domains result V ha hcalc HG =>
    obtain ⟨hn, hl, hp⟩ := ProofShape.const_spine_inj ES
    rw [← hp] at hcalc HG
    have hlen : pre.length = C.arity := by simpa only [← hp, List.length_map] using ha
    have hf' := hf
    rw [hn, hl] at hf'
    obtain ⟨program, hg, _, HF⟩ := V.realizeWith heq hΓ hlen hf' hcalc HG
    rw [← hl] at hg HF
    exact recovered_eq_prefix_completion (pending := pending) heq hstep V.registered hn.symm
      (hl.symm ▸ V.zero) (hl.symm ▸ V.layout_eq) (hl.symm ▸ V.elim_eq)
      (hl.symm ▸ V.levels_wf) hΓ ht hΓ hg hf HF (Ctx.SubstEq.id henv.ordered hΓ)
      (by simpa only [VExpr.subst_id, List.map_id_fun', id] using Eargs)

end Lean4Lean.VEnv.Strengthening
