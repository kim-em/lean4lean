import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedTelescopeCongruence

/-! # Stored declarations in typed computation chains

Stored bare constants unfold at stage zero. The stored quotient equation is
handled under its actual lambda telescope: ordinary iota at nonzero sources,
and the repaired quotient prefix followed by proof irrelevance at zero sources.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private PatternReductionTrace.of_quotient from Lean4Lean.Theory.Typing.Confluence.QuotCoverage
variable [Params]

/-- A proposition-source quotient application computes its repaired prefix,
then identifies the extracted inhabitant with the constructor payload by proof
irrelevance. No native certificate or computational joining premise is needed. -/
theorem TypedComputationEq.quot_zero_application
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : QuotRegistered env)
    (hu : u.WF univs) (hv : v.WF univs) (hz : u ≈ .zero)
    (ht : env.HasType univs Γ (mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u]) [alpha, relation, value]]) T)
    (ha : env.HasType univs Γ alpha (.sort u))
    (hrel : env.HasType univs Γ relation (.forallE alpha (.forallE alpha.lift (.sort .zero))))
    (hf : env.HasType univs Γ fn (.forallE alpha beta.lift))
    (hval : env.HasType univs Γ value alpha) :
    TypedComputationEq EnvironmentCore.definitions Γ
      (mkApps (.const ``Quot.lift [u,v])
        [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u]) [alpha, relation, value]])
      (.app fn value) T := by
  let major := mkApps (.const ``Quot.mk [u]) [alpha, relation, value]
  obtain ⟨_, _, hprefix, hmajor⟩ := ht.app_inv henv hΓ
  have hd := QuotPrefixUnfold.atFive henv hΓ hr hu hv hz ⟨_, hprefix⟩
  have R := (TypedComputationEq.quot_prefix (levels := [u,v]) (args := [alpha, relation, beta, fn, compat]) hcon hΓ hprefix hd).app_fn hΓ hmajor
  have R := R.at_source_type hΓ ht
  have hb : (VExpr.app fn.lift (mkApps (QuotPrefixUnfolding.propInhabitant u)
      [alpha.lift, relation.lift, .bvar 0])).inst major =
      VExpr.app fn (mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha, relation, major]) := by
    simp only [VExpr.inst, inst_mkApps, inst_lift]
    rw [(QuotPrefixUnfolding.propInhabitant_closed u).instN_eq (Nat.zero_le _)]
    simp [VExpr.inst, inst_lift]
  have RB := TypedComputationEq.of_beta (D := EnvironmentCore.definitions) hΓ R.defeq.hasType.2
    (show VExpr.BetaRed _ (.app fn (mkApps (QuotPrefixUnfolding.propInhabitant u)
      [alpha, relation, major])) from hb ▸ VExpr.BetaRed.beta)
  have hmajor' : env.HasType univs Γ major (mkApps (.const ``Quot [u]) [alpha, relation]) := by
    have h1 := (HasType.const hr.constructor (ls := [u]) (by simpa using hu) rfl).app ha
    have h2 := h1.app (by simpa [instL, VExpr.inst, VLevel.inst] using hrel)
    have h3 := h2.app (by simpa [instL, VExpr.inst, VLevel.inst, inst_lift, ← lift_instN_lo] using hval)
    simpa [major, mkApps, instL, VExpr.inst, VLevel.inst, inst_lift, ← lift_instN_lo] using h3
  have hp := hr.propInhabitant_app hu hz ha hrel hmajor'
  have hP := IsDefEq.defeq (IsDefEq.sortDF hu (by trivial) hz) ha
  have RI := (TypedComputationEq.proof_irrel (D := EnvironmentCore.definitions) hP hp hval).app_arg hΓ hf
  exact (R.trans RB).trans (RI.at_source_type hΓ RB.defeq.hasType.2)

/-- The entire stored quotient equation has a typed computation chain at
every well-formed universe specialization, including proposition sources. -/
theorem TypedComputationEq.quot_equation
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : QuotRegistered env)
    (hpattern : Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = quotDefEq.uvars) :
    TypedComputationEq EnvironmentCore.definitions Γ
      (quotDefEq.lhs.instL levels) (quotDefEq.rhs.instL levels) (quotDefEq.type.instL levels) := by
  change levels.length = 2 at hl
  obtain ⟨u, v, rfl⟩ : ∃ u v, levels = [u,v] := by
    rcases levels with _ | ⟨u, _ | ⟨v, tail⟩⟩ <;> simp_all
  have hex := IsDefEq.extra (Γ := Γ) hr.equation hw hl
  by_cases hz : u ≈ .zero
  · let ds := (((quotDefEq.type.takeForalls 6).getD ([], .bvar 0)).1).map (instL [u,v])
    have htyped : env.HasType univs Γ (VExpr.wrapLams ds (quotDefEq.lhs.stripLams.instL [u,v]))
        (wrapForalls ds (.bvar 3)) := hex.hasType.1
    obtain ⟨hctx, hbody⟩ := HasType.wrapLams_inv henv hΓ htyped
    have ha : env.HasType univs (ds.reverse ++ Γ) (.bvar 5) (.sort u) := by type_tac
    have hrel : env.HasType univs (ds.reverse ++ Γ) (.bvar 4)
        (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by type_tac
    have hf : env.HasType univs (ds.reverse ++ Γ) (.bvar 2)
        (.forallE (.bvar 5) (.bvar 4)) := by type_tac
    have hval : env.HasType univs (ds.reverse ++ Γ) (.bvar 0) (.bvar 5) := by type_tac
    exact (TypedComputationEq.quot_zero_application hcon hctx hr
      (hw u (by simp)) (hw v (by simp)) hz hbody ha hrel hf hval).wrapLams hΓ hctx
  · have H := PatternReductionTrace.of_quotient hpattern (QuotPattern.equation_trace (v := v) (Γ := Γ) (U := univs) hr hz)
    exact TypedComputationEq.of_pattern_trace EnvironmentCore.sound hcon hΓ hex.hasType.1 H

/-- Every stored equation of a well-formed environment is covered. The
pattern presentation must include the registered quotient rule when present;
the concrete environment presentation satisfies this requirement directly. -/
theorem TypedComputationEq.extra
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hΓ : OnCtx Γ (env.IsType univs)) (hd : env.defeqs df)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = df.uvars) :
    TypedComputationEq EnvironmentCore.definitions Γ
      (df.lhs.instL levels) (df.rhs.instL levels) (df.type.instL levels) := by
  have hex := IsDefEq.extra (Γ := Γ) hd hw hl
  obtain ⟨ds, H⟩ := henv
  rcases H.defeqs_origin hd with rfl | ⟨value, _, rfl⟩
  · have hr := H.quotRegistered hd
    exact TypedComputationEq.quot_equation hcon hΓ hr (hqpat hr) hw hl
  · change levels.length = value.uvars at hl
    have he : value.toDefEq.lhs.instL levels = .const value.name levels := by
      simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl]
    have hunfold : EnvironmentCore.definitions.unfolds value.name levels (value.toDefEq.rhs.instL levels) :=
      .inl (FullHead.quot_base henv _ _ _ ⟨value.toDefEq, levels, hd, hw, hl, he, rfl⟩)
    rw [he] at hex ⊢
    exact TypedComputationEq.delta EnvironmentCore.sound hunfold hΓ hex.hasType.1

end Lean4Lean.VEnv.Strengthening
