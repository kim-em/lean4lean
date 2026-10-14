import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqPrefixGeneration
import Lean4Lean.Theory.Typing.Strengthening.PrefixComputation

/-! # Actual registered replay of the canonical K prefix

Endpoint conversion checks the explicit generated program, so the manual
K-prefix lambda is the output of the actual singleton prefix rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature

/-- Endpoint conversion checks the actual canonical program, with its stored
rule, four captures, equality-proof major, and literal recursor spine. -/
theorem canonicalEqPrefixProgram_check (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hpat : env.PatEquation canonicalEqRecRule)
    (ht : VExpr.WF env U Γ (eqRecBeforeMajor v w α a M m b))
    (hab : env.IsDefEqU U Γ a b) :
    UnfoldingCheck env U Γ (eqRecBeforeMajor v w α a M m b)
      (canonicalEqPrefixProgram v w α a M m b (eqReflApp w α.lift a.lift)) := by
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ht
  have hf := eqRecBeforeMajor_typed heq hv hw hα ha hM hm hb
  have hE := HasType.eqApp heq hw hα ha hb
  have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType U) := ⟨hΓ, _, hE⟩
  have hr := (HasType.eqReflApp heq hw hα ha).weak (B := eqApp w α a b) henv.ordered
  have hconv := (IsDefEq.eqApp_r heq hw hα ha (hab.of_l henv hΓ ha)).weak
    (B := eqApp w α a b) henv.ordered
  have hctor : env.HasType U (eqApp w α a b :: Γ)
      (eqReflApp w α.lift a.lift) (eqApp w α a b).lift := by
    simpa only [eqReflApp, lift, liftN] using hconv.defeq hr
  have hlevels : ∀ l ∈ [v, w], l.WF U := by simp_all
  refine ⟨hf, by simp [canonicalEqPrefixProgram], hpat, canonicalEqRecBody_extract,
    hlevels, rfl, rfl, ?_, ?_, ?_⟩
  · intro j hj hd
    change j < 4 at hj
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    all_goals
      simp only [canonicalEqPrefixProgram, canonicalEqRecBody, List.getElem_cons_zero,
        List.getElem_cons_succ, List.reverse_cons, List.reverse_nil, List.take_zero, List.take_succ_cons]
    · simpa [HasType, instL, VLevel.inst, instOuter_nil, lift, liftN] using hα.weak (B := eqApp w α a b) henv.ordered
    · simpa [HasType, instL, instOuter_cons, instOuter_nil, inst, instVar] using ha.weak (B := eqApp w α a b) henv.ordered
    · have HM := hM.weak (B := eqApp w α a b) henv.ordered
      simp [HasType, canonicalEqRecMotive, instL, VLevel.inst, instOuter_cons, instOuter_nil,
        inst, instVar, eqApp, lift, liftN, inst_liftN_lo, inst_liftN'] at HM ⊢
      simpa only [liftN'_liftN_lo, liftN_liftN] using HM
    · simpa [HasType, canonicalEqRecMinor, instL, VLevel.inst, instOuter_cons, instOuter_nil,
        inst, instVar, eqReflApp, lift, liftN, inst_liftN_lo, inst_liftN', inst_lift] using
        hm.weak (B := eqApp w α a b) henv.ordered
  · exact ⟨_, hE.weak henv.ordered, .bvar .zero, hctor⟩
  · have hα' := hα.weak (B := eqApp w α a b) henv.ordered
    have ha' := ha.weak (B := eqApp w α a b) henv.ordered
    have hM' := hM.weak (B := eqApp w α a b) henv.ordered
    have hm' := hm.weak (B := eqApp w α a b) henv.ordered
    have hba' := hab.symm.weak (B := eqApp w α a b) henv.ordered
    refine ⟨``Eq.rec, [v, w], [v, w],
      [α.lift, a.lift, M.lift, m.lift, b.lift, eqReflApp w α.lift a.lift],
      [α.lift, a.lift, M.lift, m.lift, a.lift, eqReflApp w α.lift a.lift],
      ?_, ?_, hlevels, hlevels, Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl),
      .cons ⟨_, hα'⟩ (.cons ⟨_, ha'⟩ (.cons ⟨_, hM'⟩ (.cons ⟨_, hm'⟩
        (.cons hba' (.cons ⟨_, hctor⟩ .nil)))))⟩
    · rfl
    · simp [canonicalEqPrefixProgram, canonicalEqRecBody, canonicalEqRecRule,
        lamBody, instL, VLevel.inst, instOuter_cons, instOuter_nil,
        inst, instVar, mkApps, eqReflApp, lift,
        inst_liftN_lo, inst_liftN']

/-- A registered canonical Eq.rec entry realizes the manual prefix lambda as
an actual singleton prefix step whenever its typed endpoints are convertible. -/
theorem eqRecBeforeMajor_prefix_registered (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hr : RecursorRegistered env data)
    (hn : data.name = ``Eq.rec) (hlookup : registry ``Eq.rec = some data)
    (ht : VExpr.WF env U Γ (eqRecBeforeMajor v w α a M m b))
    (hab : env.IsDefEqU U Γ a b) :
    PrefixUnfold env U registry Γ ``Eq.rec [v, w] [α, a, M, m, b]
      (.lam (eqApp w α a b) m.lift) := by
  have hz := hr.eqRec_source_zero henv heq hn hΓ ht
  have hl := hr.eqRec_large heq hn
  obtain ⟨hfam, hcs, _, hrest, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  obtain ⟨i, ho, hgen⟩ := RecursorData.singletonEquation_eq hseq
  have hpat := hr.patEquation_of_empty henv hrest hgen
  obtain ⟨hv, hw, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ht
  have hlevels : ∀ l ∈ [v, w], l.WF U := by simp_all
  have hlen : [v, w].length = data.uvars := by simp [(hr.eqRec_target heq hn).1]
  obtain ⟨S, E, hS, hE, _⟩ := RecursorData.propElim_wf henv hr hl hz hlevels hlen ⟨i, ho⟩
  have hg := eqRec_prefix_generated (U := U) (α := α) (a := a) (M := M) (m := m) (b := b)
    heq hr hn hz hS hE
  have HC := canonicalEqPrefixProgram_check henv heq hΓ hpat ht hab
  exact .intro hlookup hr hn hl hlevels hz hg HC

/-- Canonical Eq supplies the real registry entry itself; no metadata or
prefix-generation hypothesis is required by operational K-prefix replay. -/
theorem eqRecBeforeMajor_prefix (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (ht : VExpr.WF env U Γ (eqRecBeforeMajor v w α a M m b))
    (hab : env.IsDefEqU U Γ a b) :
    PrefixUnfold env U env.recursorRegistry Γ ``Eq.rec [v, w] [α, a, M, m, b]
      (.lam (eqApp w α a b) m.lift) := by
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact eqRecBeforeMajor_prefix_registered henv heq hΓ hr hn hlookup ht hab

end Lean4Lean.VEnv.Strengthening
