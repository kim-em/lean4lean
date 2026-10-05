import Lean4Lean.Theory.Typing.QuotWitnessTyping

/-! The concrete five-argument quotient prefix and its total typed replay. -/

namespace Lean4Lean
open VExpr InductiveSignature InductiveSignature.NativeRecursorData
namespace QuotPrefixProgram

def atFive (u v : VLevel) (alpha relation beta fn compat : VExpr) : PrefixProgram :=
  let domain := mkApps (.const ``Quot [u]) [alpha, relation]
  let proof := mkApps (witness u) [alpha.lift, relation.lift, .bvar 0]
  { domains := [domain], result := beta.lift,
    constructor := mkApps (.const ``Quot.mk [u]) [alpha.lift, relation.lift, proof]
    equation := quotDefEq
    equationBody := ⟨((quotDefEq.type.takeForalls 6).getD ([], .bvar 0)).1,
      quotDefEq.lhs.stripLams, quotDefEq.rhs.stripLams, .bvar 3⟩
    captures := [alpha.lift, relation.lift, beta.lift, fn.lift, compat.lift, proof]
    levels := [u,v] }

theorem generate_atFive : generate [u,v] [alpha, relation, beta, fn, compat] =
    some (atFive u v alpha relation beta fn compat) := by
  simp [generate, atFive, supplyType, quotLiftConst, instL, inst, VLevel.inst,
    inst_lift, ← lift_instN_lo, NativeRecursorData.takeForalls, vars, mkApps,
    quotDefEq, CaseSchema.EquationBody.extract,
    VExpr.takeForalls, stripLams]

theorem atFive_type : (atFive u v alpha relation beta fn compat).type =
    .forallE (mkApps (.const ``Quot [u]) [alpha, relation]) beta.lift := rfl

theorem atFive_rhs : (atFive u v alpha relation beta fn compat).rhs =
    .lam (mkApps (.const ``Quot [u]) [alpha, relation])
      (.app fn.lift (mkApps (witness u) [alpha.lift, relation.lift, .bvar 0])) := by
  simp [atFive, PrefixProgram.rhs, instantiateParams, quotDefEq, stripLams,
    instL, VExpr.subst, wrapLams]
end QuotPrefixProgram
namespace VEnv

private theorem InstForallsC.nil_result (H : InstForallsC env U Γ type [] result) :
    result = type := by cases H; rfl

/-- Every well-formed five-argument quotient-lift prefix at a proof source
has its concrete closed-delta replay, with no caller-supplied captures. -/
theorem QuotDeltaRule.atFive (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero)
    (H : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v]) [alpha, relation, beta, fn, compat])) :
    QuotDeltaRule env U Γ [u,v] [alpha, relation, beta, fn, compat]
      (.lam (mkApps (.const ``Quot [u]) [alpha, relation])
        (.app fn.lift (mkApps (QuotPrefixProgram.witness u) [alpha.lift, relation.lift, .bvar 0]))) := by
  obtain ⟨result, hw, hsource⟩ := HasType.mkApps_telescope henv hΓ
    (HasType.const hr.lift (ls := [u,v]) (by simpa using And.intro hu hv) rfl) H (by rfl)
  cases hw with | cons ha hw =>
    cases hw with | cons hrel hw =>
      cases hw with | cons hbeta hw =>
        cases hw with | cons hf hw =>
          cases hw with | cons hcompat hw =>
            rw [hw.nil_result] at hsource
            simp [instL, inst, VLevel.inst, inst_lift, ← lift_instN_lo] at ha hrel hbeta hf hcompat hsource
            let domain := mkApps (.const ``Quot [u]) [alpha, relation]
            have haq : env.HasType U (domain :: Γ) alpha.lift (.sort u) := ha.weak henv
            have hrq : env.HasType U (domain :: Γ) relation.lift
                (.forallE alpha.lift (.forallE alpha.lift.lift (.sort .zero))) := by
              simpa only [HasType, lift, liftN, ← lift_liftN'] using hrel.weak henv.ordered (B := domain)
            have hmajor : env.HasType U (domain :: Γ) (.bvar 0)
                (mkApps (.const ``Quot [u]) [alpha.lift, relation.lift]) := .bvar .zero
            have hproof := hr.witness_app hu hz haq hrq hmajor
            have hconstructor := (hr.reconstruct_major hu hz haq hrq hmajor).hasType.2
            have hquot : env.HasType U Γ domain (.sort u) := by
              have h1 := (HasType.const hr.quotient (ls := [u]) (by simpa using hu) rfl).app ha
              have h2 := h1.app (by simpa [instL, inst, VLevel.inst] using hrel)
              simpa [domain, mkApps, instL, inst, inst_lift, VLevel.inst] using h2
            have hquotP := IsDefEq.defeq (IsDefEq.sortDF hu (by trivial) hz) hquot
            rw [← QuotPrefixProgram.atFive_rhs]
            apply QuotDeltaRule.ofGenerated (levels := [u,v]) hr (by simpa using And.intro hu hv) hz
              QuotPrefixProgram.generate_atFive
            · exact hsource
            · intro j hj hd
              have hj' : j < 6 := hj
              match j with
              | 0 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixProgram.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst] using haq
              | 1 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixProgram.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hrq
              | 2 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixProgram.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hbeta.weak henv.ordered (B := domain)
              | 3 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixProgram.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hf.weak henv.ordered (B := domain)
              | 4 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixProgram.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hcompat.weak henv.ordered (B := domain)
              | 5 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixProgram.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hproof
              | _ + 6 => omega
            · exact ⟨domain.lift, hquotP.weak henv, hmajor, hconstructor⟩
            · let args := [alpha.lift, relation.lift, beta.lift, fn.lift, compat.lift,
                mkApps (.const ``Quot.mk [u]) [alpha.lift, relation.lift,
                  mkApps (QuotPrefixProgram.witness u) [alpha.lift, relation.lift, .bvar 0]]]
              have hm : NativeSpineMatch env U (domain :: Γ)
                  (mkApps (.const ``Quot.lift [u,v]) args)
                  (mkApps (.const ``Quot.lift [u,v]) args) :=
                ⟨_, _, _, _, _, rfl, rfl, by simpa using And.intro hu hv,
                  by simpa using And.intro hu hv,
                  .cons (.refl _) (.cons (.refl _) .nil),
                  .cons ⟨_, haq⟩ (.cons ⟨_, hrq⟩ (.cons ⟨_, hbeta.weak henv.ordered⟩
                    (.cons ⟨_, hf.weak henv.ordered⟩ (.cons ⟨_, hcompat.weak henv.ordered⟩
                      (.cons ⟨_, hconstructor⟩ .nil)))))⟩
              simpa [QuotPrefixProgram.atFive, args, domain, nativeEtaBody,
                quotDefEq, stripLams, instL, instOuter, inst, VLevel.inst,
                mkApps, lift, liftN, ← lift_instN_lo, inst_lift] using hm
end VEnv
end Lean4Lean
