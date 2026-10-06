import Lean4Lean.Theory.Inductive.RestorationDefEq
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.IotaLemmas

/-! # Subject reduction for a single beta step

`VEnv.BetaSubjectReduction` follows from unique typing and injectivity of Pi types
(`IsDefEq.uniq`, `IsDefEqU.forallE_inv`).
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

theorem WF.betaSubjectReduction (henv : VEnv.WF env) : env.BetaSubjectReduction U := by
  intro Γ A b a hΓ T H
  obtain ⟨A', B', hf, ha⟩ := H.app_inv henv.ordered hΓ
  -- `T` agrees with the codomain of the application rule.
  have hT : env.IsDefEqU U Γ (B'.inst a) T :=
    let ⟨_, h⟩ := IsDefEq.uniq henv hΓ (.appDF hf ha) H; ⟨_, h⟩
  obtain ⟨B, hB, hb⟩ := HasType.lam_inv' henv hΓ hf
  obtain ⟨⟨_, hAA'⟩, _, hBB'⟩ := IsDefEqU.forallE_inv henv hΓ hB
  have ha' : env.HasType U Γ a A := .defeqDF hAA'.symm ha
  have hbeta : env.IsDefEq U Γ (.app (.lam A b) a) (b.inst a) (B.inst a) := .beta hb ha'
  have hBinst : env.IsDefEqU U Γ (B.inst a) (B'.inst a) :=
    IsDefEqU.instN henv.ordered .zero ⟨_, hBB'⟩ ha'
  exact (hBinst.trans henv hΓ hT).defeqDF henv hΓ hbeta

end VEnv
end Lean4Lean
