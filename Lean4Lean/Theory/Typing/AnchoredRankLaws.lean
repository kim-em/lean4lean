import Lean4Lean.Theory.Typing.AnchoredRankSteps
import Lean4Lean.Theory.Typing.AnchoredSupportComposition
import Lean4Lean.Theory.Typing.AnchoredSupportStep

/-! Code support and term equality are constructed jointly by rank. Family
codes query term admissions only at the completed preceding rank; no source
fundamental theorem or same-rank equality callback occurs in this induction. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

private theorem RankLaws.succ_support
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (lower : RankLaws env U registry n) :
    SupportLaws env U registry (n + 1) := by
  have symm := SupportLaws.succ_symm henv lower.toSupportLaws (lower.lowerEquality henv)
  have compose := SupportLaws.succ_compose henv lower.toSupportLaws (lower.lowerEquality henv)
  refine ⟨symm, SupportLaws.succ_focus henv lower.toSupportLaws, compose, ?_⟩
  intro Γ left right left' right' value support other minimal typed first before after
  have formed := minimal.typed.wf_type
  exact compose _ _ _ _ _ _ _ minimal typed
    (symm _ _ _ _ formed
      (compose _ _ _ _ _ _ _ minimal typed (symm _ _ _ _ formed first) before)) after

theorem rankLaws
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (n : Nat) : RankLaws env U registry n := by
  induction n with
  | zero =>
    let codes := SupportLaws.zero (U := U) (registry := registry) henv
    refine {
      toSupportLaws := codes
      codeTrans := ?_
      termSymm := fun _ _ _ _ _ _ related => RankLaws.zero_termSymm codes related
      termTrans := fun scope _ _ _ _ _ _ _ _ before after =>
        RankLaws.zero_termTrans henv scope before after }
    intro Γ left middle right profile before after Δ ρ future atom member
    exact (before Δ ρ future atom member).compose henv (after Δ ρ future atom member)
  | succ n lower =>
    let codes := lower.succ_support henv
    exact {
      toSupportLaws := codes
      codeTrans := fun _ _ _ _ _ before after => lower.succ_codeTrans henv before after
      termSymm := fun _ _ _ _ _ _ related => lower.succ_termSymm henv codes related
      termTrans := fun scope _ _ _ _ _ _ _ _ before after =>
        lower.succ_termTrans henv scope before after }

end Lean4Lean.AnchoredSemantics
