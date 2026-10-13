import Lean4Lean.Theory.Typing.Strengthening.LambdaReannotation
import Lean4Lean.Theory.Typing.Confluence.WFParams

/-! # Finite full-reduction joins with recursive domain comparisons

Typed reannotation and explicit eta expansion turn every ordinary normal comparison
into a join with a recursive domain certificate. The construction is finite by
induction on the comparison, not by normalization of its endpoints. It takes place
in the ambient context; it does not claim that generated annotations avoid an
extra binder or that its reductions can be performed in a smaller context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A finite full-reduction join with a recursively certified final comparison. -/
def DomainJoin (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a' b' n, FullReduction Γ a a' ∧ FullReduction Γ b b' ∧ DomainNormal n Γ a' b'

private theorem eta_reduction (hf : HasType Params.env univs Γ f (.forallE A B)) :
    FullReduction Γ f (.lam A (.app f.lift (.bvar 0))) := .tail .rfl (.funEta hf)

/-- Repair an ordinary normal comparison by finite typed reannotation and eta
expansion. The reducts need not preserve the support of their original endpoints:
the lambda case uses its common domain witness, and eta-both introduces its typed
function domain. This missing scope guarantee is not assumed. -/
theorem normal_domain_join (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : NormalEqN η n Γ a b) : DomainJoin Γ a b := by
  induction H with
  | refl h => exact ⟨_, _, _, .rfl, .rfl, .refl h⟩
  | sortDF h1 h2 h3 => exact ⟨_, _, _, .rfl, .rfl, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, _, _, .rfl, .rfl, .constDF h1 h2 h3 h4 h5⟩
  | appDF hf1 hf2 ha1 ha2 _ _ ihf iha =>
    obtain ⟨_, _, _, Rf1, Rf2, HF⟩ := ihf hΓ
    obtain ⟨_, _, _, Ra1, Ra2, HA⟩ := iha hΓ
    exact ⟨_, _, _, Rf1.app Ra1, Rf2.app Ra2,
      .appDF (Rf1.hasType hΓ hf1) (Rf2.hasType hΓ hf2)
        (Ra1.hasType hΓ ha1) (Ra2.hasType hΓ ha2) HF HA⟩
  | projDF hp _ ihm =>
    obtain ⟨_, _, _, Rm1, Rm2, HM⟩ := ihm hΓ
    exact ⟨_, _, _, Rm1.proj, Rm2.proj, .projDF (Rm1.proj.hasType hΓ hp) HM⟩
  | lamDF hA1 hA2 HB ihb =>
    have hΓA : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ, _, hA1.hasType.1⟩
    obtain ⟨_, hb⟩ := HB.defeq hΓA
    obtain ⟨_, _, _, Rb1, Rb2, HB'⟩ := ihb hΓA
    have hl := (IsDefEq.lamDF hA1 hb.hasType.1).hasType.2
    have hr := (IsDefEq.lamDF hA2 hb.hasType.2).hasType.2
    exact ⟨_, _, _, (lambda_reannotation hl).trans (FullReduction.lam .rfl Rb1),
      (lambda_reannotation hr).trans (FullReduction.lam .rfl Rb2),
      .lamDF hA1.hasType.1 (.refl hA1.hasType.1) HB'⟩
  | forallEDF hA1 HA hB1 HB ihA ihB =>
    have hΓA : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ, _, hA1.hasType.1⟩
    have hA2 := hA1.transU_l henv hΓ (HA.defeq hΓ)
    have hB2 := ((HB.defeq hΓA).of_l henv hΓA hB1).hasType.2
    obtain ⟨_, _, _, RA1, RA2, HA'⟩ := ihA hΓ
    obtain ⟨_, _, _, RB1, RB2, HB'⟩ := ihB hΓA
    have hAA := hA1.trans (RA1.defeq hΓ hA1.hasType.2)
    exact ⟨_, _, _, .forallE RA1 (RB1.defeqDFC hΓ (.succ .zero hA1) hB1),
      .forallE RA2 (RB2.defeqDFC hΓ (.succ .zero hA2) hB2),
      .forallEDF hAA.hasType.2 HA' ((RB1.hasType hΓA hB1).defeqDFC henv (.succ .zero hAA))
        (HB'.defeqDFC (.succ .zero hAA))⟩
  | etaL hf _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    obtain ⟨_, _, _, R1, R2, H⟩ := ih ⟨hΓ, _, hA⟩
    exact ⟨_, _, _, .lam .rfl R1, (eta_reduction hf).trans (FullReduction.lam .rfl R2),
      .lamDF hA (.refl hA) H⟩
  | etaR hf _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    obtain ⟨_, _, _, R1, R2, H⟩ := ih ⟨hΓ, _, hA⟩
    exact ⟨_, _, _, (eta_reduction hf).trans (FullReduction.lam .rfl R1), .lam .rfl R2,
      .lamDF hA (.refl hA) H⟩
  | etaBoth hf1 hf2 _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf1.isType henv hΓ).forallE_inv henv
    obtain ⟨_, _, _, R1, R2, H⟩ := ih ⟨hΓ, _, hA⟩
    exact ⟨_, _, _, (eta_reduction hf1).trans (FullReduction.lam .rfl R1),
      (eta_reduction hf2).trans (FullReduction.lam .rfl R2), .lamDF hA (.refl hA) H⟩
  | proofIrrel hP ha hb => exact ⟨_, _, _, .rfl, .rfl, .proofIrrel hP ha hb⟩

/-- Prepending reductions to a certified join does not change its final comparison. -/
theorem DomainJoin.prepend (Ra : FullReduction Γ a a') (Rb : FullReduction Γ b b')
    (H : DomainJoin Γ a' b') : DomainJoin Γ a b := by
  obtain ⟨_, _, _, Ra', Rb', H⟩ := H
  exact ⟨_, _, _, Ra.trans Ra', Rb.trans Rb', H⟩

omit [Params] in
/-- In a canonical-Eq environment, every declarative equality has a finite full
join with recursive domain certificates. This is ambient-context completeness;
its reducts and reannotation typings have no smaller-context guarantee. -/
theorem domain_join_complete {E : VEnv} (hE : E.WF) (heq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (H : E.IsDefEq U Γ a b T) :
    letI := hE.params U
    DomainJoin Γ a b := by
  letI := hE.params U
  obtain ⟨_, _, Ra, Rb, n, HN⟩ := hE.church_rosser heq hΓ H
  exact (normal_domain_join hΓ HN).prepend Ra Rb

end Lean4Lean.VEnv.Strengthening
