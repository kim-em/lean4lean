import Lean4Lean.Theory.Typing.Strengthening.BidirectionalNormal
import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop

/-! # The recursive-family loop admits a bidirectional comparison

The earlier beta-only counterexample to `HybridNormal` does not refute this
mode-indexed relation: the family argument's eta comparison is in common-type
mode, including when used in the domain of an independent lambda comparison.
No reductions of the loops are needed for this test. General descent and join
completeness remain separate obligations.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveDomain
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- Eta is allowed at the family's argument, whose common type is supplied by the
application. It is then available inside a recursively compared lambda domain. -/
theorem domain_bidirectional (hc : Params.env.constants c = some (declaration c).toVConstant) :
    BiNormal true 3 loopCtx (domainL c) (domainR c) := by
  have hf : loopCtx ⊢ fn : argType := by
    have h : loopCtx ⊢ fn : argType.lift := .bvar .zero
    simpa only [argType, lift, tower_liftN] using h
  have hb : .sort .zero :: loopCtx ⊢ .app fn.lift (.bvar 0) : .sort .zero :=
    HasType.app (hf.weak henv) (.bvar .zero)
  have HE : BiNormal true 2 loopCtx fn etaFn := .etaR hf (.refl hb)
  have hF := family_typed hc univs loopCtx
  have hf' := ((IsDefEq.eta hf).symm).hasType.2
  exact .appDF hF hF hf hf' (.refl hF) HE

/-- The self-application loops rejected by every beta-only hybrid join have a
finite bidirectional certificate. This proves coverage of that test only. -/
theorem omega_bidirectional (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) :
    BiNormal false 10 loopCtx (omegaTerm (domainL c)) (omegaTerm (domainR c)) := by
  have hΓ : OnCtx loopCtx (Params.env.IsType univs) := ⟨trivial, _, argType_typed Params.env univs []⟩
  have hD := (domain_recursive hδ).hasType.1
  have hb : domainL c :: loopCtx ⊢ selfBody : .sort .zero := by
    have hv : domainL c :: loopCtx ⊢ .bvar 0 : (domainL c).lift := .bvar .zero
    have hf := ((domain_recursive hδ).weakN henv Ctx.LiftN.one).defeq hv
    exact HasType.app hf hv
  have HL : BiNormal false 4 loopCtx (diagonal (domainL c)) (diagonal (domainR c)) :=
    .lamIndependent hD (domain_bidirectional hc) (.refl hb)
  have hl : loopCtx ⊢ diagonal (domainL c) : .forallE (domainL c) (.sort .zero) := .lam hD hb
  have hr := ((HL.defeq hΓ).of_l henv hΓ hl).hasType.2
  exact .appDF hl hr ((domain_recursive hδ).symm.defeq hl)
    ((domain_recursive hδ).symm.defeq hr) HL (.promote HL)

end Lean4Lean.VEnv.Strengthening.RecursiveDomain
