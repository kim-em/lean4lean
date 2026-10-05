import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming

/-! Literal constant occurrences of a source term belong to the environment
of its original typing derivation. This ignores target substitutions and
metadata labels: only source `.const` nodes can contain native observations. -/
namespace Lean4Lean
namespace VExpr

def ConstantsIn (env : VEnv) : VExpr → Prop
  | .const name _ => ∃ value, env.constants name = some value
  | .app f a | .lam f a | .forallE f a => f.ConstantsIn env ∧ a.ConstantsIn env
  | .proj _ _ e => e.ConstantsIn env
  | _ => True

variable {env env' : VEnv} {e : VExpr}

theorem ConstantsIn.mono (h : e.ConstantsIn env) (le : env ≤ env') : e.ConstantsIn env' := by
  induction e with
  | const name levels => obtain ⟨value, h⟩ := h; exact ⟨value, le.constants h⟩
  | app _ _ ih₁ ih₂ | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | proj _ _ _ ih => exact ih h
  | _ => trivial

theorem ConstantsIn.instL (h : e.ConstantsIn env) (levels : List VLevel) :
    (e.instL levels).ConstantsIn env := by
  induction e with
  | app _ _ ih₁ ih₂ | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | proj _ _ _ ih => exact ih h
  | _ => exact h

theorem ConstantsIn.wrapLams (h : (wrapLams domains body).ConstantsIn env) :
    (∀ domain ∈ domains, domain.ConstantsIn env) ∧ body.ConstantsIn env := by
  induction domains with
  | nil => exact ⟨by simp, h⟩
  | cons domain domains ih =>
    obtain ⟨tail, body⟩ := ih h.2
    exact ⟨by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro h.1 tail, body⟩

theorem ConstantsIn.takeForalls
    (parsed : InductiveSignature.NativeRecursorData.takeForalls count e = some (domains, result))
    (h : e.ConstantsIn env) :
    (∀ domain ∈ domains, domain.ConstantsIn env) ∧ result.ConstantsIn env := by
  induction count generalizing e domains result with
  | zero =>
    simp only [InductiveSignature.NativeRecursorData.takeForalls, Option.some.injEq,
      Prod.mk.injEq] at parsed
    rcases parsed with ⟨rfl, rfl⟩
    exact ⟨by simp, h⟩
  | succ count ih =>
    cases e <;> simp only [InductiveSignature.NativeRecursorData.takeForalls] at parsed <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at parsed
    obtain ⟨⟨tail, body⟩, parsed, equal⟩ := parsed
    cases equal
    obtain ⟨tailKnown, bodyKnown⟩ := ih parsed h.2
    exact ⟨by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro h.1 tailKnown, bodyKnown⟩

end VExpr
namespace VEnv

/-- Both endpoints are inspected through ORIGINAL Strong children. In
particular beta and stored equations already have endpoint-typing children. -/
theorem IsDefEqStrong.constantsIn (h : IsDefEqStrong env U Γ left right type) :
    left.ConstantsIn env ∧ right.ConstantsIn env := by
  induction h with
  | bvar | sortDF | elimDF => exact ⟨trivial, trivial⟩
  | constDF lookup => exact ⟨⟨_, lookup⟩, ⟨_, lookup⟩⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | appDF _ _ _ _ _ _ _ _ _ fn arg _ =>
    exact ⟨⟨fn.1, arg.1⟩, ⟨fn.2, arg.2⟩⟩
  | projDF _ _ _ _ _ _ _ _ _ _ _ _ _ first second => exact ⟨first.2, second.2⟩
  | lamDF _ _ _ _ _ _ _ domain _ _ body _ =>
    exact ⟨⟨domain.1, body.1⟩, ⟨domain.2, body.2⟩⟩
  | forallEDF _ _ _ _ _ domain body _ =>
    exact ⟨⟨domain.1, body.1⟩, ⟨domain.2, body.2⟩⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ domain _ body arg _ result =>
    exact ⟨⟨⟨domain.1, body.1⟩, arg.1⟩, result.1⟩
  | eta _ _ _ _ _ _ _ _ domain _ _ fn lifted _ =>
    exact ⟨⟨domain.1, lifted.1, trivial⟩, fn.1⟩
  | proofIrrel _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | extra _ _ _ _ _ _ _ _ _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | elimIota _ _ _ _ _ _ _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | projIota _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | structEta _ _ _ _ _ right left => exact ⟨left.1, right.1⟩
  | unitLike _ _ _ _ _ _ left right => exact ⟨left.1, right.1⟩

/-- Strong already retains the formation children needed for the assigned
type. No derived typing proof or context-well-formedness theorem is required. -/
theorem IsDefEqStrong.typeConstantsIn (h : IsDefEqStrong env U Γ left right type) :
    type.ConstantsIn env := by
  induction h with
  | bvar _ _ formed => exact formed.constantsIn.1
  | sortDF | forallEDF => trivial
  | constDF _ _ _ _ _ _ _ formed => exact formed.constantsIn.1
  | elimDF _ _ _ _ _ _ _ formed => exact formed.constantsIn.1
  | appDF _ _ _ _ _ _ formed => exact formed.constantsIn.1
  | projDF _ _ _ _ _ _ _ formed => exact formed.constantsIn.1
  | lamDF _ _ domain body => exact ⟨domain.constantsIn.1, body.constantsIn.1⟩
  | defeqDF _ types => exact types.constantsIn.2
  | beta _ _ _ _ _ _ formed => exact formed.constantsIn.1
  | eta _ _ domain body => exact ⟨domain.constantsIn.1, body.constantsIn.1⟩
  | proofIrrel type => exact type.constantsIn.1
  | extra _ _ _ _ formed => exact formed.constantsIn.1
  | elimIota _ _ _ _ _ _ formed => exact formed.constantsIn.1
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | projIota _ _ _ _ ih _ => exact ih
  | structEta _ _ _ _ _ ih _ => exact ih
  | unitLike _ _ _ _ _ _ ih _ => exact ih

end VEnv
end Lean4Lean
