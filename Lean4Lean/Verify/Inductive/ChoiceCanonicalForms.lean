import Lean4Lean.Verify.Inductive.RuleTranslation
import Lean4Lean.Theory.CanonicalChoice

/-! # Production syntax of `Nonempty` and `Classical.choice`

The types of `Nonempty`, `Nonempty.intro` and `Classical.choice` as `Init.Prelude` submits
them (`class inductive Nonempty (α : Sort u) : Prop | intro (val : α)`, and
`axiom Classical.choice {α : Sort u} : Nonempty α → α`), stated literally and generic only in
binder and universe-parameter names. Each translates (`TrExprSyn`, hence every `TrExprS`
derivation) to the corresponding stored term of `VEnv.HasCanonicalChoice`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-- The family type of `Nonempty`: `Sort u → Prop`. -/
def nonemptyBootstrapType (u alphaName : Name) : Expr :=
  .forallE alphaName (.sort (.param u)) (.sort .zero) .default

/-- The constructor type of `Nonempty.intro`: `∀ {α : Sort u} (val : α), Nonempty α`. -/
def nonemptyBootstrapIntroType (u alphaName valName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE valName (.bvar 0) (.app (.const ``Nonempty [.param u]) (.bvar 1)) .default)
    .implicit

/-- The type of `Classical.choice`: `∀ {α : Sort u}, Nonempty α → α`. -/
def choiceBootstrapType (u alphaName hName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE hName (.app (.const ``Nonempty [.param u]) (.bvar 0)) (.bvar 1) .default)
    .implicit

section
variable {u : Name}

private theorem ofLevel_one' : VLevel.ofLevel [u] (.param u) = some (.param 0) := by
  simp [VLevel.ofLevel]

private theorem mapM_one' :
    [Level.param u].mapM (VLevel.ofLevel [u]) = some [.param 0] := by
  simp [List.mapM_cons, ofLevel_one']

/-- Build a `TrExprSyn` derivation whose target is given. -/
local syntax "canonical_choice_tr_syn" : tactic
local macro_rules | `(tactic| canonical_choice_tr_syn) => `(tactic|
  repeat' (first
    | apply TrExprSyn.forallE
    | apply TrExprSyn.lam
    | apply TrExprSyn.app
    | (apply TrExprSyn.bvar; rfl)
    | (apply TrExprSyn.sort; first | exact ofLevel_one' | rfl)
    | (apply TrExprSyn.const; exact mapM_one')))

theorem nonemptyBootstrapType_syn (alphaName : Name) :
    TrExprSyn [u] [] (nonemptyBootstrapType u alphaName) canonicalNonemptyType := by
  unfold nonemptyBootstrapType canonicalNonemptyType
  canonical_choice_tr_syn

theorem nonemptyBootstrapIntroType_syn (alphaName valName : Name) :
    TrExprSyn [u] [] (nonemptyBootstrapIntroType u alphaName valName)
      canonicalNonemptyIntroType := by
  unfold nonemptyBootstrapIntroType canonicalNonemptyIntroType
  canonical_choice_tr_syn

theorem choiceBootstrapType_syn (alphaName hName : Name) :
    TrExprSyn [u] [] (choiceBootstrapType u alphaName hName) canonicalChoiceType := by
  unfold choiceBootstrapType canonicalChoiceType
  canonical_choice_tr_syn

end

/-! ### Every translation is the stored term -/

section
variable {env : VEnv} {e : VExpr}

theorem TrExprS.eq_canonicalNonemptyType {u a : Name}
    (H : TrExprS env [u] [] (nonemptyBootstrapType u a) e) : e = canonicalNonemptyType :=
  H.toSyn.unique (nonemptyBootstrapType_syn a)

theorem TrExprS.eq_canonicalNonemptyIntroType {u a b : Name}
    (H : TrExprS env [u] [] (nonemptyBootstrapIntroType u a b) e) :
    e = canonicalNonemptyIntroType :=
  H.toSyn.unique (nonemptyBootstrapIntroType_syn a b)

theorem TrExprS.eq_canonicalChoiceType {u a b : Name}
    (H : TrExprS env [u] [] (choiceBootstrapType u a b) e) : e = canonicalChoiceType :=
  H.toSyn.unique (choiceBootstrapType_syn a b)

end

/-! ### Production constants -/

/-- A production constant with the type `Init.Prelude` gives `Nonempty`. -/
def IsProductionNonempty (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧ ∃ u a, ci.levelParams = [u] ∧ ci.type = nonemptyBootstrapType u a

/-- A production constant with the type `Init.Prelude` gives `Nonempty.intro`. -/
def IsProductionNonemptyIntro (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧
    ∃ u a b, ci.levelParams = [u] ∧ ci.type = nonemptyBootstrapIntroType u a b

/-- A production constant with the type `Init.Prelude` gives `Classical.choice`. -/
def IsProductionChoice (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧ ∃ u a b, ci.levelParams = [u] ∧ ci.type = choiceBootstrapType u a b

end Lean4Lean
