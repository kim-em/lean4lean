import Lean4Lean.Theory.Typing.Basic

/-!
The eta/beta/native overlap has an equality repair that uses whole-function
type conversion, without extracting a conversion between the binder domains.
The body equality below may contain native computation using the fresh binder;
its endpoint need no longer have eta syntax.

This certificate checks equality soundness in the production inference rules.
It does not establish a confluent reduction, a decreasing measure for eta
ancestry, or Pi injectivity. The proposed annotated calculus supplies whole-type
conversion by structural type uniqueness; raw type uniqueness is not assumed
or proved here. These premises cannot become new checker caller obligations.
-/
namespace Lean4Lean.VEnv.EtaResidualObligation

/-- Cancel an eta expansion after typed body computation, then apply the
function at a converted whole Pi type. The argument is never substituted
into the body under the other domain. -/
theorem residualApplication
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A A' B B' f r a : VExpr} {u v : VLevel}
    (hA' : env.HasType U Γ A' (.sort v))
    (hF : env.HasType U Γ f (.forallE A' B'))
    (hBody : env.IsDefEq U (A' :: Γ)
      (.app f.lift (.bvar 0)) r B')
    (hWhole : env.IsDefEq U Γ (.forallE A' B') (.forallE A B) (.sort u))
    (ha : env.HasType U Γ a A) :
    env.IsDefEq U Γ (.app (.lam A' r) a) (.app f a) (B.inst a) := by
  have hResidual : env.IsDefEq U Γ (.lam A' r) f (.forallE A' B') :=
    .trans (.lamDF hA' (.symm hBody)) (.eta hF)
  exact .appDF (.defeqDF hWhole hResidual) ha

/-- The complete composite peak, including the original beta contractum.
This is a declarative equality, not a forward reduction joining the branches. -/
theorem betaResidualEquality
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A A' B B' t r a : VExpr} {u v : VLevel}
    (hA' : env.HasType U Γ A' (.sort v))
    (hF : env.HasType U Γ (.lam A t) (.forallE A' B'))
    (hBody : env.IsDefEq U (A' :: Γ)
      (.app (VExpr.lam A t).lift (.bvar 0)) r B')
    (hWhole : env.IsDefEq U Γ (.forallE A' B') (.forallE A B) (.sort u))
    (ht : env.HasType U (A :: Γ) t B)
    (ha : env.HasType U Γ a A) :
    env.IsDefEq U Γ (.app (.lam A' r) a) (t.inst a) (B.inst a) :=
  .trans (residualApplication hA' hF hBody hWhole ha) (.beta ht ha)

/-- A residual body equality can compare two arbitrary functions before they
are applied at a converted whole Pi type. This generalizes equality soundness
past the point where the source function is syntactically a lambda. -/
theorem extensionalResidualApplication
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A B D E f0 f1 a : VExpr} {u v : VLevel}
    (hA : env.HasType U Γ A (.sort v))
    (hF0 : env.HasType U Γ f0 (.forallE A B))
    (hF1 : env.HasType U Γ f1 (.forallE A B))
    (hBody : env.IsDefEq U (A :: Γ)
      (.app f0.lift (.bvar 0)) (.app f1.lift (.bvar 0)) B)
    (hWhole : env.IsDefEq U Γ (.forallE A B) (.forallE D E) (.sort u))
    (ha : env.HasType U Γ a D) :
    env.IsDefEq U Γ (.app f1 a) (.app f0 a) (E.inst a) := by
  have hFunctions : env.IsDefEq U Γ f1 f0 (.forallE A B) :=
    .trans (.symm (.eta hF1))
      (.trans (.lamDF hA (.symm hBody)) (.eta hF0))
  exact .appDF (.defeqDF hWhole hFunctions) ha

/-- The caller domain stays `D` throughout eta followed by beta. The residual
body equality remains in `A :: Γ`, including at the middle application whose
lambda binds `D`. Thus the proposed observation-transfer call that substitutes
`a` into `hBody` needs typing at `A`, while beta supplies typing at `D`.

This checks that the problematic composition and both residual equalities are
well typed using whole-Pi conversion. It does not prove that domain conversion
is impossible, that the proposed recursive call is justified, or that the
observation relation has a sound global induction. -/
theorem fixedCallerResidualComposition
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A B D E t f0 a : VExpr} {u v w : VLevel}
    (hA : env.HasType U Γ A (.sort v))
    (hD : env.HasType U Γ D (.sort w))
    (ht : env.HasType U (D :: Γ) t E)
    (ha : env.HasType U Γ a D)
    (hWhole : env.IsDefEq U Γ (.forallE D E) (.forallE A B) (.sort u))
    (hF0 : env.HasType U Γ f0 (.forallE A B))
    (hBody : env.IsDefEq U (A :: Γ)
      (.app f0.lift (.bvar 0))
      (.app (VExpr.lam D t).lift (.bvar 0)) B) :
    let etaBody := VExpr.app (VExpr.lam D t).lift (.bvar 0)
    let source := VExpr.app (.lam A etaBody) a
    let middle := VExpr.app (.lam D t) a
    env.IsDefEq U Γ source middle (E.inst a) ∧
    env.IsDefEq U Γ middle (t.inst a) (E.inst a) ∧
    env.IsDefEq U Γ source (.app f0 a) (E.inst a) ∧
    env.IsDefEq U Γ middle (.app f0 a) (E.inst a) := by
  have hLambda : env.HasType U Γ (.lam D t) (.forallE D E) :=
    .lamDF hD ht
  have hLambdaAtA : env.HasType U Γ (.lam D t) (.forallE A B) :=
    .defeqDF hWhole hLambda
  exact ⟨.appDF (.defeqDF (.symm hWhole) (.eta hLambdaAtA)) ha,
    .beta ht ha,
    residualApplication hA hF0 hBody (.symm hWhole) ha,
    extensionalResidualApplication hA hF0 hLambdaAtA hBody (.symm hWhole) ha⟩

#print axioms residualApplication
#print axioms betaResidualEquality
#print axioms extensionalResidualApplication
#print axioms fixedCallerResidualComposition
end Lean4Lean.VEnv.EtaResidualObligation
