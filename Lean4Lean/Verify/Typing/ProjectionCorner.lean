import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Verify.Typing.Lemmas

/-!
# The open corner of the projection telescope walk

`inferProj` walks the constructor telescope of a structure. A field binder whose body has no loose
bound variables is kept without substituting anything for it, so the body, translated under the
binder, has to be translated without it. When the field's projection is typable it inhabits the
binder and substitution does this. The remaining case is stated here as `ProjectionWalkCorner`,
an explicit hypothesis of the checker's correctness (`VEnvs.WF.projectionCorner`).
-/

namespace Lean4Lean

theorem VProjectionInfo.instantiateProjectionParameters_append :
    ∀ (T : VExpr) (xs ys : List VExpr),
      VProjectionInfo.instantiateProjectionParameters T (xs ++ ys) =
        (VProjectionInfo.instantiateProjectionParameters T xs).bind
          (VProjectionInfo.instantiateProjectionParameters · ys)
  | _, [], _ => rfl
  | .forallE _ body, x :: xs, ys =>
    VProjectionInfo.instantiateProjectionParameters_append (body.inst x) xs ys
  | .bvar .., _ :: _, _ | .sort .., _ :: _, _ | .const .., _ :: _, _ | .app .., _ :: _, _
  | .lam .., _ :: _, _ | .elim .., _ :: _, _ | .proj .., _ :: _, _ => rfl

/-- **The projection-walk corner.** Let `S` be a registered structure, `T₀` its constructor type at
universe levels `ls` (up to level equivalence), `e'` a major typed at `S ls (params ++ idx)` in the
context `Δ`, and `j` a field index such that the walk, after instantiating the parameters with
`params` and the first `j` fields with the projections `.proj S k e'`, reaches the binder
`∀ D, body'`. Suppose no sort of `D` satisfies the projection guard, so `.proj S j e'` is not
typable (typically a data field of a `Prop` structure; the executable, like the C++ kernel's
`infer_proj`, still walks past such a field when the rest does not depend on it). Then a closed
source body translating to `body'` under the binder `D` translates, without the binder, to the
unlifted residual.

**This is an open hypothesis.** The unrestricted version (any binder `D` whose sort fails the
guard) is false: extend the small context of the two-family model of
`docs/inductives/STRENGTHENING.md` with `D : Type`, `out : D → P v`, `z : SI` and
`f : SJ → Prop`; under `d : D` the proof `out d : P v` gives `SI ≡ SJ`, so `f z` translates under
the binder, while in a model with `SI` terminal, `SJ`, `P v` and `D` empty it has no translation
without it. The statement here is restricted to the walk over a registered constructor telescope
at a typed major, and is expected to hold for the environments built from declarations: every
proposition derivable from the field is also derivable from the major by eliminating the structure
into `Prop`, which defeats this countermodel. No proof is known: a syntactic inhabitant of the
data field does not exist, so induction on `TrExprS` cannot transport the typing derivations. -/
def ProjectionWalkCorner : Prop :=
  ∀ {venv : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {T₀ : VExpr} {params idx : List VExpr} {e' D body' : VExpr} {j : Nat}
    {body : Lean.Expr},
    venv.WF → Δ.WF venv Us.length → venv.projections S info →
    (∀ l ∈ ls, l.WF Us.length) → ls.length = info.uvars →
    VExpr.LEquiv Us.length T₀ (info.ctorType.instL ls) →
    params.length = info.nparams →
    venv.HasType Us.length Δ.toCtx e' (VExpr.mkApps (.const S ls) (params ++ idx)) →
    VProjectionInfo.instantiateProjectionParameters T₀
      (params ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body') →
    venv.IsType Us.length Δ.toCtx D →
    (∀ u, venv.HasType Us.length Δ.toCtx D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero)) →
    TrExprS venv Us ((none, .vlam D) :: Δ) body body' → Closed body →
    ∃ b₀, TrExprS venv Us Δ body b₀ ∧ body' = b₀.lift

end Lean4Lean
