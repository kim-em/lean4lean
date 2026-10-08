import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.InhabitedSubstitution
import Lean4Lean.Theory.Typing.ProjectionCornerCaseElim
import Lean4Lean.Theory.Typing.ProjectionCornerChoice

/-!
# The corner of the projection telescope walk

`inferProj` walks the constructor telescope of a structure. A field binder whose body has no loose
bound variables is kept without substituting anything for it, so the body, translated under the
binder, has to be translated without it. When the field's projection is typable it inhabits the
binder and substitution does this. Otherwise (typically a data field of a `Prop` structure, which
the executable, like the C++ kernel's `infer_proj`, still walks past when the rest does not depend
on it) the binder is inhabited by eliminating the major into `Prop` through the structure's
registered case eliminator and applying canonical choice (`VEnv.WF.corner_inhabit_choice`), and
substitution again removes it (`projectionWalkCorner_choice`). Every registered structure has a
registered case eliminator in a well-formed environment (`VEnv.WF.projections_eliminated`).
This is one of the two ways a checker context resolves the corner (`ProjectionCorner`); the other,
used by `addDecl.WF_of_canonicalEq`, is a telescope certificate of every visible constructor
(`TelTrN.delete_closed`), which needs no choice.
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
`∀ D, body'`, where no sort of `D` satisfies the projection guard. In a well-formed environment
with canonical choice, a closed source body translating to `body'` under the binder `D` translates,
without the binder, to the unlifted residual. -/
theorem projectionWalkCorner_choice {venv : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name}
    {info : VProjectionInfo} {ls : List VLevel} {T₀ : VExpr} {params idx : List VExpr}
    {e' D body' : VExpr} {j : Nat} {body : Lean.Expr}
    (henv : venv.WF) (hch : venv.HasCanonicalChoice) (hΔ : Δ.WF venv Us.length)
    (hinfo : venv.projections S info)
    (hls : ∀ l ∈ ls, l.WF Us.length) (hlslen : ls.length = info.uvars)
    (hT₀ : VExpr.LEquiv Us.length T₀ (info.ctorType.instL ls))
    (hpl : params.length = info.nparams)
    (he' : venv.HasType Us.length Δ.toCtx e' (VExpr.mkApps (.const S ls) (params ++ idx)))
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (params ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : venv.IsType Us.length Δ.toCtx D)
    (hguard : ∀ u, venv.HasType Us.length Δ.toCtx D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    (H : TrExprS venv Us ((none, .vlam D) :: Δ) body body') (hc : Closed body) :
    ∃ b₀, TrExprS venv Us Δ body b₀ ∧ body' = b₀.lift := by
  obtain ⟨d₀, hd₀⟩ := henv.corner_inhabit_choice hch hΔ.toCtx hinfo hls hlslen hT₀ hpl he'
    hwalk hD hguard
  exact H.weakBV_inv₁_inhabited henv hd₀ ⟨hΔ, by simp, hD⟩ hc

end Lean4Lean
