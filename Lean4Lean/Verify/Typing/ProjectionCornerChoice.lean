import Lean4Lean.Verify.Typing.InhabitedStrengthening
import Lean4Lean.Theory.Typing.ProjectionCornerElim

/-!
# The projection-walk corner under canonical choice

`inferProj` walks a structure's constructor telescope, instantiating the parameters and the
earlier fields' projections. When it passes a field binder `D` whose projection fails the universe
guard, the body is translated under the binder and must be translated without it. Under canonical
choice (`VEnv.HasCanonicalChoice`) and a registered recursor of the structure into `Prop`
(`VEnv.StructurePropRecursor`), the binder is inhabited (`VEnv.corner_inhabit`), so removing it is
substitution (`TrExprS.weakBV_inv₁_inhabited`).

This is the statement of the conjecture `ProjectionWalkCorner` (on the E1 branch, in
`Verify/Typing/ProjectionCorner.lean`), stated for one environment with these two extra
hypotheses.

In the C++ kernel, every successful `infer_proj` on `.proj S i e` happens after `S`'s constructor
has been declared, and `add_inductive` declares the recursors immediately after the constructors.
The branch's staged verification has a transient window, where the types, the constructors and
the projection entries are registered but the recursors are not yet. In that window the checker
runs only on generated terms. E1 discharges the recursor hypothesis at the call site.
-/

namespace Lean4Lean

theorem projectionWalkCorner_of_choice {venv : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name}
    {info : VProjectionInfo} {ls : List VLevel} {T₀ : VExpr} {params idx : List VExpr}
    {e' D body' : VExpr} {j : Nat} {body : Lean.Expr}
    (henv : venv.WF) (hch : venv.HasCanonicalChoice) (hΔ : Δ.WF venv Us.length)
    (hinfo : venv.projections S info) (hls : ∀ l ∈ ls, l.WF Us.length)
    (hlslen : ls.length = info.uvars)
    (hT₀ : VExpr.LEquiv Us.length T₀ (info.ctorType.instL ls))
    (hpl : params.length = info.nparams) (hni : info.nindices = 0)
    (he' : venv.HasType Us.length Δ.toCtx e' (VExpr.mkApps (.const S ls) (params ++ idx)))
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (params ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : venv.IsType Us.length Δ.toCtx D)
    (hguard : ∀ u, venv.HasType Us.length Δ.toCtx D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    (hrec : venv.StructurePropRecursor Us.length S info ls)
    (H : TrExprS venv Us ((none, .vlam D) :: Δ) body body') (hc : Closed body) :
    ∃ b₀, TrExprS venv Us Δ body b₀ ∧ body' = b₀.lift := by
  obtain ⟨d₀, hd₀⟩ := VEnv.corner_inhabit henv hch hΔ.toCtx hinfo hls hlslen hT₀ hpl hni he'
    hwalk hD hguard hrec
  exact H.weakBV_inv₁_inhabited henv hd₀ ⟨hΔ, by simp, hD⟩ hc

end Lean4Lean
