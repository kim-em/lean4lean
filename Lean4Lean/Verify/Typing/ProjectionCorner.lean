import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.InhabitedStrengthening
import Lean4Lean.Theory.Typing.ProjectionCornerCaseElim

/-!
# The open corner of the projection telescope walk

`inferProj` walks the constructor telescope of a structure. A field binder whose body has no loose
bound variables is kept without substituting anything for it, so the body, translated under the
binder, has to be translated without it. When the field's projection is typable it inhabits the
binder and substitution does this. When the environment has canonical choice
(`VEnv.HasCanonicalChoice`), the structure has no indices and its family has a registered case
eliminator, the binder is inhabited by eliminating the major into `Prop`
(`VEnv.corner_inhabit_elim`), and substitution again does it (`projectionWalkCorner_resolved`).
The remaining cases are stated here as `ProjectionWalkCorner`, an unproved conjecture taken as an
explicit argument `(hcorner : ProjectionWalkCorner)` by the top-level theorems of
`Verify/Environment.lean` and carried to the checker in `VContext`; the checker uses both
through `ProjectionWalkCorner.full`.
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

/-- The walks at which the corner is proved: canonical choice, no indices, and a registered case
eliminator of the structure's family. -/
def ProjectionWalkCornerResolved (venv : VEnv) (S : Name) (info : VProjectionInfo) : Prop :=
  venv.HasCanonicalChoice ∧ info.nindices = 0 ∧
    ∃ key schema, venv.eliminators key schema ∧ S ∈ schema.originalFamilies

/-- **The projection-walk corner.** Let `S` be a registered structure, `T₀` its constructor type at
universe levels `ls` (up to level equivalence), `e'` a major typed at `S ls (params ++ idx)` in the
context `Δ`, and `j` a field index such that the walk, after instantiating the parameters with
`params` and the first `j` fields with the projections `.proj S k e'`, reaches the binder
`∀ D, body'`. Suppose no sort of `D` satisfies the projection guard, so `.proj S j e'` is not
typable (typically a data field of a `Prop` structure; the executable, like the C++ kernel's
`infer_proj`, still walks past such a field when the rest does not depend on it). Then a closed
source body translating to `body'` under the binder `D` translates, without the binder, to the
unlifted residual.

**This is an unproved conjecture** (restricted context strengthening at the projection walk),
assumed explicitly by `addDecl.WF` and the other top-level theorems, for the walks not covered by
`projectionWalkCorner_resolved`: environments without canonical choice, structures with indices
(the C++ kernel's `infer_proj`, like the executable, accepts one-constructor families with indices),
and structures whose family has no registered case eliminator. The unrestricted version (any binder `D` whose sort fails the
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
    ¬ ProjectionWalkCornerResolved venv S info →
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

/-- The corner at a structure without indices with a registered case eliminator, under canonical
choice: the binder is inhabited (`VEnv.corner_inhabit_elim`), so removing it is substitution. -/
theorem projectionWalkCorner_resolved {venv : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name}
    {info : VProjectionInfo} {ls : List VLevel} {T₀ : VExpr} {params idx : List VExpr}
    {e' D body' : VExpr} {j : Nat} {body : Lean.Expr}
    (henv : venv.WF) (hΔ : Δ.WF venv Us.length) (hinfo : venv.projections S info)
    (hres : ProjectionWalkCornerResolved venv S info)
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
  obtain ⟨hch, hni, key, schema, hel, hS⟩ := hres
  obtain ⟨d₀, hd₀⟩ := VEnv.corner_inhabit_elim henv hch hΔ.toCtx hinfo hls hlslen hT₀ hpl hni he'
    hwalk hD hguard hel hS
  exact H.weakBV_inv₁_inhabited henv hd₀ ⟨hΔ, by simp, hD⟩ hc

/-- The projection-walk corner at every walk: proved where it is resolved, the conjecture
elsewhere. -/
theorem ProjectionWalkCorner.full (hcorner : ProjectionWalkCorner) {venv : VEnv} {Us : List Name}
    {Δ : VLCtx} {S : Name} {info : VProjectionInfo} {ls : List VLevel} {T₀ : VExpr}
    {params idx : List VExpr} {e' D body' : VExpr} {j : Nat} {body : Lean.Expr}
    (henv : venv.WF) (hΔ : Δ.WF venv Us.length) (hinfo : venv.projections S info)
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
  by_cases hres : ProjectionWalkCornerResolved venv S info
  · exact projectionWalkCorner_resolved henv hΔ hinfo hres hls hlslen hT₀ hpl he' hwalk hD hguard
      H hc
  · exact hcorner henv hΔ hinfo hres hls hlslen hT₀ hpl he' hwalk hD hguard H hc

end Lean4Lean
