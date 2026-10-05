import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.Typing.HeadReduction

/-! Head computation for the full presentation. Aligned native prefixes may
overlap at different lengths, so literal one-step determinism is deliberately
not part of this relation. Function and structure eta expansions belong to
FullStep; sort-typed head exposure excludes these value expansions using the
actual family declaration.
-/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

inductive FullWHRed (Γ : List VExpr) : VExpr → VExpr → Prop where
  | core : WHRed Γ e e' → FullWHRed Γ e e'
  | delta : NativeDeltaRule env univs recursorData Γ name levels arguments rhs →
      FullWHRed Γ (mkApps (.const name levels) arguments) rhs
  | quotDelta : QuotDeltaRule env univs Γ levels arguments rhs →
      FullWHRed Γ (mkApps (.const ``Quot.lift levels) arguments) rhs
  | projIota : env.projections family info →
      HasType env univs Γ (.proj family index (mkApps (.const info.ctorName levels) args)) fieldType →
      args[info.nparams + index]? = some field → HasType env univs Γ field fieldType →
      FullWHRed Γ (.proj family index (mkApps (.const info.ctorName levels) args)) field
  | app : FullWHRed Γ fn fn' → FullWHRed Γ (.app fn arg) (.app fn' arg)
  | proj : FullWHRed Γ major major' →
      FullWHRed Γ (.proj family index major) (.proj family index major')

theorem FullWHRed.fullStep (H : FullWHRed Γ e e') : FullStep Γ e e' := by
  induction H with
  | core h => exact .core h.parRed
  | delta h => exact .delta h
  | quotDelta h => exact .quotDelta h
  | projIota hl ht hi hf => exact .projIota hl ht hi hf
  | app _ ih => exact .app ih .rfl
  | proj _ ih => exact .proj ih

theorem FullWHRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : FullWHRed Γ e e') :
    FullWHRed Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H with
  | core h => exact .core (h.weakN W)
  | delta h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .delta (h.weakN henv W)
  | quotDelta h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .quotDelta (h.weakN henv W)
  | projIota hl ht hi hf =>
    have ht' := ht.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at ht' ⊢
    exact .projIota hl ht' (by simp [hi]) (hf.weakN henv W)
  | app _ ih => exact .app ih
  | proj _ ih => exact .proj ih

theorem FullWHRed.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullWHRed Γ e e') (ht : HasType env univs Γ e type) :
    IsDefEq env univs Γ e e' type := H.fullStep.defeq hΓ ht

def FullWHRedS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (FullWHRed Γ)

theorem FullWHRedS.fullReduction (H : FullWHRedS Γ e e') : FullReduction Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih h.fullStep

theorem FullWHRedS.weakN (W : Ctx.LiftN n k Γ Γ') (H : FullWHRedS Γ e e') :
    FullWHRedS Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (h.weakN W)

theorem FullWHRedS.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullWHRedS Γ e e') (ht : HasType env univs Γ e type) :
    IsDefEq env univs Γ e e' type := H.fullReduction.defeq hΓ ht

theorem FullWHRedS.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullWHRedS Γ e e') (ht : HasType env univs Γ e type) :
    HasType env univs Γ e' type := H.fullReduction.hasType hΓ ht

theorem FullWHRedS.app (H : FullWHRedS Γ f f') : FullWHRedS Γ (.app f a) (.app f' a) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.app h)

theorem FullWHRedS.proj (H : FullWHRedS Γ e e') :
    FullWHRedS Γ (.proj family index e) (.proj family index e') := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.proj h)

theorem WHRedS.full (H : WHRedS Γ e e') : FullWHRedS Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.core h)

end Lean4Lean.VEnv
