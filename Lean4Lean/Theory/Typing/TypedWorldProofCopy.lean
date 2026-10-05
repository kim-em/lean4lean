import Lean4Lean.Theory.Typing.TypedWorldProofComparison
import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming

/-! Contract a fresh canonical proof prefix into a specified existing typed
copy. The base variables remain literal identities, and every copied prefix
variable has exactly the caller's chosen value. -/
namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

def proofCopyReadback : Subst → Nat → Subst
  | _, 0 => Subst.id
  | values, n + 1 => (proofCopyReadback values.tail n).cons values.head

@[simp] theorem proofCopyReadback_base (values : Subst) (n : Nat) :
    Subst.lift_l (.skipN .refl n) (proofCopyReadback values n) = Subst.id := by
  induction n generalizing values with
  | zero => rfl
  | succ n ih => exact ih values.tail

/-- The freshly renamed prefix reads back to the specified complete old
substitution, not merely to a definitionally equal tuple. -/
theorem proofCopyReadback_copy (values : Subst) (n : Nat) (ρ : Lift)
    (base : Subst.lift_l (.skipN .refl n) values = Subst.id.lift_r ρ) :
    Subst.lift_l (ρ.consN n) (proofCopyReadback values n) = values := by
  induction n generalizing values with
  | zero => exact base.symm
  | succ n ih =>
    funext i
    cases i with
    | zero => rfl
    | succ i => exact congrFun (ih values.tail base) i

theorem proofCopyReadback_typed
    {env : VEnv} {U : Nat} {source target : List VExpr} {ρ : Lift} {values : Subst}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (added : List VExpr)
    (typed : Ctx.SubstEq env U target values values (added ++ source))
    (base : Subst.lift_l (.skipN .refl added.length) values = Subst.id.lift_r ρ)
    (formed : OnCtx (renameAdded ρ added ++ target) (env.IsType U)) :
    Ctx.SubstEq env U target (proofCopyReadback values added.length)
      (proofCopyReadback values added.length) (renameAdded ρ added ++ target) := by
  induction added generalizing values with
  | nil => exact .id henv hTarget
  | cons P added ih =>
    cases typed with
    | cons typed oldType head =>
      obtain ⟨tailWF, level, headWF⟩ := formed
      refine .cons (ih typed base tailWF) headWF ?_
      have commute : (P.lift' (ρ.consN added.length)).subst
          (proofCopyReadback values.tail added.length) = P.subst values.tail := by
        rw [subst_lift', proofCopyReadback_copy values.tail added.length ρ base]
      change env.HasType U target values.head
        ((P.lift' (ρ.consN added.length)).subst (proofCopyReadback values.tail added.length))
      rw [commute]
      exact head

/-- The inserted proof slots can be folded onto an existing typed copy,
including a copy retained through arbitrary later data binders. -/
def ProofInsertion.copyRetraction
    {env : VEnv} {U : Nat} {source target : List VExpr} {ρ : Lift} {values : Subst}
    (henv : env.Ordered) (added : List VExpr)
    (inserted : ProofInsertion env U target (renameAdded ρ added ++ target)
      (.skipN .refl added.length))
    (typed : Ctx.SubstEq env U target values values (added ++ source))
    (base : Subst.lift_l (.skipN .refl added.length) values = Subst.id.lift_r ρ) :
    SplitTypedEmbedding env U target (renameAdded ρ added ++ target) :=
  inserted.withRetraction henv (proofCopyReadback values added.length)
    (proofCopyReadback_typed henv inserted.baseWF added typed base (inserted.targetWF henv))
    (fun e => by rw [subst_lift', proofCopyReadback_base, subst_id])

end Lean4Lean.VEnv
