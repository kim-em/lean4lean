import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Typing.LevelEquiv

/-! # Substitution identities for instantiating a minor premise at actual parameters

The projection-walk corner applies a recursor to parameters, a motive and a minor premise in an
arbitrary context. These lemmas compute the generated minor premise's type instantiated at the
actual parameters and motive, as a substitution. -/

namespace Lean4Lean
namespace VExpr

theorem Subst.lift_liftN (σ : Subst) : ∀ i, σ.lift.liftN i = σ.liftN (i + 1)
  | 0 => rfl
  | i + 1 => by
    show (σ.lift.liftN i).lift = (σ.liftN (i + 1)).lift
    rw [Subst.lift_liftN σ i]

theorem subst_wrapForalls (σ : Subst) : ∀ (ds : List VExpr) (b : VExpr),
    (wrapForalls ds b).subst σ =
      wrapForalls (ds.mapIdx fun i d => d.subst (σ.liftN i)) (b.subst (σ.liftN ds.length))
  | [], b => rfl
  | d :: ds, b => by
    have ih := subst_wrapForalls σ.lift ds b
    show VExpr.forallE (d.subst σ) ((wrapForalls ds b).subst σ.lift) = _
    rw [ih, List.mapIdx_cons]
    simp only [Subst.lift_liftN, List.length_cons]
    rfl

/-- Substituting under a binder inserted at depth `i` skips the substitution's head. -/
theorem liftN_one_subst_liftN (d : VExpr) (σ : Subst) (i : Nat) :
    (d.liftN 1 i).subst (σ.liftN i) = d.subst (σ.tail.liftN i) := by
  rw [liftN_subst]
  congr 1; funext v
  simp only [Subst.lift_l, Lift.liftVar_consN_skipN, Subst.liftN_apply, Subst.tail, liftVar]
  by_cases hv : v < i
  · simp [hv]
  · rw [if_neg hv, if_neg (by omega), if_neg hv]
    congr 2; omega

theorem liftN_subst_liftN_add (X : VExpr) (τ : Subst) (f h : Nat) :
    (X.liftN h).subst (τ.liftN (f + h)) = (X.subst (τ.liftN f)).liftN h := by
  rw [liftN_eq_subst X h, liftN_eq_subst _ h, subst_subst, subst_subst]
  congr 1; funext v
  simp only [Subst.comp, Subst.shift, subst_bvar, Subst.liftN_apply]
  by_cases hv : v < f
  · rw [if_pos (by omega), if_pos hv]; rfl
  · rw [if_neg (by omega), if_neg hv, ← liftN_eq_subst, liftN_liftN]
    congr 2; omega

theorem Subst.ofList_snoc_zero (ps : List VExpr) (M : VExpr) :
    Subst.ofList (ps ++ [M]) 0 = M := by
  simp [Subst.ofList]

/-- Instantiating the parameters, lifted past `n` new binders, and the first `i` of those
binders, is substituting the parameters beneath `i` binders and lifting past the rest. -/
theorem instOuter_params_bvarRange {X : VExpr} {ps : List VExpr} {i n : Nat}
    (hX : X.ClosedN (ps.length + i)) (hi : i ≤ n) :
    X.instOuter (ps.map (·.liftN n) ++ bvarRange i n) =
      (X.subst ((Subst.ofList ps).liftN i)).liftN (n - i) := by
  rw [instOuter_eq_subst, liftN_eq_subst _ (n - i), subst_subst]
  apply subst_congr_closedN hX
  intro v hv
  have hlen : (ps.map (·.liftN n) ++ bvarRange i n).length = ps.length + i := by simp
  rw [Subst.ofList_lt _ (by omega)]
  simp only [Subst.comp, Subst.liftN_apply, hlen]
  by_cases hvi : v < i
  · rw [if_pos hvi, List.getElem_append_right (by simp; omega)]
    simp only [subst_bvar, Subst.shift, List.length_map]
    rw [bvarRange_getElem _ _ _ (by omega)]
    congr 1; omega
  · rw [if_neg hvi, List.getElem_append_left (by simp; omega), Subst.ofList_lt _ (by omega)]
    simp only [List.getElem_map, ← liftN_eq_subst, liftN_liftN]
    have e1 : i + (n - i) = n := by omega
    have e2 : ps.length + i - 1 - v = ps.length - 1 - (v - i) := by omega
    simp only [e1, e2]

end VExpr
end Lean4Lean

namespace Lean4Lean
namespace VExpr

/-- An application or a constant: the shape of a constructor's result type, kept by
instantiation and by level equivalence. -/
def AppOrConst : VExpr → Prop
  | .app .. | .const .. => True
  | _ => False

theorem AppOrConst.inst {e : VExpr} (h : e.AppOrConst) (a : VExpr) (k : Nat) :
    (e.inst a k).AppOrConst := by
  cases e <;> simp_all [AppOrConst, VExpr.inst]

theorem AppOrConst.instOuterAt {e : VExpr} (h : e.AppOrConst) :
    ∀ (args : List VExpr) (k : Nat), (e.instOuterAt args k).AppOrConst := by
  intro args
  induction args generalizing e with
  | nil => intro _; exact h
  | cons a as ih => intro k; exact ih (h.inst a _) k

theorem AppOrConst.instL {e : VExpr} (h : e.AppOrConst) (ls : List VLevel) :
    (e.instL ls).AppOrConst := by
  cases e <;> simp_all [AppOrConst, VExpr.instL]

theorem AppOrConst.of_lequiv {e e' : VExpr} (H : LEquiv U e e') (h : e'.AppOrConst) :
    e.AppOrConst := by
  cases H <;> simp_all [AppOrConst]

theorem AppOrConst.ne_forallE {e : VExpr} (h : e.AppOrConst) : ∀ A B, e ≠ .forallE A B := by
  intro A B he; subst he; exact h

theorem AppOrConst.of_getAppFnArgs {e : VExpr} {c : Name} {ls : List VLevel}
    (h : e.getAppFnArgs.1 = .const c ls) : e.AppOrConst := by
  cases e with
  | app => trivial
  | const => trivial
  | _ =>
    simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at h

theorem instantiateProjectionParameters_wrapForalls_long :
    ∀ (n : Nat) (ds : List VExpr) (b : VExpr), b.AppOrConst → ds.length = n →
      ∀ args : List VExpr, n < args.length →
        VProjectionInfo.instantiateProjectionParameters (wrapForalls ds b) args = none := by
  intro n
  induction n with
  | zero =>
    intro ds b hb hds args h
    cases ds with
    | cons => simp at hds
    | nil =>
      cases args with
      | nil => simp at h
      | cons a as =>
        cases b <;> simp_all [AppOrConst, VProjectionInfo.instantiateProjectionParameters,
          wrapForalls]
  | succ n ih =>
    intro ds b hb hds args h
    cases ds with
    | nil => simp at hds
    | cons d ds =>
      cases args with
      | nil => simp at h
      | cons a as =>
        show VProjectionInfo.instantiateProjectionParameters
          ((wrapForalls ds b).inst a) as = none
        rw [wrapForalls_inst]
        exact ih _ _ (hb.inst a _) (by simp at hds ⊢; omega) as (by simp at h; omega)

/-- The binder reached by instantiating a telescope, level-equivalent to a wrapped telescope
ending in an application or constant, at a prefix of arguments. -/
theorem walk_binder {T₀ : VExpr} {ds : List VExpr} {r : VExpr} {args : List VExpr}
    {D body' : VExpr} (hT : LEquiv U T₀ (wrapForalls ds r)) (hr : r.AppOrConst)
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀ args = some (.forallE D body')) :
    ∃ h : args.length < ds.length, LEquiv U D ((ds[args.length]'h).instOuter args) := by
  obtain ⟨ds₀, b₀, rfl, hds, hb⟩ := hT.wrapForalls_inv
  have hb₀ := hr.of_lequiv hb
  have hlen := List.Forall₂.length_eq hds
  by_cases hn : args.length ≤ ds₀.length
  · rw [VProjectionInfo.instantiateProjectionParameters_wrapForalls _ _ _ hn] at hwalk
    by_cases hlt : args.length < ds₀.length
    · rw [List.drop_eq_getElem_cons hlt] at hwalk
      simp only [instDomsAt, wrapForalls, List.foldr_cons, Option.some.injEq,
        VExpr.forallE.injEq] at hwalk
      obtain ⟨rfl, -⟩ := hwalk
      refine ⟨by omega, ?_⟩
      rw [← instOuter_eq_instOuterAt]
      exact (List.forall₂_getElem hds _ hlt (by omega)).instOuter args
    · have he : args.length = ds₀.length := by omega
      rw [he, List.drop_length, Nat.sub_self] at hwalk
      simp only [instDomsAt, wrapForalls, List.foldr_nil, Option.some.injEq] at hwalk
      exact absurd hwalk ((hb₀.instOuterAt args 0).ne_forallE _ _)
  · rw [instantiateProjectionParameters_wrapForalls_long _ _ _ hb₀ rfl _ (by omega)] at hwalk
    cases hwalk

theorem instOuter_app_bvar2_bvar0 (ps : List VExpr) (a b c : VExpr) :
    (VExpr.app (.bvar 2) (.bvar 0)).instOuter (ps ++ [a] ++ [b] ++ [c]) = .app a c := by
  rw [instOuter_eq_subst]
  simp only [subst_app, subst_bvar,
    Subst.ofList_lt _ (show 2 < (ps ++ [a] ++ [b] ++ [c]).length by simp),
    Subst.ofList_lt _ (show 0 < (ps ++ [a] ++ [b] ++ [c]).length by simp)]
  congr 1 <;> simp [List.getElem_append_right]

end VExpr
end Lean4Lean
