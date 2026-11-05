import Lean4Lean.Theory.Typing.Strengthening.ProofErasureGenericContextBeta
import Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution

/-! # Administrative beta cleanup for arbitrary eta telescopes

Only the applications introduced when opening the displayed telescope reduce.
The arbitrary residual body is neither normalized nor inspected.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaTelescope
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Insert one external binder while preserving every preceding telescope slot. -/
def liftDomains : List VExpr → Nat → List VExpr
  | [], _ => []
  | A :: ds, k => A.liftN 1 k :: liftDomains ds (k+1)

/-- Insertion preserves the number of displayed binders. -/
theorem liftDomains_length : (liftDomains ds k).length = ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons A ds ih => simp only [liftDomains, List.length_cons, ih]

/-- The shifted telescope is the literal type of a fresh generic function. -/
theorem wrapForalls_lift :
    (VExpr.wrapForalls ds T).liftN 1 k =
      VExpr.wrapForalls (liftDomains ds k) (T.liftN 1 (k+ds.length)) := by
  induction ds generalizing k with
  | nil => rfl
  | cons A ds ih =>
    change VExpr.forallE (A.liftN 1 k) ((VExpr.wrapForalls ds T).liftN 1 (k+1)) =
      VExpr.forallE (A.liftN 1 k)
        (VExpr.wrapForalls (liftDomains ds (k+1)) (T.liftN 1 (k+(ds.length+1))))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (VExpr.forallE (A.liftN 1 k)) (ih (k := k+1))

/-- Instantiating the inserted generic variable restores all original domains. -/
theorem inst_liftDomains (ds : List VExpr) (a : VExpr) (k : Nat) :
    VExpr.instDomains (liftDomains ds k) a k = ds := by
  induction ds generalizing k with
  | nil => rfl
  | cons A ds ih => simp only [liftDomains, VExpr.instDomains, VExpr.inst_liftN, ih]

/-- Substituting a function into its generic eta telescope yields precisely the
eta opening of that function, with the original dependent annotations. -/
theorem generic_inst (ds : List VExpr) (a : VExpr) :
    (VExpr.wrapLams (liftDomains ds 0) (etaOpen ds.length (.bvar 0))).inst a =
      VExpr.wrapLams ds (etaOpen ds.length a) := by
  rw [VExpr.wrapLams_inst, liftDomains_length, inst_liftDomains]
  rw [etaOpen_instN]
  simp [VExpr.inst, VExpr.instVar]

/-- Original beta reduction is stable under insertion of fresh binders. -/
theorem beta_lift (R : VExpr.BetaRed a b) (n k : Nat) :
    VExpr.BetaRed (a.liftN n k) (b.liftN n k) := by
  induction R generalizing k with
  | refl => exact .refl
  | trans _ _ ih₁ ih₂ => exact (ih₁ k).trans (ih₂ k)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ k) (ih₂ k)
  | proj _ ih => exact .proj (ih k)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ k) (ih₂ (k+1))
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ k) (ih₂ (k+1))
  | beta => rw [VExpr.liftN_inst_hi]; exact .beta

/-- Opening a function with fresh variables preserves beta paths. -/
theorem beta_etaOpen (R : VExpr.BetaRed a b) (n : Nat) :
    VExpr.BetaRed (etaOpen n a) (etaOpen n b) := by
  induction n generalizing a b with
  | zero => exact R
  | succ n ih => exact ih (.app (beta_lift R 1 0) .refl)

/-- Closing a beta path beneath fixed domains preserves it. -/
theorem beta_wrapLams (R : VExpr.BetaRed a b) (ds : List VExpr) :
    VExpr.BetaRed (VExpr.wrapLams ds a) (VExpr.wrapLams ds b) := by
  induction ds with
  | nil => exact R
  | cons A ds ih => exact .lam .refl ih

/-- Fresh application cancels the full displayed lambda prefix. -/
theorem etaOpen_wrapLams_beta (ds : List VExpr) (b : VExpr) :
    VExpr.BetaRed (etaOpen ds.length (VExpr.wrapLams ds b)) b := by
  induction ds with
  | nil => exact .refl
  | cons A ds ih =>
    have R : VExpr.BetaRed
        (.app (VExpr.wrapLams (A :: ds) b).lift (.bvar 0)) (VExpr.wrapLams ds b) := by
      simpa only [VExpr.wrapLams, List.foldr_cons, VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using
        (VExpr.BetaRed.beta (A := A.lift) (b := (VExpr.wrapLams ds b).liftN 1 1) (a := .bvar 0))
    exact (beta_etaOpen R ds.length).trans ih

/-- Append one final lambda after an arbitrary fixed prefix. -/
theorem wrapLams_append_one (ds : List VExpr) (A b : VExpr) :
    VExpr.wrapLams (ds ++ [A]) b = VExpr.wrapLams ds (.lam A b) := by
  induction ds with
  | nil => rfl
  | cons X ds ih => exact congrArg (VExpr.lam X) ih

/-- Append one final Pi after an arbitrary fixed prefix. -/
theorem wrapForalls_append_one (ds : List VExpr) (A B : VExpr) :
    VExpr.wrapForalls (ds ++ [A]) B = VExpr.wrapForalls ds (.forallE A B) := by
  induction ds with
  | nil => rfl
  | cons X ds ih => exact congrArg (VExpr.forallE X) ih

/-- A generic eta telescope one binder longer than the supplied lambda prefix
beta-cleans to eta of its residual body, at arbitrary finite binder depth. -/
theorem generic_inst_wrapLams_beta (ds : List VExpr) (A f : VExpr) :
    VExpr.BetaRed
      ((VExpr.wrapLams (liftDomains (ds ++ [A]) 0)
        (etaOpen (ds ++ [A]).length (.bvar 0))).inst (VExpr.wrapLams ds f))
      (VExpr.wrapLams ds (.lam A (.app f.lift (.bvar 0)))) := by
  rw [generic_inst, List.length_append, List.length_cons, List.length_nil,
    Nat.add_zero, etaOpen_succ, wrapLams_append_one]
  exact beta_wrapLams (.lam .refl (.app (beta_lift (etaOpen_wrapLams_beta ds f) 1 0) .refl)) ds

end Lean4Lean.VEnv.Strengthening.EtaTelescope
