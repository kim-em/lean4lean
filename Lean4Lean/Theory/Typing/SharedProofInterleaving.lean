import Lean4Lean.Theory.Typing.TypedWorld

/-! A common-context zipper for two traces with the same canonical ordinary
binders. Each trace may additionally allocate its own inhabited proof binders.
The zipper retains both sets of private variables and adds each shared binder
once, using its domain over the canonical shared context. -/

namespace Lean4Lean.VEnv
open VExpr
noncomputable section

namespace SplitTypedEmbedding
variable {env : VEnv} {U : Nat} {Γ Δ : List VExpr}

private theorem lift_skip (e : VExpr) (ρ : Lift) :
    e.lift' ρ.skip = (e.lift' ρ).lift := by
  rw [lift_eq_lift', ← lift'_comp]
  rfl

private theorem subst_lift_refl (σ : Subst) : σ.lift_r .refl = σ := by
  funext i
  exact lift'_refl

private theorem subst_lift_skip (σ : Subst) (ρ : Lift) :
    (σ.lift_r ρ).lift_r (.skip .refl) = σ.lift_r ρ.skip := by
  funext i
  change ((σ i).lift' ρ).lift' (.skip .refl) = (σ i).lift' ρ.skip
  rw [← lift'_comp]
  rfl

private theorem subst_rename (e : VExpr) (ρ : Lift) :
    e.subst (Subst.id.lift_r ρ) = e.lift' ρ := by
  rw [← lift'_subst, subst_id]

private def identity (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) :
    SplitTypedEmbedding env U Γ Γ where
  liftMap := .refl
  retract := .id
  weakening := by simpa only [subst_lift_refl] using Ctx.SubstEq.id henv hΓ
  typed := .id henv hΓ
  leftInv := by intro e; simp
  rightInv := by simpa only [subst_lift_refl] using Ctx.SubstEq.id henv hΓ

private theorem forward (F : SplitTypedEmbedding env U Γ Δ) (henv : env.Ordered)
    (H : env.IsDefEq U Γ e e' A) :
    env.IsDefEq U Δ (e.lift' F.liftMap) (e'.lift' F.liftMap) (A.lift' F.liftMap) := by
  simpa only [subst_rename] using H.subst henv F.weakening F.targetWF

/-- Add a target-only inhabited proof variable. Its chosen witness is used
solely by the retraction. -/
private def addPrivate (F : SplitTypedEmbedding env U Γ Δ) (henv : env.Ordered)
    (hP : env.HasType U Δ P (.sort .zero)) (hq : env.HasType U Δ q P) :
    SplitTypedEmbedding env U Γ (P :: Δ) where
  liftMap := F.liftMap.skip
  retract := F.retract.cons (q.subst F.retract)
  weakening := by
    have h := F.weakening.skip (B := P) henv
    simpa only [subst_lift_skip] using h
  typed := .cons F.typed hP (hq.subst henv F.typed F.baseWF)
  leftInv := by
    intro e
    rw [lift_skip, lift_subst_cons, F.leftInv]
  rightInv := by
    have ht := F.rightInv.skip (B := P) henv
    have htail : Ctx.SubstEq env U (P :: Δ) Subst.id.tail
        ((F.retract.cons (q.subst F.retract)).lift_r F.liftMap.skip).tail Δ := by
      have hl : Subst.id.lift_r (.skip .refl) = Subst.id.tail := by
        funext i; rfl
      have hr : (F.retract.lift_r F.liftMap).lift_r (.skip .refl) =
          ((F.retract.cons (q.subst F.retract)).lift_r F.liftMap.skip).tail := by
        funext i
        change ((F.retract i).lift' F.liftMap).lift' (.skip .refl) =
          (F.retract i).lift' F.liftMap.skip
        rw [← lift'_comp]
        rfl
      rwa [hl, hr] at ht
    refine .cons htail hP ?_
    have hq' := (F.roundTrip henv hq).hasType.2
    have heq := IsDefEq.proofIrrel (hP.weak henv)
      (show env.HasType U (P :: Δ) (.bvar 0) P.lift from .bvar .zero)
      (hq'.weak henv)
    have htype : P.subst Subst.id.tail = P.lift := by rw [← lift_subst, subst_id]
    change env.IsDefEq U (P :: Δ) (.bvar 0)
      ((q.subst F.retract).lift' F.liftMap.skip) (P.subst Subst.id.tail)
    rw [lift_skip, htype]
    exact heq

/-- Add the same source binder and its renamed domain to the target. -/
private def addShared (F : SplitTypedEmbedding env U Γ Δ) (henv : env.Ordered)
    (hA : env.HasType U Γ A (.sort level)) :
    {G : SplitTypedEmbedding env U (A :: Γ) (A.lift' F.liftMap :: Δ) //
      G.liftMap = F.liftMap.cons} := by
  have ht := F.forward henv hA
  change env.HasType U Δ (A.lift' F.liftMap) (.sort level) at ht
  have out : {G : SplitTypedEmbedding env U
      ((A.lift' F.liftMap).subst F.retract :: Γ) (A.lift' F.liftMap :: Δ) //
      G.liftMap = F.liftMap.cons} := ⟨F.underBinder henv ht, rfl⟩
  exact Eq.mp (congrArg
    (fun X => {G : SplitTypedEmbedding env U (X :: Γ) (A.lift' F.liftMap :: Δ) //
      G.liftMap = F.liftMap.cons}) (F.leftInv A)) out

end SplitTypedEmbedding

/-- `shared` is a newest-first telescope over `base`. Its domains contain
only the canonical shared variables; target-only proof variables never occur
in those canonical domains. -/
inductive SharedProofInterleaving (env : VEnv) (U : Nat) (base : List VExpr) :
    List VExpr → List VExpr → Lift → Type where
  | base : OnCtx base (env.IsType U) → SharedProofInterleaving env U base [] base .refl
  | privateStep : SharedProofInterleaving env U base shared target ρ →
      env.HasType U target P (.sort .zero) → env.HasType U target q P →
      SharedProofInterleaving env U base shared (P :: target) ρ.skip
  | sharedStep : SharedProofInterleaving env U base shared target ρ →
      env.HasType U (shared ++ base) Q (.sort level) →
      SharedProofInterleaving env U base (Q :: shared) (Q.lift' ρ :: target) ρ.cons

namespace SharedProofInterleaving
variable {env : VEnv} {U : Nat} {base shared target : List VExpr} {ρ : Lift}

def steps {shared target : List VExpr} {ρ : Lift}
    (I : SharedProofInterleaving env U base shared target ρ) : Nat := match I with
  | .base _ => 0
  | .privateStep I _ _ | .sharedStep I _ => I.steps + 1

private def embedding (I : SharedProofInterleaving env U base shared target ρ)
    (henv : env.Ordered) : {F : SplitTypedEmbedding env U (shared ++ base) target //
      F.liftMap = ρ} := by
  induction I with
  | base hΓ => exact ⟨SplitTypedEmbedding.identity henv hΓ, rfl⟩
  | privateStep I hP hq ih => exact ⟨ih.1.addPrivate henv hP hq, congrArg Lift.skip ih.2⟩
  | sharedStep I hQ ih =>
    obtain ⟨F, hF⟩ := ih
    cases hF
    exact F.addShared henv hQ

def toEmbedding (I : SharedProofInterleaving env U base shared target ρ)
    (henv : env.Ordered) : SplitTypedEmbedding env U (shared ++ base) target :=
  (I.embedding henv).1

@[simp] theorem toEmbedding_map (I : SharedProofInterleaving env U base shared target ρ)
    (henv : env.Ordered) : (I.toEmbedding henv).liftMap = ρ := (I.embedding henv).2

/-- Keep the literal insertion provenance of an initial display frame. -/
theorem toInsertion (I : SharedProofInterleaving env U base shared target ρ) :
    ProofInsertion env U (shared ++ base) target ρ := by
  induction I with
  | base hΓ => exact .refl hΓ
  | privateStep _ hP hq ih => exact ih.skip hP hq
  | sharedStep _ hQ ih => exact ih.cons hQ

/-- Both forward embeddings agree on canonical variables, and those are the
only variables whose images from the two sides can coincide. -/
structure CommonTarget (env : VEnv) (U : Nat) (leftTarget rightTarget : List VExpr)
    (leftMap rightMap : Lift) where
  target : List VExpr
  left : SplitTypedEmbedding env U leftTarget target
  right : SplitTypedEmbedding env U rightTarget target
  agreement : leftMap.comp left.liftMap = rightMap.comp right.liftMap
  overlap : ∀ i j, left.liftMap.liftVar i = right.liftMap.liftVar j →
    ∃ k, leftMap.liftVar k = i ∧ rightMap.liftVar k = j
  /-- The common target adds only inhabited proof variables to either side;
  retained binder domains are renamed literally. These histories are needed
  when a semantic witness is moved through a later dependent world. -/
  leftInsertion : ProofInsertion env U leftTarget target left.liftMap
  rightInsertion : ProofInsertion env U rightTarget target right.liftMap

namespace CommonTarget
variable {leftTarget rightTarget : List VExpr} {leftMap rightMap : Lift}

private def addLeft (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (henv : env.Ordered) (hP : env.HasType U leftTarget P (.sort .zero))
    (hq : env.HasType U leftTarget q P) :
    CommonTarget env U (P :: leftTarget) rightTarget leftMap.skip rightMap := by
  have hp' : env.HasType U C.target (P.lift' C.left.liftMap) (.sort .zero) :=
    C.left.forward henv hP
  have hq' := C.left.forward henv hq
  let F := C.left.addShared henv hP
  let G := C.right.addPrivate henv hp' hq'
  refine ⟨P.lift' C.left.liftMap :: C.target, F.1, G, ?_, ?_, ?_, ?_⟩
  · change leftMap.skip.comp F.1.liftMap = rightMap.comp C.right.liftMap.skip
    rw [F.2]
    exact congrArg Lift.skip C.agreement
  · intro i j hij
    change F.1.liftMap.liftVar i = C.right.liftMap.skip.liftVar j at hij
    rw [F.2] at hij
    cases i with
    | zero => simp only [Lift.liftVar] at hij; cases hij
    | succ i =>
      simp only [Lift.liftVar] at hij
      obtain ⟨k, hk, hk'⟩ := C.overlap i j (Nat.succ.inj hij)
      exact ⟨k, by simp only [Lift.liftVar, hk], hk'⟩
  · rw [F.2]
    exact C.leftInsertion.cons hP
  · exact C.rightInsertion.skip hp' hq'

private def addLeft_history
    (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (H : SharedProofInterleaving env U base shared C.target
      (leftMap.comp C.left.liftMap))
    (henv : env.Ordered) (hP : env.HasType U leftTarget P (.sort .zero))
    (hq : env.HasType U leftTarget q P) :
    SharedProofInterleaving env U base shared (C.addLeft henv hP hq).target
      (leftMap.skip.comp (C.addLeft henv hP hq).left.liftMap) := by
  change SharedProofInterleaving env U base shared
    (P.lift' C.left.liftMap :: C.target)
    (leftMap.skip.comp (C.left.addShared henv hP).1.liftMap)
  rw [(C.left.addShared henv hP).2]
  exact H.privateStep (C.left.forward henv hP) (C.left.forward henv hq)

private def addRight (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (henv : env.Ordered) (hP : env.HasType U rightTarget P (.sort .zero))
    (hq : env.HasType U rightTarget q P) :
    CommonTarget env U leftTarget (P :: rightTarget) leftMap rightMap.skip := by
  have hp' : env.HasType U C.target (P.lift' C.right.liftMap) (.sort .zero) :=
    C.right.forward henv hP
  have hq' := C.right.forward henv hq
  let F := C.left.addPrivate henv hp' hq'
  let G := C.right.addShared henv hP
  refine ⟨P.lift' C.right.liftMap :: C.target, F, G.1, ?_, ?_, ?_, ?_⟩
  · change leftMap.comp C.left.liftMap.skip = rightMap.skip.comp G.1.liftMap
    rw [G.2]
    exact congrArg Lift.skip C.agreement
  · intro i j hij
    change C.left.liftMap.skip.liftVar i = G.1.liftMap.liftVar j at hij
    rw [G.2] at hij
    cases j with
    | zero => simp only [Lift.liftVar] at hij; cases hij
    | succ j =>
      simp only [Lift.liftVar] at hij
      obtain ⟨k, hk, hk'⟩ := C.overlap i j (Nat.succ.inj hij)
      exact ⟨k, hk, by simp only [Lift.liftVar, hk']⟩
  · exact C.leftInsertion.skip hp' hq'
  · rw [G.2]
    exact C.rightInsertion.cons hP

private def addRight_history
    (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (H : SharedProofInterleaving env U base shared C.target
      (leftMap.comp C.left.liftMap))
    (henv : env.Ordered) (hP : env.HasType U rightTarget P (.sort .zero))
    (hq : env.HasType U rightTarget q P) :
    SharedProofInterleaving env U base shared (C.addRight henv hP hq).target
      (leftMap.comp (C.addRight henv hP hq).left.liftMap) := by
  exact H.privateStep (C.right.forward henv hP) (C.right.forward henv hq)

private def addBoth {Q : VExpr} (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (henv : env.Ordered)
    (hL : env.HasType U leftTarget (Q.lift' leftMap) (.sort level))
    (hR : env.HasType U rightTarget (Q.lift' rightMap) (.sort level)) :
    CommonTarget env U (Q.lift' leftMap :: leftTarget) (Q.lift' rightMap :: rightTarget)
      leftMap.cons rightMap.cons := by
  let F := C.left.addShared henv hL
  let G₀ := C.right.addShared henv hR
  have he : (Q.lift' rightMap).lift' C.right.liftMap =
      (Q.lift' leftMap).lift' C.left.liftMap := by
    rw [← lift'_comp, ← lift'_comp, C.agreement]
  let G : {G : SplitTypedEmbedding env U (Q.lift' rightMap :: rightTarget)
      ((Q.lift' leftMap).lift' C.left.liftMap :: C.target) //
      G.liftMap = C.right.liftMap.cons} :=
    Eq.mp (congrArg (fun X => {G : SplitTypedEmbedding env U
      (Q.lift' rightMap :: rightTarget) (X :: C.target) //
      G.liftMap = C.right.liftMap.cons}) he) G₀
  refine ⟨(Q.lift' leftMap).lift' C.left.liftMap :: C.target, F.1, G.1,
    ?_, ?_, ?_, ?_⟩
  · rw [F.2, G.2]
    exact congrArg Lift.cons C.agreement
  · intro i j hij
    rw [F.2, G.2] at hij
    cases i with
    | zero =>
      cases j with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ j => simp only [Lift.liftVar] at hij; cases hij
    | succ i =>
      cases j with
      | zero => simp only [Lift.liftVar] at hij; cases hij
      | succ j =>
        simp only [Lift.liftVar] at hij
        obtain ⟨k, hk, hk'⟩ := C.overlap i j (Nat.succ.inj hij)
        exact ⟨k + 1, by simp only [Lift.liftVar, hk], by simp only [Lift.liftVar, hk']⟩
  · rw [F.2]
    exact C.leftInsertion.cons hL
  · rw [G.2, ← he]
    exact C.rightInsertion.cons hR

private def addBoth_history {Q : VExpr}
    (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (H : SharedProofInterleaving env U base shared C.target
      (leftMap.comp C.left.liftMap))
    (henv : env.Ordered) (hQ : env.HasType U (shared ++ base) Q (.sort level))
    (hL : env.HasType U leftTarget (Q.lift' leftMap) (.sort level))
    (hR : env.HasType U rightTarget (Q.lift' rightMap) (.sort level)) :
    SharedProofInterleaving env U base (Q :: shared) (C.addBoth henv hL hR).target
      (leftMap.cons.comp (C.addBoth henv hL hR).left.liftMap) := by
  change SharedProofInterleaving env U base (Q :: shared)
    ((Q.lift' leftMap).lift' C.left.liftMap :: C.target)
    (leftMap.cons.comp (C.left.addShared henv hL).1.liftMap)
  rw [(C.left.addShared henv hL).2]
  simpa only [lift'_comp, Lift.comp] using H.sharedStep hQ

/-- In particular, a private variable from either side is never identified
with any variable from the other side. -/
theorem private_left_distinct
    (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (hi : ∀ k, leftMap.liftVar k ≠ i) (j : Nat) :
    C.left.liftMap.liftVar i ≠ C.right.liftMap.liftVar j := by
  intro h
  obtain ⟨k, hk, _⟩ := C.overlap i j h
  exact hi k hk

theorem private_right_distinct
    (C : CommonTarget env U leftTarget rightTarget leftMap rightMap)
    (hj : ∀ k, rightMap.liftVar k ≠ j) (i : Nat) :
    C.left.liftMap.liftVar i ≠ C.right.liftMap.liftVar j := by
  intro h
  obtain ⟨k, _, hk⟩ := C.overlap i j h
  exact hj k hk

end CommonTarget

/-- Merge two histories by retaining each private event separately and adding
each canonical shared event once. The recursion removes an event from at
least one input, including when private events alternate between the inputs. -/
def commonTargetWithHistory {shared leftTarget rightTarget : List VExpr}
    {leftMap rightMap : Lift}
    (I : SharedProofInterleaving env U base shared leftTarget leftMap)
    (J : SharedProofInterleaving env U base shared rightTarget rightMap)
    (henv : env.Ordered) :
    (C : CommonTarget env U leftTarget rightTarget leftMap rightMap) ×'
      SharedProofInterleaving env U base shared C.target
        (leftMap.comp C.left.liftMap) :=
  match I, J with
  | .privateStep I hP hq, J =>
    let C := commonTargetWithHistory I J henv
    ⟨C.1.addLeft henv hP hq, C.1.addLeft_history C.2 henv hP hq⟩
  | I, .privateStep J hP hq =>
    let C := commonTargetWithHistory I J henv
    ⟨C.1.addRight henv hP hq, C.1.addRight_history C.2 henv hP hq⟩
  | .base hΓ, .base _ => by
    refine ⟨⟨base, SplitTypedEmbedding.identity henv hΓ,
      SplitTypedEmbedding.identity henv hΓ, rfl, ?_, .refl hΓ, .refl hΓ⟩, .base hΓ⟩
    intro i j hij
    exact ⟨i, rfl, hij⟩
  | .sharedStep I hQ, .sharedStep J _ => by
    have hL := (I.toEmbedding henv).forward henv hQ
    have hR := (J.toEmbedding henv).forward henv hQ
    simp only [toEmbedding_map, lift'] at hL hR
    let C := commonTargetWithHistory I J henv
    exact ⟨C.1.addBoth henv hL hR, C.1.addBoth_history C.2 henv hQ hL hR⟩
termination_by I.steps + J.steps
decreasing_by all_goals simp only [steps]; omega

def commonTarget {leftTarget rightTarget : List VExpr} {leftMap rightMap : Lift}
    (I : SharedProofInterleaving env U base shared leftTarget leftMap)
    (J : SharedProofInterleaving env U base shared rightTarget rightMap)
    (henv : env.Ordered) :
    CommonTarget env U leftTarget rightTarget leftMap rightMap :=
  (I.commonTargetWithHistory J henv).1

/-- The merged context retains the actual private/shared event history, so
later comparison can extend or merge it again without recovering provenance
from an arbitrary split embedding. -/
def commonTarget_history {leftTarget rightTarget : List VExpr} {leftMap rightMap : Lift}
    (I : SharedProofInterleaving env U base shared leftTarget leftMap)
    (J : SharedProofInterleaving env U base shared rightTarget rightMap)
    (henv : env.Ordered) :
    SharedProofInterleaving env U base shared (I.commonTarget J henv).target
      (leftMap.comp (I.commonTarget J henv).left.liftMap) :=
  (I.commonTargetWithHistory J henv).2

end SharedProofInterleaving
end
end Lean4Lean.VEnv
