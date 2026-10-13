import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping

/-! # General closed propositional elimination for singleton reconstruction

The target proposition may depend on all parameters, indices and the major.
A branch proved at the constructor gives a closed proof-producing function.
This factors the telescope plumbing needed to extract equality witnesses for
data slots, as well as the existing proof-field extraction.
-/
namespace Lean4Lean.PropElim
open VExpr VEnv SingletonLayout
variable (S : SingletonLayout) (params : List VExpr) (E : PropElim)

/-- Motive with an arbitrary propositional body in the generic context. -/
def motiveOf (body : VExpr) : VExpr :=
  wrapLams (S.indices ++ [majorTy S params E]) body

/-- Closed eliminator program for the supplied proposition and constructor branch. -/
def valueOf (body branch : VExpr) : VExpr :=
  wrapLams (params ++ S.indices ++ [majorTy S params E])
    (mkApps E.elimHead (genericPa S params ++
      [(motiveOf S params E body).liftN (S.indices.length + 1),
        (E.minorOf (motiveOf S params E body) branch).liftN (S.indices.length + 1)] ++
      bvarRange (S.indices.length + 1) (S.indices.length + 1)))

/-- Type of the closed proof-producing program. -/
def typeOf (body : VExpr) : VExpr :=
  wrapForalls (params ++ S.indices ++ [majorTy S params E]) body

variable {S params E} {body branch : VExpr}

/-- A propositional body and its constructor branch suffice to type the generic
closed program. No alignment of occurrence indices is required. -/
theorem valueOf_typed (henv : env.WF) (W : E.WF S params env U)
    (hbody : env.HasType U (params ++ S.indices ++ [majorTy S params E]).reverse body (.sort .zero))
    (hbr0 : env.HasType U (params ++ S.fields).reverse branch
      (body.instOuter (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]))) :
    env.HasType U [] (valueOf S params E body branch) (typeOf S params E body) := by
  have T := W.typed
  -- the generic context: parameters, indices, major
  have hmcl : (majorTy S params E).ClosedN (params.length + S.indices.length) := by
    have hc := CtxWF.closed henv.ordered (T.indicesCtx S.indices.length (Nat.le_refl _))
    rw [List.take_length] at hc
    have := (W.majorTy_typed.closedN' henv.ordered.closed hc).1
    simpa [Nat.add_comm] using this
  have hΔg : OnCtx (params ++ S.indices ++ [majorTy S params E]).reverse (env.IsType U) := by
    have h1 := T.indicesCtx S.indices.length (Nat.le_refl _)
    rw [List.take_length] at h1
    rw [List.reverse_append]
    exact ⟨h1, _, W.majorTy_typed⟩
  have hmot : env.HasType U params.reverse (motiveOf S params E body) (motiveType S params E) := by
    unfold motiveOf motiveType
    apply HasType.wrapLams_of (by simpa [List.reverse_append, List.append_assoc] using hΔg)
    simpa [List.reverse_append, List.append_assoc] using hbody
  have hΔb : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  -- the motive applied to the constructor is that type
  have hmajI : (majorTy S params E).instOuter (branchPa S params ++ E.ctorIndices) =
      VExpr.mkApps E.family (branchPa S params ++ E.ctorIndices) := by
    have hl : (branchPa S params ++ E.ctorIndices).length = params.length + S.indices.length := by
      simp [branchPa, W.ctorIndices_length]; try omega
    simp only [majorTy]
    simp only [VExpr.instOuter_mkApps, instOuter_closed0 W.family_closed]
    rw [List.map_append, VExpr.instOuter_bvarRange _ _ _ (by omega) (by rw [hl]; exact Nat.le_refl _),
      VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by rw [hl]; omega), hl]
    simp [branchPa, ← W.ctorIndices_length]
  have htel3 : TelInst env U (params ++ S.fields).reverse
      (params ++ (S.indices ++ [majorTy S params E]))
      (branchPa S params ++ (E.ctorIndices ++ [ctorApp S params E])) := by
    have := W.ctorIndices_typed.append_one (d := majorTy S params E) (a := ctorApp S params E)
      (by rw [hmajI]; exact W.ctor_typed)
    simpa [List.append_assoc] using this
  have hDcl : ∀ i (h : i < (S.indices ++ [majorTy S params E]).length),
      ((S.indices ++ [majorTy S params E])[i]).ClosedN (params.length + i) := by
    intro i h
    by_cases hi : i < S.indices.length
    · rw [List.getElem_append_left hi]; exact T.scope.indices i hi
    · have : i = S.indices.length := by simp at h; omega
      subst this; simpa using hmcl
  have hD := TelInst.unlift (r := S.fields.length) hDcl rfl htel3
  have hmotW := hmot.weakN henv.ordered (Ctx.LiftN.zero S.fields.reverse)
  simp only [List.length_reverse, motiveType, liftN_wrapForalls] at hmotW
  rw [← List.reverse_append] at hmotW
  have hT' := HasType.mkApps_of_tel (by simpa [VExpr.liftN] using hmotW) hD
  simp only [VExpr.instOuter_sort] at hT'
  have hBcl : body.ClosedN
      (params.length + (S.indices ++ [majorTy S params E]).length) := by
    have hc := CtxWF.closed henv.ordered hΔg
    have := (hbody.closedN' henv.ordered.closed hc).1
    simp only [List.length_reverse, List.length_append, List.length_singleton] at this
    simp only [List.length_append, List.length_singleton]
    rwa [show params.length + (S.indices.length + 1) = params.length + S.indices.length + 1 by omega]
  have hbeta := VExpr.WF.beta_wrapLams henv hΔb
    (domains := (S.indices ++ [majorTy S params E]).mapIdx fun l d => d.liftN S.fields.length l)
    (args := E.ctorIndices ++ [ctorApp S params E])
    (body := body.liftN S.fields.length
        (S.indices ++ [majorTy S params E]).length)
    (by simp [W.ctorIndices_length])
    (by
      have := hT'
      rw [show motiveOf S params E body = VExpr.wrapLams (S.indices ++ [majorTy S params E])
        body from rfl, liftN_wrapLams] at this
      exact ⟨_, this⟩)
  have hR : (body.liftN S.fields.length
        (S.indices ++ [majorTy S params E]).length).instOuter (E.ctorIndices ++ [ctorApp S params E]) =
      body.instOuter (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) := by
    rw [show (S.indices ++ [majorTy S params E]).length = (E.ctorIndices ++ [ctorApp S params E]).length by
        simp [W.ctorIndices_length],
      liftN_instOuter_params (by have := hBcl; simpa [W.ctorIndices_length] using this),
      ← List.append_assoc]
    rfl
  rw [hR] at hbeta
  have hb : env.HasType U (params ++ S.fields).reverse (branch)
      (VExpr.mkApps ((motiveOf S params E body).liftN S.fields.length)
        (E.ctorIndices ++ [ctorApp S params E])) := by
    have h := IsDefEqU.defeqDF henv hΔb (IsDefEqU.symm hbeta) hbr0
    rw [show motiveOf S params E body = VExpr.wrapLams (S.indices ++ [majorTy S params E])
        body from rfl, liftN_wrapLams]
    exact h
  -- the eliminator application has the motive's body as its type
  have helim := W.elim _ _ hmot hb
  have hΔg' : OnCtx (majorTy S params E :: (params ++ S.indices).reverse) (env.IsType U) := by
    simpa [List.reverse_append] using hΔg
  have hres := HasType.projectionMotive_result henv hΔg'
    (domains := S.indices ++ [majorTy S params E])
    (body := body)
    (by simpa [motiveOf] using helim)
  unfold valueOf typeOf
  apply HasType.wrapLams_of (by simpa using hΔg)
  simpa [List.reverse_append, List.append_assoc, motiveOf] using hres

end Lean4Lean.PropElim
