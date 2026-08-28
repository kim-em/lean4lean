import Lean4Lean.Verify.TypeChecker.WHNF

namespace Lean4Lean

open Lean hiding Environment Exception

namespace TypeChecker

/-- Two expressions agree after simultaneously closing two ordered lists of
free variables.  This is the concrete alpha relation used by the executable
checker: it does not choose a global renaming and is insensitive to unrelated
locals in either ambient context. -/
def ExprAlphaUnder (left right : List FVarId)
    (e₁ e₂ : Expr) : Prop :=
  e₁.abstractList left = e₂.abstractList right

theorem ExprAlphaUnder.refl (e : Expr) (binders : List FVarId) :
    ExprAlphaUnder binders binders e e := rfl

theorem ExprAlphaUnder.symm
    (H : ExprAlphaUnder left right e₁ e₂) :
    ExprAlphaUnder right left e₂ e₁ := Eq.symm H

theorem ExprAlphaUnder.trans
    (H₁₂ : ExprAlphaUnder left middle e₁ e₂)
    (H₂₃ : ExprAlphaUnder middle right e₂ e₃) :
    ExprAlphaUnder left right e₁ e₃ := Eq.trans H₁₂ H₂₃

private theorem Expr.abstractList_isForall_alpha
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).isForall = e.isForall := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Expr.abstractList]
      rw [ih]
      cases e <;> simp only [Expr.abstract1, Expr.isForall]
      all_goals try rfl
      rename_i id
      by_cases h : (fv == id) = true <;> simp [h, Expr.isForall]

/-- Simultaneous closure cannot change whether an expression exposes a
forall, so alpha-aligned expressions agree on the branch inspected by
`isRecArg`. -/
theorem ExprAlphaUnder.isForall_eq
    (H : ExprAlphaUnder left right leftExpr rightExpr) :
    leftExpr.isForall = rightExpr.isForall := by
  have hclosed := congrArg Expr.isForall H
  simpa only [Expr.abstractList_isForall_alpha] using hclosed

/-- Simultaneous closure commutes with the forall constructor.  This generic
expression fact is kept here because the alpha-locality development must not
depend on the inductive-recursors telescope modules. -/
theorem Expr.abstractList_forallE_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.forallE name domain body bi).abstractList fvars k =
      .forallE name (domain.abstractList fvars k)
        (body.abstractList fvars (k + 1)) bi := by
  induction fvars generalizing domain body k with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih (domain := domain.abstract1 fv k)
        (body := body.abstract1 fv (k + 1)) (k := k)

/-- Closing a free variable after lifting below `d` binders is the same as
closing it outside those binders and lifting the resulting loose variable.
This is the value-side algebra needed by substitution under binders. -/
theorem Expr.abstract1_liftLooseBVars_alpha
    (value : Expr) (fv : FVarId) (k d : Nat) :
    (value.liftLooseBVars' k d).abstract1 fv (k + d) =
      (value.abstract1 fv k).liftLooseBVars' k d := by
  induction value generalizing k d <;>
    grind [Expr.abstract1, Expr.liftLooseBVars']

/-- Abstracting a free variable commutes with substituting a bound variable.
This is the single-binder algebra behind alpha-equivariance of `let` beta
reduction. -/
theorem Expr.abstract1_instantiate1'_alpha
    (body value : Expr) (fv : FVarId) (d : Nat) :
    (body.instantiate1' value d).abstract1 fv d =
      (body.abstract1 fv (d + 1)).instantiate1'
        (value.abstract1 fv 0) d := by
  induction body generalizing d with
  | bvar index =>
      by_cases hbelow : index < d
      · have hbelowSucc : index < d + 1 := by omega
        simp [Expr.instantiate1', Expr.abstract1, hbelow, hbelowSucc]
      by_cases heq : index = d
      · subst index
        simpa [Expr.instantiate1', Expr.abstract1] using
          Expr.abstract1_liftLooseBVars_alpha value fv 0 d
      · have habove : d < index := by omega
        have hnotBelowSucc : ¬index < d + 1 := by omega
        have hsubNotBelow : ¬index - 1 < d := by omega
        have hplusNotBelow : ¬index + 1 < d := by omega
        have hplusNe : index + 1 ≠ d := by omega
        simp [Expr.instantiate1', Expr.abstract1, hbelow, heq,
          hnotBelowSucc, hsubNotBelow, hplusNotBelow, hplusNe,
          Nat.sub_add_cancel (by omega : 1 ≤ index)]
  | fvar id =>
      by_cases h : (fv == id) = true
      · simp [Expr.instantiate1', Expr.abstract1, h]
      · simp [Expr.instantiate1', Expr.abstract1, h]
  | mvar | sort | const | lit => rfl
  | app fn arg ihFn ihArg =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihFn, ihArg]
  | lam name domain body bi ihDomain ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihDomain]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihBody (d + 1)
  | forallE name domain body bi ihDomain ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihDomain]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihBody (d + 1)
  | letE name type value body nondep ihType ihValue ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihType, ihValue]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihBody (d + 1)
  | mdata data body ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihBody]
  | proj name index body ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihBody]

/-- Simultaneously closing an ordered free-variable spine commutes with the
outer substitution performed by `let` beta reduction. -/
theorem Expr.abstractList_instantiate1_alpha
    (body value : Expr) (fvars : List FVarId) :
    (body.instantiate1 value).abstractList fvars =
      (body.abstractList fvars 1).instantiate1
        (value.abstractList fvars) := by
  rw [Expr.instantiate1_eq, Expr.instantiate1_eq]
  induction fvars generalizing body value with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList]
      rw [Expr.abstract1_instantiate1'_alpha body value fv 0]
      exact ih (body.abstract1 fv 1) (value.abstract1 fv 0)

/-- Simultaneous closure commutes with the `let` constructor. -/
theorem Expr.abstractList_letE_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.letE name type value body nondep).abstractList fvars k =
      .letE name (type.abstractList fvars k)
        (value.abstractList fvars k)
        (body.abstractList fvars (k + 1)) nondep := by
  induction fvars generalizing type value body k with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih (type := type.abstract1 fv k)
        (value := value.abstract1 fv k)
        (body := body.abstract1 fv (k + 1)) (k := k)

/-- Alpha-aligned `let` expressions have alpha-aligned pure beta reducts.
This isolates the cache-independent reduction step from recursive WHNF. -/
theorem ExprAlphaUnder.let_beta
    (H : ExprAlphaUnder left right
      (.letE leftName leftType leftValue leftBody leftNondep)
      (.letE rightName rightType rightValue rightBody rightNondep)) :
    ExprAlphaUnder left right
      (leftBody.instantiate1 leftValue)
      (rightBody.instantiate1 rightValue) := by
  have Hclosed :
      Expr.letE leftName (leftType.abstractList left)
          (leftValue.abstractList left) (leftBody.abstractList left 1)
          leftNondep =
        Expr.letE rightName (rightType.abstractList right)
          (rightValue.abstractList right) (rightBody.abstractList right 1)
          rightNondep := by
    simpa only [ExprAlphaUnder, Expr.abstractList_letE_alpha,
      Nat.zero_add] using H
  injection Hclosed with _ _ Hvalue Hbody _
  unfold ExprAlphaUnder
  rw [Expr.abstractList_instantiate1_alpha,
    Expr.abstractList_instantiate1_alpha, Hvalue, Hbody]

/-- Simultaneous closure commutes with application. -/
theorem Expr.abstractList_app_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.app fn arg).abstractList fvars k =
      .app (fn.abstractList fvars k) (arg.abstractList fvars k) := by
  induction fvars generalizing fn arg k with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih (fn := fn.abstract1 fv k) (arg := arg.abstract1 fv k)
        (k := k)

/-- Simultaneous closure commutes with lambda abstraction. -/
theorem Expr.abstractList_lam_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.lam name domain body bi).abstractList fvars k =
      .lam name (domain.abstractList fvars k)
        (body.abstractList fvars (k + 1)) bi := by
  induction fvars generalizing domain body k with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih (domain := domain.abstract1 fv k)
        (body := body.abstract1 fv (k + 1)) (k := k)

/-- Alpha equality of applications is pointwise. -/
theorem ExprAlphaUnder.app_parts
    (H : ExprAlphaUnder left right
      (.app leftFn leftArg) (.app rightFn rightArg)) :
    ExprAlphaUnder left right leftFn rightFn ∧
      ExprAlphaUnder left right leftArg rightArg := by
  have Hclosed :
      Expr.app (leftFn.abstractList left) (leftArg.abstractList left) =
        Expr.app (rightFn.abstractList right) (rightArg.abstractList right) := by
    simpa only [ExprAlphaUnder, Expr.abstractList_app_alpha] using H
  injection Hclosed with Hfn Harg
  exact ⟨Hfn, Harg⟩

/-- Alpha equality is preserved by applying one pair of alpha-equal
arguments.  This is the basic congruence used when WHNF rebuilds an
application after reducing its head. -/
theorem ExprAlphaUnder.app
    (Hfn : ExprAlphaUnder left right leftFn rightFn)
    (Harg : ExprAlphaUnder left right leftArg rightArg) :
    ExprAlphaUnder left right
      (.app leftFn leftArg) (.app rightFn rightArg) := by
  unfold ExprAlphaUnder at Hfn Harg ⊢
  simp only [Expr.abstractList_app_alpha]
  rw [Hfn, Harg]

/-- Pointwise alpha equality of argument lists is preserved by the
left-associated application spine used by delta unfolding and WHNF head
rebuilding. -/
theorem ExprAlphaUnder.mkAppList
    (Hfn : ExprAlphaUnder left right leftFn rightFn)
    (Hargs : List.Forall₂
      (ExprAlphaUnder left right) leftArgs rightArgs) :
    ExprAlphaUnder left right
      (leftFn.mkAppList leftArgs) (rightFn.mkAppList rightArgs) := by
  induction Hargs generalizing leftFn rightFn with
  | nil => exact Hfn
  | cons Harg _ ih =>
      simp only [Expr.mkAppList]
      exact ih (Hfn.app Harg)

/-- Simultaneous closure commutes with metadata syntax. -/
theorem Expr.abstractList_mdata_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.mdata data body).abstractList fvars k =
      .mdata data (body.abstractList fvars k) := by
  induction fvars generalizing body k with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih (body := body.abstract1 fv k) (k := k)

/-- Alpha equality of metadata wrappers relates their bodies.  Metadata is
erased by WHNF, but equality after closing also shows that both runs erase
the same wrapper payload. -/
theorem ExprAlphaUnder.mdata_parts
    (H : ExprAlphaUnder left right
      (.mdata leftData leftBody) (.mdata rightData rightBody)) :
    leftData = rightData ∧
      ExprAlphaUnder left right leftBody rightBody := by
  have Hclosed :
      Expr.mdata leftData (leftBody.abstractList left) =
        Expr.mdata rightData (rightBody.abstractList right) := by
    simpa only [ExprAlphaUnder, Expr.abstractList_mdata_alpha] using H
  injection Hclosed with Hdata Hbody
  exact ⟨Hdata, Hbody⟩

/-- Removing paired metadata wrappers, as the first branch of `whnf'` does,
preserves alpha equality. -/
theorem ExprAlphaUnder.mdata_body
    (H : ExprAlphaUnder left right
      (.mdata leftData leftBody) (.mdata rightData rightBody)) :
    ExprAlphaUnder left right leftBody rightBody :=
  H.mdata_parts.2

/-- One head beta step of alpha-aligned applications is alpha-aligned.  This
is the cache-independent reducible-application case consumed by recursive
WHNF after it exposes paired lambdas. -/
theorem ExprAlphaUnder.app_beta
    (H : ExprAlphaUnder left right
      (.app (.lam leftName leftType leftBody leftBi) leftArg)
      (.app (.lam rightName rightType rightBody rightBi) rightArg)) :
    ExprAlphaUnder left right
      (leftBody.instantiate1 leftArg)
      (rightBody.instantiate1 rightArg) := by
  rcases H.app_parts with ⟨Hfn, Harg⟩
  have Hclosed :
      Expr.lam leftName (leftType.abstractList left)
          (leftBody.abstractList left 1) leftBi =
        Expr.lam rightName (rightType.abstractList right)
          (rightBody.abstractList right 1) rightBi := by
    simpa only [ExprAlphaUnder, Expr.abstractList_lam_alpha,
      Nat.zero_add] using Hfn
  injection Hclosed with _ _ Hbody _
  unfold ExprAlphaUnder at Harg ⊢
  rw [Expr.abstractList_instantiate1_alpha,
    Expr.abstractList_instantiate1_alpha, Harg, Hbody]

/-- Simultaneous closure leaves constants unchanged. -/
theorem Expr.abstractList_const_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.const name levels).abstractList fvars k = .const name levels := by
  induction fvars with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih

/-- Constants related by simultaneous closure are literally the same
constant, including their universe arguments. -/
theorem ExprAlphaUnder.const_eq
    (H : ExprAlphaUnder left right
      (.const leftName leftLevels) (.const rightName rightLevels)) :
    leftName = rightName ∧ leftLevels = rightLevels := by
  have Hclosed : Expr.const leftName leftLevels =
      Expr.const rightName rightLevels := by
    simpa only [ExprAlphaUnder, Expr.abstractList_const_alpha] using H
  injection Hclosed with Hname Hlevels
  exact ⟨Hname, Hlevels⟩

/-- Simultaneous closure commutes with projection syntax. -/
theorem Expr.abstractList_proj_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.proj name index struct).abstractList fvars k =
      .proj name index (struct.abstractList fvars k) := by
  induction fvars generalizing struct k with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih (struct := struct.abstract1 fv k) (k := k)

/-- Alpha equality of projections fixes the projection metadata and relates
the two structure operands. -/
theorem ExprAlphaUnder.proj_parts
    (H : ExprAlphaUnder left right
      (.proj leftName leftIndex leftStruct)
      (.proj rightName rightIndex rightStruct)) :
    leftName = rightName ∧ leftIndex = rightIndex ∧
      ExprAlphaUnder left right leftStruct rightStruct := by
  have Hclosed :
      Expr.proj leftName leftIndex (leftStruct.abstractList left) =
        Expr.proj rightName rightIndex (rightStruct.abstractList right) := by
    simpa only [ExprAlphaUnder, Expr.abstractList_proj_alpha] using H
  injection Hclosed with Hname Hindex Hstruct
  exact ⟨Hname, Hindex, Hstruct⟩

/-- Alpha-equality of exposed foralls supplies exactly the two facts consumed
by one `loopUArgs` step: aligned declaration domains, and aligned bodies after
opening the bound variable with two fresh local constants. -/
theorem ExprAlphaUnder.forall_open
    (H : ExprAlphaUnder left right
      (.forallE leftName leftDomain leftBody leftBi)
      (.forallE rightName rightDomain rightBody rightBi))
    (hleftFv : leftFv ∉ left)
    (hrightFv : rightFv ∉ right)
    (hleftBody : leftBody.FVarsIn (fun fv => fv ≠ leftFv))
    (hrightBody : rightBody.FVarsIn (fun fv => fv ≠ rightFv)) :
    ExprAlphaUnder left right leftDomain rightDomain ∧
      ExprAlphaUnder (left ++ [leftFv]) (right ++ [rightFv])
        (leftBody.instantiate1 (.fvar leftFv))
        (rightBody.instantiate1 (.fvar rightFv)) := by
  have Hclosed :
      Expr.forallE leftName (leftDomain.abstractList left)
          (leftBody.abstractList left 1) leftBi =
        Expr.forallE rightName (rightDomain.abstractList right)
          (rightBody.abstractList right 1) rightBi := by
    simpa only [ExprAlphaUnder, Expr.abstractList_forallE_alpha,
      Nat.zero_add] using H
  injection Hclosed with _ Hdomain Hbody _
  constructor
  · exact Hdomain
  · unfold ExprAlphaUnder
    calc
      (leftBody.instantiate1 (.fvar leftFv)).abstractList
          (left ++ [leftFv]) = leftBody.abstractList left 1 := by
        rw [Expr.abstractList_append]
        simp only [Expr.abstractList]
        rw [Expr.abstract1_abstractList hleftFv]
        rw [Expr.instantiate1_eq, hleftBody.abstract_instantiate1]
      _ = rightBody.abstractList right 1 := Hbody
      _ = (rightBody.instantiate1 (.fvar rightFv)).abstractList
          (right ++ [rightFv]) := by
        rw [Expr.abstractList_append]
        simp only [Expr.abstractList]
        rw [Expr.abstract1_abstractList hrightFv]
        rw [Expr.instantiate1_eq, hrightBody.abstract_instantiate1]

/-- The domains of two alpha-aligned exposed foralls are alpha-aligned
without any freshness premise on their bodies. -/
theorem ExprAlphaUnder.forall_domain
    (H : ExprAlphaUnder left right
      (.forallE leftName leftDomain leftBody leftBi)
      (.forallE rightName rightDomain rightBody rightBi)) :
    ExprAlphaUnder left right leftDomain rightDomain := by
  have Hclosed :
      Expr.forallE leftName (leftDomain.abstractList left)
          (leftBody.abstractList left 1) leftBi =
        Expr.forallE rightName (rightDomain.abstractList right)
          (rightBody.abstractList right 1) rightBi := by
    simpa only [ExprAlphaUnder, Expr.abstractList_forallE_alpha,
      Nat.zero_add] using H
  injection Hclosed

/-- Ordered local declarations corresponding under simultaneous closure.
At ordinal `i`, each declaration type is closed only over the preceding
binders.  Later and unrelated ambient locals are intentionally unconstrained;
the locality theorem for a checker operation must separately show that its
input and every declaration it follows use only this aligned spine (plus any
literally shared outer free variables). -/
structure LocalContext.OrderedBinderRenaming
    (leftCtx rightCtx : LocalContext)
    (left right : List FVarId) : Prop where
  length_eq : left.length = right.length
  left_nodup : left.Nodup
  right_nodup : right.Nodup
  declarations : ∀ i (hiLeft : i < left.length)
      (hiRight : i < right.length),
    ∃ leftIndex leftName leftType leftBi leftKind,
      leftCtx.find? (left[i]'hiLeft) =
        some (.cdecl leftIndex (left[i]'hiLeft) leftName leftType leftBi
          leftKind) ∧
    ∃ rightIndex rightName rightType rightBi rightKind,
      rightCtx.find? (right[i]'hiRight) =
        some (.cdecl rightIndex (right[i]'hiRight) rightName rightType rightBi
          rightKind) ∧
      ExprAlphaUnder (left.take i) (right.take i) leftType rightType

theorem LocalContext.OrderedBinderRenaming.right_length
    (H : LocalContext.OrderedBinderRenaming leftCtx rightCtx left right) :
    right.length = left.length := H.length_eq.symm

/-- Pointwise form of an ordered binder renaming, exposing the exact local
lookups together with the alpha-equal declaration domains consumed by
`inferType` on the paired free variables. -/
theorem LocalContext.OrderedBinderRenaming.declarationAt
    (H : LocalContext.OrderedBinderRenaming leftCtx rightCtx left right)
    (i : Nat) (hi : i < left.length) :
    let hiRight : i < right.length := H.length_eq ▸ hi
    ∃ leftIndex leftName leftType leftBi leftKind,
      leftCtx.find? (left[i]'hi) =
        some (.cdecl leftIndex (left[i]'hi) leftName leftType leftBi leftKind) ∧
    ∃ rightIndex rightName rightType rightBi rightKind,
      rightCtx.find? (right[i]'hiRight) =
        some (.cdecl rightIndex (right[i]'hiRight) rightName rightType rightBi
          rightKind) ∧
      ExprAlphaUnder (left.take i) (right.take i) leftType rightType := by
  exact H.declarations i hi (H.length_eq ▸ hi)

/-- A free variable absent from the left local-context map is absent from the
left generated binder spine. -/
theorem LocalContext.OrderedBinderRenaming.left_not_mem_of_find?_eq_none
    (H : LocalContext.OrderedBinderRenaming leftCtx rightCtx left right)
    (hfind : leftCtx.find? fv = none) : fv ∉ left := by
  intro hmem
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  rcases H.declarationAt i hi with
    ⟨index, name, type, bi, kind, hlookup, _⟩
  have heq : left[i]'hi = fv := hget
  rw [heq, hfind] at hlookup
  cases hlookup

/-- A free variable absent from the right local-context map is absent from
the right generated binder spine. -/
theorem LocalContext.OrderedBinderRenaming.right_not_mem_of_find?_eq_none
    (H : LocalContext.OrderedBinderRenaming leftCtx rightCtx left right)
    (hfind : rightCtx.find? fv = none) : fv ∉ right := by
  intro hmem
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hiLeft : i < left.length := by simpa [H.length_eq] using hi
  rcases H.declarationAt i hiLeft with
    ⟨_, _, _, _, _, _, index, name, type, bi, kind, hlookup, _⟩
  have heq : right[i]'(H.length_eq ▸ hiLeft) = fv := by
    simpa [hget]
  rw [heq, hfind] at hlookup
  cases hlookup

/-- The empty generated spine is aligned in arbitrary ambient contexts. -/
theorem LocalContext.OrderedBinderRenaming.empty
    (leftCtx rightCtx : LocalContext) :
    LocalContext.OrderedBinderRenaming leftCtx rightCtx [] [] where
  length_eq := rfl
  left_nodup := List.nodup_nil
  right_nodup := List.nodup_nil
  declarations i hi := by simp at hi

/-- Extend an ordered binder renaming by one paired constant declaration.
The freshness premises are stated using the exact local-context lookups made
by `withLocalDecl`; no global choice of free-variable renaming is needed. -/
theorem LocalContext.OrderedBinderRenaming.push
    (H : LocalContext.OrderedBinderRenaming leftCtx rightCtx left right)
    (hleftWF : leftCtx.WF) (hrightWF : rightCtx.WF)
    (hleftFresh : leftCtx.find? leftFv = none)
    (hrightFresh : rightCtx.find? rightFv = none)
    (Htype : ExprAlphaUnder left right leftType rightType)
    (leftName rightName : Name) (leftBi rightBi : BinderInfo)
    (leftKind rightKind : LocalDeclKind := .default) :
    LocalContext.OrderedBinderRenaming
      (leftCtx.mkLocalDecl leftFv leftName leftType leftBi leftKind)
      (rightCtx.mkLocalDecl rightFv rightName rightType rightBi rightKind)
      (left ++ [leftFv]) (right ++ [rightFv]) := by
  have hleftNotMem : leftFv ∉ left := by
    intro hmem
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    rcases H.declarationAt i hi with
      ⟨leftIndex, oldLeftName, oldLeftType, oldLeftBi, oldLeftKind,
        hleft, _⟩
    have : left[i]'hi = leftFv := by simpa [hget]
    rw [this, hleftFresh] at hleft
    cases hleft
  have hrightNotMem : rightFv ∉ right := by
    intro hmem
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    have hiLeft : i < left.length := by simpa [H.length_eq] using hi
    rcases H.declarationAt i hiLeft with
      ⟨_, _, _, _, _, _, rightIndex, oldRightName, oldRightType,
        oldRightBi, oldRightKind, hright, _⟩
    have : right[i]'(H.length_eq ▸ hiLeft) = rightFv := by
      simpa [hget]
    rw [this, hrightFresh] at hright
    cases hright
  refine {
    length_eq := by simp [H.length_eq]
    left_nodup := by
      rw [List.nodup_append]
      refine ⟨H.left_nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact fun h => hleftNotMem (h ▸ ha)
    right_nodup := by
      rw [List.nodup_append]
      refine ⟨H.right_nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact fun h => hrightNotMem (h ▸ ha)
    declarations := ?_ }
  intro i hiLeft hiRight
  by_cases hiOld : i < left.length
  · have hiRightOld : i < right.length := by simpa [H.length_eq] using hiOld
    rcases H.declarations i hiOld hiRightOld with
      ⟨leftIndex, oldLeftName, oldLeftType, oldLeftBi, oldLeftKind,
        hleft, rightIndex, oldRightName, oldRightType, oldRightBi,
        oldRightKind, hright, htypes⟩
    refine ⟨leftIndex, oldLeftName, oldLeftType, oldLeftBi, oldLeftKind,
      ?_, rightIndex, oldRightName, oldRightType, oldRightBi, oldRightKind,
      ?_, ?_⟩
    · simp only [List.getElem_append_left hiOld]
      change (leftCtx.fvarIdToDecl.insert leftFv
          (.cdecl leftCtx.decls.size leftFv leftName leftType leftBi
            leftKind)).find? left[i] = _
      rw [hleftWF.map_wf.find?_insert, if_neg]
      · exact hleft
      · simp only [beq_iff_eq]
        intro heq
        rw [← heq, hleftFresh] at hleft
        cases hleft
    · simp only [List.getElem_append_left hiRightOld]
      change (rightCtx.fvarIdToDecl.insert rightFv
          (.cdecl rightCtx.decls.size rightFv rightName rightType rightBi
            rightKind)).find? right[i] = _
      rw [hrightWF.map_wf.find?_insert, if_neg]
      · exact hright
      · simp only [beq_iff_eq]
        intro heq
        rw [← heq, hrightFresh] at hright
        cases hright
    · simpa [List.take_append_of_le_length (Nat.le_of_lt hiOld),
        List.take_append_of_le_length (Nat.le_of_lt hiRightOld)] using htypes
  · have hiEq : i = left.length := by
      simp only [List.length_append, List.length_singleton] at hiLeft
      omega
    subst i
    have hrightLength : right.length = left.length := H.length_eq.symm
    have hleftElem :
        (left ++ [leftFv])[left.length]'hiLeft = leftFv := by
      simp
    have hrightElem :
        (right ++ [rightFv])[left.length]'hiRight = rightFv := by
      simpa [hrightLength]
    refine ⟨leftCtx.decls.size, leftName, leftType, leftBi, leftKind,
      ?_, rightCtx.decls.size, rightName, rightType, rightBi, rightKind,
      ?_, ?_⟩
    · rw [hleftElem]
      change (leftCtx.fvarIdToDecl.insert leftFv
          (.cdecl leftCtx.decls.size leftFv leftName leftType leftBi
            leftKind)).find? leftFv = _
      rw [hleftWF.map_wf.find?_insert, if_pos (by simp)]
    · rw [hrightElem]
      change (rightCtx.fvarIdToDecl.insert rightFv
          (.cdecl rightCtx.decls.size rightFv rightName rightType rightBi
            rightKind)).find? rightFv = _
      rw [hrightWF.map_wf.find?_insert, if_pos (by simp)]
    · simpa [H.length_eq] using Htype

/-- The primitive free-variable inference operation respects an aligned
binder ordinal.  This is the first executable locality step used by WHNF:
the result is obtained from the two exact local-context lookups, with no
appeal to semantic typing or uniqueness. -/
theorem LocalContext.OrderedBinderRenaming.inferFVarAt
    (H : LocalContext.OrderedBinderRenaming
      leftContext.lctx rightContext.lctx left right)
    (i : Nat) (hi : i < left.length) :
    let hiRight : i < right.length := H.length_eq ▸ hi
    ∃ leftType rightType,
      Inner.inferFVar leftContext (left[i]'hi) = .ok leftType ∧
      Inner.inferFVar rightContext (right[i]'hiRight) = .ok rightType ∧
      ExprAlphaUnder (left.take i) (right.take i) leftType rightType := by
  rcases H.declarationAt i hi with
    ⟨leftIndex, leftName, leftType, leftBi, leftKind, hleft,
      rightIndex, rightName, rightType, rightBi, rightKind, hright,
      htypes⟩
  refine ⟨leftType, rightType, ?_, ?_, htypes⟩
  · simp only [Inner.inferFVar, hleft, LocalDecl.type]
    rfl
  · simp only [Inner.inferFVar, hright, LocalDecl.type]
    rfl

/-- Ambient checker contexts for an ordered binder renaming.  Outer free
variables satisfying `shared` are literal shared declarations; generated
binders may differ and are compared by `binders`.  The checker configuration
fields listed here are precisely those read by `inferType` and WHNF. -/
structure Context.OrderedBinderRenaming
    (shared : FVarId → Prop) (left right : List FVarId)
    (leftContext rightContext : Context) : Prop where
  env_eq : leftContext.env = rightContext.env
  safety_eq : leftContext.safety = rightContext.safety
  eagerReduce_eq : leftContext.eagerReduce = rightContext.eagerReduce
  lparams_eq : leftContext.lparams = rightContext.lparams
  fuel_eq : leftContext.fuel = rightContext.fuel
  binders : LocalContext.OrderedBinderRenaming
    leftContext.lctx rightContext.lctx left right
  left_lctx_wf : leftContext.lctx.WF
  right_lctx_wf : rightContext.lctx.WF
  shared_declarations : ∀ fv, shared fv →
    leftContext.lctx.find? fv = rightContext.lctx.find? fv
  shared_fresh : ∀ fv, shared fv → fv ∉ left ∧ fv ∉ right
  left_only_cdecls : ∀ decl ∈ leftContext.lctx.toList,
    ∃ index fv name type bi kind,
      decl = .cdecl index fv name type bi kind
  right_only_cdecls : ∀ decl ∈ rightContext.lctx.toList,
    ∃ index fv name type bi kind,
      decl = .cdecl index fv name type bi kind

/-- In alpha-aligned checker contexts, the executable delta classifier makes
the same decision on alpha-aligned constant heads. -/
theorem Context.OrderedBinderRenaming.isDelta_const_eq
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hinput : ExprAlphaUnder left right
      (.const leftName leftLevels) (.const rightName rightLevels)) :
    Inner.isDelta leftContext.env (.const leftName leftLevels) =
      Inner.isDelta rightContext.env (.const rightName rightLevels) := by
  rcases Hinput.const_eq with ⟨rfl, rfl⟩
  rw [H.env_eq]

/-- Extend two alpha-aligned checker contexts by the paired declarations
created by one `loopUArgs` forall step.  The shared outer region must exclude
the two newly generated identifiers; all other shared lookups are preserved
literally. -/
theorem Context.OrderedBinderRenaming.push
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (leftFv rightFv : FVarId)
    (hleftFresh : leftContext.lctx.find? leftFv = none)
    (hrightFresh : rightContext.lctx.find? rightFv = none)
    (hsharedFresh : ∀ fv, shared fv → fv ≠ leftFv ∧ fv ≠ rightFv)
    (leftName rightName : Name) (leftType rightType : Expr)
    (leftBi rightBi : BinderInfo)
    (Htype : ExprAlphaUnder left right leftType rightType) :
    Context.OrderedBinderRenaming shared
      (left ++ [leftFv]) (right ++ [rightFv])
      { leftContext with
        lctx := leftContext.lctx.mkLocalDecl leftFv leftName leftType leftBi }
      { rightContext with
        lctx := rightContext.lctx.mkLocalDecl rightFv rightName rightType
          rightBi } where
  env_eq := H.env_eq
  safety_eq := H.safety_eq
  eagerReduce_eq := H.eagerReduce_eq
  lparams_eq := H.lparams_eq
  fuel_eq := H.fuel_eq
  binders := H.binders.push H.left_lctx_wf H.right_lctx_wf
    hleftFresh hrightFresh Htype leftName rightName leftBi rightBi
  left_lctx_wf := H.left_lctx_wf.mkLocalDecl hleftFresh
  right_lctx_wf := H.right_lctx_wf.mkLocalDecl hrightFresh
  shared_declarations fv hfv := by
    change (leftContext.lctx.fvarIdToDecl.insert leftFv
        (.cdecl leftContext.lctx.decls.size leftFv leftName leftType leftBi
          .default)).find? fv =
      (rightContext.lctx.fvarIdToDecl.insert rightFv
        (.cdecl rightContext.lctx.decls.size rightFv rightName rightType
          rightBi .default)).find? fv
    rw [H.left_lctx_wf.map_wf.find?_insert,
      H.right_lctx_wf.map_wf.find?_insert,
      if_neg (by simpa only [beq_iff_eq] using (hsharedFresh fv hfv).1.symm),
      if_neg (by simpa only [beq_iff_eq] using (hsharedFresh fv hfv).2.symm)]
    exact H.shared_declarations fv hfv
  shared_fresh fv hfv := by
    rcases H.shared_fresh fv hfv with ⟨hleft, hright⟩
    rcases hsharedFresh fv hfv with ⟨hneLeft, hneRight⟩
    constructor
    · simpa [hneLeft] using hleft
    · simpa [hneRight] using hright
  left_only_cdecls decl hdecl := by
    simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hdecl
    rcases hdecl with rfl | hdecl
    · exact ⟨leftContext.lctx.decls.size, leftFv, leftName, leftType,
        leftBi, .default, rfl⟩
    · exact H.left_only_cdecls decl hdecl
  right_only_cdecls decl hdecl := by
    simp only [LocalContext.mkLocalDecl_toList, List.mem_cons] at hdecl
    rcases hdecl with rfl | hdecl
    · exact ⟨rightContext.lctx.decls.size, rightFv, rightName, rightType,
        rightBi, .default, rfl⟩
    · exact H.right_only_cdecls decl hdecl

/-- An all-`cdecl` local context never exposes a reducible let declaration
through lookup. -/
theorem LocalContext.find?_ne_ldecl_of_onlyCDecls
    (lctx : LocalContext)
    (Hwf : lctx.WF)
    (Hcdecls : ∀ decl ∈ lctx.toList,
      ∃ (index : Nat) (fv : FVarId) (name : Name) (type : Expr)
        (bi : BinderInfo) (kind : LocalDeclKind),
        decl = LocalDecl.cdecl index fv name type bi kind)
    (fv : FVarId) :
    ∀ (index : Nat) (declFv : FVarId) (name : Name) (type value : Expr)
      (nonDep : Bool) (kind : LocalDeclKind),
      lctx.find? fv ≠
        some (LocalDecl.ldecl index declFv name type value nonDep kind) := by
  intro index declFv name type value nonDep kind hfind
  rw [Hwf.find?_eq_find?_toList] at hfind
  have hmember := List.mem_of_find?_eq_some hfind
  rcases Hcdecls _ hmember with
    ⟨cdeclIndex, cdeclFv, cdeclName, cdeclType, cdeclBi, cdeclKind,
      hcdecl⟩
  cases hcdecl

/-- Executable let-detection is false for every free variable in an
all-constant-declaration context. -/
theorem Inner.isLetFVar_eq_false_of_onlyCDecls
    (lctx : LocalContext) (Hwf : lctx.WF)
    (Hcdecls : ∀ decl ∈ lctx.toList,
      ∃ (index : Nat) (fv : FVarId) (name : Name) (type : Expr)
        (bi : BinderInfo) (kind : LocalDeclKind),
        decl = LocalDecl.cdecl index fv name type bi kind)
    (fv : FVarId) :
    Inner.isLetFVar lctx fv = false := by
  unfold Inner.isLetFVar
  cases hlookup : lctx.find? fv with
  | none => simp [hlookup]
  | some decl =>
      cases decl with
      | cdecl => simp [hlookup]
      | ldecl index declFv name type value nonDep kind =>
          exact False.elim <|
            LocalContext.find?_ne_ldecl_of_onlyCDecls lctx Hwf Hcdecls fv
              index declFv name type value nonDep kind hlookup

theorem Inner.getLCtx_run (methods : Methods) (context : Context)
    (state : State) :
    (getLCtx : RecM LocalContext) methods context state =
      .ok (context.lctx, state) := by
  rfl

theorem readContext_run (context : Context) (state : State) :
    (readThe Context : M Context) context state =
      .ok (context, state) := by
  rfl

/-- Public WHNF erases one metadata wrapper before doing any cache lookup or
context-sensitive work.  Exposing this exact equation lets the alpha proof
recurse on the strictly smaller wrapped expression. -/
theorem whnf_mdata_run_eq
    (context : Context) (state : State) (data : MData) (body : Expr) :
    whnf (.mdata data body) context state = whnf body context state := by
  unfold whnf RecM.run Inner.whnf
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind]
  rw [readContext_run]
  simp only [Except.bind]
  cases context.fuel.recDepth with
  | zero => rfl
  | succ depth =>
      simp only [Methods.withFuel]
      rfl

/-- Constant unfolding reads only the environment from its checker context.
With a common state (in particular the empty state used by
`TypeChecker.M.run`), equal environments give literally equal executions,
including the canonical unfold-cache update. -/
theorem Inner.unfoldDefinitionCore_eq_of_env_eq
    (henv : leftContext.env = rightContext.env)
    (methods : Methods) (state : State) (e : Expr) :
    Inner.unfoldDefinitionCore e methods leftContext state =
      Inner.unfoldDefinitionCore e methods rightContext state := by
  unfold Inner.unfoldDefinitionCore
  cases e <;> try rfl
  rename_i name levels
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind, getEnv, liftM, monadLift,
    MonadLiftT.monadLift, MonadLift.monadLift,
    instMonadLiftTOfMonadLift, instMonadLiftT, ReaderT.instMonadLift,
    StateT.instMonadLift, StateT.lift, ReaderT.read, MonadReader.read,
    instMonadReaderOfMonadReaderOf, readThe, MonadReaderOf.read,
    instMonadReaderOfReaderTOfMonad, StateT.get, StateT.modifyGet,
    _root_.modify, MonadState.get, MonadState.modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, getThe, modifyGetThe,
    instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
    instMonadStateOfStateTOfMonad, Pure.pure,
    Applicative.toPure, Monad.toApplicative, ReaderT.pure, StateT.pure,
    Except.instMonad, Except.pure, Except.bind]
  rw [henv]
  cases hdelta : Inner.isDelta rightContext.env (.const name levels) with
  | none =>
      simp [hdelta, pure, ReaderT.pure, StateT.pure, Except.pure]
  | some info =>
      simp only [hdelta]
      split
      · cases hcache : state.unfold[Expr.const name levels]? <;>
          simp [hcache, bind, pure, ReaderT.bind, ReaderT.pure,
            StateT.bind, StateT.get, StateT.modifyGet, StateT.pure,
            Except.bind, Except.pure]
      · simp [bind, pure, ReaderT.bind, ReaderT.pure, StateT.bind,
          StateT.get, StateT.modifyGet, StateT.pure, Except.bind,
          Except.pure]

/-- In an all-`cdecl` context the executable `whnfFVar` branch is literally
the identity, independently of the recursive methods supplied by the caller.
This removes the only local-declaration unfolding case from the WHNF alpha
proof used by inductive constructor fields. -/
theorem Inner.whnfFVar_eq_fvar_of_onlyCDecls
    (context : Context) (Hwf : context.lctx.WF)
    (Hcdecls : ∀ decl ∈ context.lctx.toList,
      ∃ (index : Nat) (fv : FVarId) (name : Name) (type : Expr)
        (bi : BinderInfo) (kind : LocalDeclKind),
        decl = LocalDecl.cdecl index fv name type bi kind)
    (methods : Methods) (state : State) (fv : FVarId)
    (cheapProj : Bool) :
    Inner.whnfFVar (.fvar fv) cheapProj methods context state =
      .ok ((.fvar fv), state) := by
  unfold Inner.whnfFVar
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind]
  rw [Inner.getLCtx_run]
  simp only [Bind.bind, Except.bind]
  cases hlookup : context.lctx.find? fv with
  | none =>
      simp [Expr.fvarId!, hlookup, Pure.pure, Applicative.toPure,
        Monad.toApplicative, ReaderT.instMonad, ReaderT.pure,
        StateT.instMonad, StateT.pure, Except.instMonad, Except.pure]
  | some decl =>
      cases decl with
      | cdecl =>
          simp [Expr.fvarId!, hlookup, Pure.pure, Applicative.toPure,
            Monad.toApplicative, ReaderT.instMonad, ReaderT.pure,
            StateT.instMonad, StateT.pure, Except.instMonad, Except.pure]
      | ldecl index declFv name type value nonDep kind =>
          exact False.elim <|
            LocalContext.find?_ne_ldecl_of_onlyCDecls context.lctx
              Hwf Hcdecls fv
              index declFv name type value nonDep kind hlookup

/-- The recursive WHNF implementation does not inspect the ambient context
when its input already exposes a forall.  This exact execution lemma is the
base case used while `loopUArgs` peels a higher-order recursive domain. -/
theorem Inner.whnf'_forall
    (methods : Methods) (context : Context) (state : State)
    (name : Name) (domain body : Expr) (bi : BinderInfo) :
    Inner.whnf' (.forallE name domain body bi) methods context state =
      .ok ((.forallE name domain body bi), state) := by
  unfold Inner.whnf'
  simp only [Pure.pure, Applicative.toPure, Monad.toApplicative,
    ReaderT.instMonad, ReaderT.pure, StateT.instMonad, StateT.pure,
    Except.instMonad, Except.pure]

/-- Source forms returned by public WHNF before consulting either the local
context or the reduction cache. -/
inductive Expr.WhnfImmediate : Expr → Prop
  | bvar : Expr.WhnfImmediate (.bvar index)
  | sort : Expr.WhnfImmediate (.sort level)
  | mvar (mvarId : MVarId) : Expr.WhnfImmediate (.mvar mvarId)
  | forallE : Expr.WhnfImmediate (.forallE name domain body bi)
  | lit : Expr.WhnfImmediate (.lit value)

theorem Inner.whnf'_immediate
    (H : Expr.WhnfImmediate e)
    (methods : Methods) (context : Context) (state : State) :
    Inner.whnf' e methods context state = .ok (e, state) := by
  cases H <;> rfl

/-- The recursive WHNF implementation also leaves a free variable unchanged
when the local context contains no let declarations. -/
theorem Inner.whnf'_fvar_of_onlyCDecls
    (methods : Methods) (context : Context) (state : State)
    (Hwf : context.lctx.WF)
    (Hcdecls : ∀ decl ∈ context.lctx.toList,
      ∃ (index : Nat) (fv : FVarId) (name : Name) (type : Expr)
        (bi : BinderInfo) (kind : LocalDeclKind),
        decl = LocalDecl.cdecl index fv name type bi kind)
    (fv : FVarId) :
    Inner.whnf' (.fvar fv) methods context state =
      .ok ((.fvar fv), state) := by
  unfold Inner.whnf'
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind]
  rw [Inner.getLCtx_run]
  simp only [Except.bind]
  rw [Inner.isLetFVar_eq_false_of_onlyCDecls context.lctx Hwf Hcdecls fv]
  simp [Pure.pure, Applicative.toPure, Monad.toApplicative,
    ReaderT.instMonad, ReaderT.pure, StateT.instMonad, StateT.pure,
    Except.instMonad, Except.pure]

/-- Any successful public WHNF run on an exposed forall returns that forall
unchanged (and does not mutate the checker state).  The zero-fuel method is
ruled out by success rather than imposed as an extra caller premise. -/
theorem whnf_forall_result_eq
    (context : Context) (state outState : State)
    (name : Name) (domain body result : Expr) (bi : BinderInfo)
    (Hrun : whnf (.forallE name domain body bi) context state =
      .ok (result, outState)) :
    result = .forallE name domain body bi ∧ outState = state := by
  unfold whnf RecM.run Inner.whnf at Hrun
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind] at Hrun
  rw [readContext_run] at Hrun
  simp only [Except.bind] at Hrun
  cases hdepth : context.fuel.recDepth with
  | zero =>
      rw [hdepth] at Hrun
      simp [Methods.withFuel, MonadExcept.throw, throwThe,
        MonadExceptOf.throw, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept,
        liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        Functor.map, Except.map] at Hrun
  | succ depth =>
      rw [hdepth] at Hrun
      simp only [Methods.withFuel] at Hrun
      rw [Inner.whnf'_forall] at Hrun
      have hpairs := (Except.ok.inj Hrun).symm
      exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- Every successful public WHNF run on an immediate source form returns it
unchanged and preserves the checker state. -/
theorem whnf_immediate_result_eq
    (H : Expr.WhnfImmediate e)
    (context : Context) (state outState : State) (result : Expr)
    (Hrun : whnf e context state = .ok (result, outState)) :
    result = e ∧ outState = state := by
  unfold whnf RecM.run Inner.whnf at Hrun
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind] at Hrun
  rw [readContext_run] at Hrun
  simp only [Except.bind] at Hrun
  cases hdepth : context.fuel.recDepth with
  | zero =>
      rw [hdepth] at Hrun
      simp [Methods.withFuel, MonadExcept.throw, throwThe,
        MonadExceptOf.throw, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept,
        liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        Functor.map, Except.map] at Hrun
  | succ depth =>
      rw [hdepth] at Hrun
      simp only [Methods.withFuel] at Hrun
      rw [Inner.whnf'_immediate H] at Hrun
      have hpairs := (Except.ok.inj Hrun).symm
      exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- Immediate WHNF respects any alpha relation on its two inputs. -/
theorem whnf_immediate_alpha
    (HleftImmediate : Expr.WhnfImmediate leftInput)
    (HrightImmediate : Expr.WhnfImmediate rightInput)
    (Hinput : ExprAlphaUnder leftBinders rightBinders
      leftInput rightInput)
    (leftContext rightContext : Context)
    (leftState leftOut rightState rightOut : State)
    (leftResult rightResult : Expr)
    (Hleft : whnf leftInput leftContext leftState =
      .ok (leftResult, leftOut))
    (Hright : whnf rightInput rightContext rightState =
      .ok (rightResult, rightOut)) :
    ExprAlphaUnder leftBinders rightBinders leftResult rightResult := by
  rcases whnf_immediate_result_eq HleftImmediate leftContext leftState
      leftOut leftResult Hleft with ⟨rfl, _⟩
  rcases whnf_immediate_result_eq HrightImmediate rightContext rightState
      rightOut rightResult Hright with ⟨rfl, _⟩
  exact Hinput

/-- Any successful public WHNF run on a free variable in an all-`cdecl`
context returns that variable unchanged and preserves the state. -/
theorem whnf_fvar_result_eq
    (context : Context) (state outState : State)
    (Hwf : context.lctx.WF)
    (Hcdecls : ∀ decl ∈ context.lctx.toList,
      ∃ (index : Nat) (fv : FVarId) (name : Name) (type : Expr)
        (bi : BinderInfo) (kind : LocalDeclKind),
        decl = LocalDecl.cdecl index fv name type bi kind)
    (fv : FVarId) (result : Expr)
    (Hrun : whnf (.fvar fv) context state = .ok (result, outState)) :
    result = .fvar fv ∧ outState = state := by
  unfold whnf RecM.run Inner.whnf at Hrun
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind] at Hrun
  rw [readContext_run] at Hrun
  simp only [Except.bind] at Hrun
  cases hdepth : context.fuel.recDepth with
  | zero =>
      rw [hdepth] at Hrun
      simp [Methods.withFuel, MonadExcept.throw, throwThe,
        MonadExceptOf.throw, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, liftM, monadLift,
        MonadLiftT.monadLift, MonadLift.monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        Functor.map, Except.map] at Hrun
  | succ depth =>
      rw [hdepth] at Hrun
      simp only [Methods.withFuel] at Hrun
      rw [Inner.whnf'_fvar_of_onlyCDecls _ context state Hwf Hcdecls fv]
        at Hrun
      have hpairs := (Except.ok.inj Hrun).symm
      exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- The exposed-forall branch of public WHNF is alpha-equivariant. -/
theorem whnf_forall_alpha
    (leftContext rightContext : Context)
    (leftState leftOut rightState rightOut : State)
    (leftBinders rightBinders : List FVarId)
    (leftName rightName : Name)
    (leftDomain leftBody rightDomain rightBody leftResult rightResult : Expr)
    (leftBi rightBi : BinderInfo)
    (Hinput : ExprAlphaUnder leftBinders rightBinders
      (.forallE leftName leftDomain leftBody leftBi)
      (.forallE rightName rightDomain rightBody rightBi))
    (Hleft : whnf (.forallE leftName leftDomain leftBody leftBi)
      leftContext leftState = .ok (leftResult, leftOut))
    (Hright : whnf (.forallE rightName rightDomain rightBody rightBi)
      rightContext rightState = .ok (rightResult, rightOut)) :
    ExprAlphaUnder leftBinders rightBinders leftResult rightResult := by
  rcases whnf_forall_result_eq leftContext leftState leftOut
    leftName leftDomain leftBody leftResult leftBi Hleft with
    ⟨rfl, _⟩
  rcases whnf_forall_result_eq rightContext rightState rightOut
    rightName rightDomain rightBody rightResult rightBi Hright with
    ⟨rfl, _⟩
  exact Hinput

/-- Primitive inference of a literally shared outer free variable is the
same in both contexts. -/
theorem Context.OrderedBinderRenaming.inferFVarShared
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (hfv : shared fv) :
    Inner.inferFVar leftContext fv = Inner.inferFVar rightContext fv := by
  simp only [Inner.inferFVar]
  rw [H.shared_declarations fv hfv]

/-- Primitive inference at a generated binder ordinal is alpha-compatible
under the full checker-context relation. -/
theorem Context.OrderedBinderRenaming.inferFVarAt
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (i : Nat) (hi : i < left.length) :
    let hiRight : i < right.length := H.binders.length_eq ▸ hi
    ∃ leftType rightType,
      Inner.inferFVar leftContext (left[i]'hi) = .ok leftType ∧
      Inner.inferFVar rightContext (right[i]'hiRight) = .ok rightType ∧
      ExprAlphaUnder (left.take i) (right.take i) leftType rightType :=
  H.binders.inferFVarAt i hi

/-- Closing more free variables shifts an already-bound variable above the
closure cutoff once per variable. -/
private theorem Expr.abstractList_bvar_ge_alpha
    (fvars : List FVarId) (k n : Nat) :
    (Expr.bvar (k + n)).abstractList fvars k =
      .bvar (k + n + fvars.length) := by
  induction fvars generalizing n with
  | nil => simp
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      rw [if_neg (by omega)]
      have hindex : k + n + 1 = k + (n + 1) := by omega
      rw [hindex, ih (n := n + 1)]
      congr 1
      simp only [List.length_cons]
      omega

/-- Closing the variable at an exact ordinal in a duplicate-free binder
spine depends only on that ordinal and the spine length. -/
private theorem Expr.abstractList_fvarAt_alpha
    (H : fvars.Nodup) (i : Nat) (hi : i < fvars.length) :
    (Expr.fvar fvars[i]).abstractList fvars k =
      .bvar (k + (fvars.length - 1 - i)) := by
  induction fvars generalizing i k with
  | nil => simp at hi
  | cons head tail ih =>
      simp only [List.nodup_cons] at H
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero, Expr.abstractList]
          rw [show (Expr.fvar head).abstract1 head k = .bvar k by
            simp [Expr.abstract1]]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Expr.abstractList_bvar_ge_alpha tail k 0
      | succ i =>
          have hiTail : i < tail.length := by simpa using hi
          have hne : head ≠ tail[i] := by
            intro heq
            exact H.1 (heq ▸ List.getElem_mem hiTail)
          simp only [List.getElem_cons_succ, Expr.abstractList]
          rw [show (Expr.fvar tail[i]).abstract1 head k =
              .fvar tail[i] by simp [Expr.abstract1, hne]]
          rw [ih H.2 i hiTail (k := k)]
          apply congrArg Expr.bvar
          simp only [List.length_cons]
          omega

/-- Closing a free variable disjoint from the generated binder spine leaves
it unchanged. -/
private theorem Expr.abstractList_fvar_fresh_alpha
    (H : fv ∉ fvars) :
    (Expr.fvar fv).abstractList fvars k = .fvar fv := by
  induction fvars with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at H
      simp only [Expr.abstractList]
      rw [show (Expr.fvar fv).abstract1 head k = .fvar fv by
        simp [Expr.abstract1, Ne.symm H.1]]
      exact ih H.2

/-- Closing free variables does not affect an already bound variable below
the closure depth. -/
private theorem Expr.abstractList_bvar_lt_alpha
    (fvars : List FVarId) (i k : Nat) (hi : i < k) :
    (Expr.bvar i).abstractList fvars k = .bvar i := by
  induction fvars with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1, if_pos hi]
      exact ih

/-- Closing a duplicate-free free-variable spine and reopening it with the
same identifiers is a left inverse on well-scoped expressions.  This makes
the canonical closed form injective on every concrete WHNF cache key used in
the paired runs. -/
theorem Expr.abstractList_instantiateRevList_eq_self
    (hnd : fvars.Nodup) (hclosed : Closed e k) :
    (e.abstractList fvars k).instantiateRevList
        (fvars.map Expr.fvar) k = e := by
  induction e generalizing k with
  | bvar i =>
      rw [Expr.abstractList_bvar_lt_alpha fvars i k hclosed]
      exact Expr.instantiateRevList_bvar_fvars_lt fvars i k hclosed
  | fvar fv =>
      by_cases hmem : fv ∈ fvars
      · obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
        have hselected := Expr.abstractList_fvarAt_alpha
          (fvars := fvars) hnd i hi (k := k)
        rw [hget] at hselected
        rw [hselected]
        have hrestore := Expr.instantiateRevList_bvar_fvars_getElem
          fvars i k hi
        rwa [hget] at hrestore
      · rw [Expr.abstractList_fvar_fresh_alpha hmem]
        exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | mvar id => simp [Closed] at hclosed
  | sort level =>
      have habstract : (Expr.sort level).abstractList fvars k =
          .sort level := by
        induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
      rw [habstract]
      exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | const name levels =>
      rw [Expr.abstractList_const_alpha]
      exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | lit value =>
      have habstract : (Expr.lit value).abstractList fvars k =
          .lit value := by
        induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
      rw [habstract]
      exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | app fn arg ihFn ihArg =>
      rcases hclosed with ⟨hfn, harg⟩
      simp only [Expr.abstractList_app_alpha, Expr.instantiateRevList_app]
      rw [ihFn hfn, ihArg harg]
  | lam name domain body bi ihDomain ihBody =>
      rcases hclosed with ⟨hdomain, hbody⟩
      simp only [Expr.abstractList_lam_alpha, Expr.instantiateRevList_lam]
      rw [ihDomain hdomain, ihBody hbody]
  | forallE name domain body bi ihDomain ihBody =>
      rcases hclosed with ⟨hdomain, hbody⟩
      simp only [Expr.abstractList_forallE_alpha,
        Expr.instantiateRevList_forallE]
      rw [ihDomain hdomain, ihBody hbody]
  | letE name type value body nondep ihType ihValue ihBody =>
      rcases hclosed with ⟨htype, hvalue, hbody⟩
      simp only [Expr.abstractList_letE_alpha,
        Expr.instantiateRevList_letE]
      rw [ihType htype, ihValue hvalue, ihBody hbody]
  | mdata data body ihBody =>
      simp only [Expr.abstractList_mdata_alpha,
        Expr.instantiateRevList_mdata]
      rw [ihBody hclosed]
  | proj name index body ihBody =>
      simp only [Expr.abstractList_proj_alpha,
        Expr.instantiateRevList_proj]
      rw [ihBody hclosed]

/-- On well-scoped expressions, equality after closing the same
duplicate-free binder spine reflects concrete expression equality. -/
theorem Expr.abstractList_injective_of_closed
    (hnd : fvars.Nodup) (hleft : Closed left k) (hright : Closed right k)
    (H : left.abstractList fvars k = right.abstractList fvars k) :
    left = right := by
  have H' := congrArg
    (fun e => e.instantiateRevList (fvars.map Expr.fvar) k) H
  simpa [Expr.abstractList_instantiateRevList_eq_self hnd hleft,
    Expr.abstractList_instantiateRevList_eq_self hnd hright] using H'

/-- Successful WHNF runs on corresponding generated free variables are
alpha-aligned.  All-`cdecl` contexts make both runs operational identities;
the binder relation then closes the two distinct identifiers to the same
de Bruijn ordinal. -/
theorem Context.OrderedBinderRenaming.whnfFVarAt_alpha
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (i : Nat) (hi : i < left.length)
    (leftState leftOut rightState rightOut : State)
    (leftResult rightResult : Expr)
    (Hleft : whnf (.fvar (left[i]'hi)) leftContext leftState =
      .ok (leftResult, leftOut))
    (Hright : whnf (.fvar (right[i]'(H.binders.length_eq ▸ hi)))
      rightContext rightState = .ok (rightResult, rightOut)) :
    ExprAlphaUnder left right leftResult rightResult := by
  rcases whnf_fvar_result_eq leftContext leftState leftOut
      H.left_lctx_wf H.left_only_cdecls (left[i]'hi) leftResult Hleft with
    ⟨rfl, _⟩
  rcases whnf_fvar_result_eq rightContext rightState rightOut
      H.right_lctx_wf H.right_only_cdecls
      (right[i]'(H.binders.length_eq ▸ hi)) rightResult Hright with
    ⟨rfl, _⟩
  unfold ExprAlphaUnder
  rw [Expr.abstractList_fvarAt_alpha H.binders.left_nodup i hi,
    Expr.abstractList_fvarAt_alpha H.binders.right_nodup i
      (H.binders.length_eq ▸ hi), H.binders.length_eq]

/-- Successful WHNF runs on a literally shared outer free variable are
identical up to closing the generated binder spines. -/
theorem Context.OrderedBinderRenaming.whnfFVarShared_alpha
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (hfv : shared fv)
    (leftState leftOut rightState rightOut : State)
    (leftResult rightResult : Expr)
    (Hleft : whnf (.fvar fv) leftContext leftState =
      .ok (leftResult, leftOut))
    (Hright : whnf (.fvar fv) rightContext rightState =
      .ok (rightResult, rightOut)) :
    ExprAlphaUnder left right leftResult rightResult := by
  rcases whnf_fvar_result_eq leftContext leftState leftOut
      H.left_lctx_wf H.left_only_cdecls fv leftResult Hleft with
    ⟨rfl, _⟩
  rcases whnf_fvar_result_eq rightContext rightState rightOut
      H.right_lctx_wf H.right_only_cdecls fv rightResult Hright with
    ⟨rfl, _⟩
  unfold ExprAlphaUnder
  rcases H.shared_fresh fv hfv with ⟨hleft, hright⟩
  rw [Expr.abstractList_fvar_fresh_alpha hleft,
    Expr.abstractList_fvar_fresh_alpha hright]

end TypeChecker
end Lean4Lean
