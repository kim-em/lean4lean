import Lean4Lean.Verify.Inductive.Nested.Lowering

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact, cache-independent specification of `Expr.replace`. A successful
node callback stops traversal at that node; otherwise the relation records
the recursively restored children and the same update combinators used by
Lean's implementation. -/
inductive ExprReplacement (replaceNode : Expr → Option Expr) : Expr → Expr → Prop
  | hit (h : replaceNode input = some output) :
      ExprReplacement replaceNode input output
  | bvar (h : replaceNode (.bvar i) = none) :
      ExprReplacement replaceNode (.bvar i) (.bvar i)
  | fvar {fvarId : FVarId} (h : replaceNode (.fvar fvarId) = none) :
      ExprReplacement replaceNode (.fvar fvarId) (.fvar fvarId)
  | mvar {mvarId : MVarId} (h : replaceNode (.mvar mvarId) = none) :
      ExprReplacement replaceNode (.mvar mvarId) (.mvar mvarId)
  | sort (h : replaceNode (.sort level) = none) :
      ExprReplacement replaceNode (.sort level) (.sort level)
  | const (h : replaceNode (.const name levels) = none) :
      ExprReplacement replaceNode (.const name levels) (.const name levels)
  | lit (h : replaceNode (.lit literal) = none) :
      ExprReplacement replaceNode (.lit literal) (.lit literal)
  | app (h : replaceNode (.app fn arg) = none)
      (hfn : ExprReplacement replaceNode fn fn')
      (harg : ExprReplacement replaceNode arg arg') :
      ExprReplacement replaceNode (.app fn arg)
        (Expr.updateApp! (.app fn arg) fn' arg')
  | lam (h : replaceNode (.lam name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.lam name dom body bi)
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body')
  | forallE (h : replaceNode (.forallE name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.forallE name dom body bi)
        (Expr.updateForallE! (.forallE name dom body bi) dom' body')
  | letE (h : replaceNode (.letE name type value body nondep) = none)
      (htype : ExprReplacement replaceNode type type')
      (hvalue : ExprReplacement replaceNode value value')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.letE name type value body nondep)
        (Expr.updateLetE! (.letE name type value body nondep)
          type' value' body')
  | mdata (h : replaceNode (.mdata data body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.mdata data body)
        (Expr.updateMData! (.mdata data body) body')
  | proj (h : replaceNode (.proj typeName index body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.proj typeName index body)
        (Expr.updateProj! (.proj typeName index body) body')

/-- A replacement callback which never matches a forall node preserves every
leading forall telescope and its exact arity.  The residual expression may
change, which is precisely what nested restoration does to auxiliary
applications below the binders. -/
theorem ExprReplacement.forallTelescope
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      Expr.ForallTelescope output arity restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil output⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | hit h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored⟩
      refine ⟨restoredResidual, ?_⟩
      simpa [Expr.updateForallE!] using
        (Expr.ForallTelescope.cons (name := name) (dom := _)
          (bi := bi) Hrestored)

/-- Residual-sensitive form of `forallTelescope`: replacement below the
leading binders is retained as an explicit relation between the old and new
residual expressions. -/
theorem ExprReplacement.forallTelescope_residual
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      Expr.ForallTelescope output arity restoredResidual ∧
      ExprReplacement replaceNode residual restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil output, Hreplace⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | hit h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored, Hresidual⟩
      refine ⟨restoredResidual, ?_, Hresidual⟩
      simpa [Expr.updateForallE!] using
        (Expr.ForallTelescope.cons (name := name) (dom := _)
          (bi := bi) Hrestored)

/-- Binder-aligned form of expression replacement.  Unlike the existential
`forallTelescope_residual` theorem, this relation retains the replacement
proof for every old/restored domain and for the final residual. -/
inductive ExprReplacement.ForallTelescopeReplacement
    (replaceNode : Expr → Option Expr) :
    Expr → Expr → Nat → Expr → Expr → Prop
  | nil (Hbody : ExprReplacement replaceNode oldBody newBody) :
      ExprReplacement.ForallTelescopeReplacement replaceNode
        oldBody newBody 0 oldBody newBody
  | cons
      (Hnone : replaceNode (.forallE name oldDom oldBody bi) = none)
      (Hdom : ExprReplacement replaceNode oldDom newDom)
      (Hbody : ExprReplacement.ForallTelescopeReplacement replaceNode
        oldBody newBody arity oldResidual newResidual) :
      ExprReplacement.ForallTelescopeReplacement replaceNode
        (.forallE name oldDom oldBody bi)
        (Expr.updateForallE! (.forallE name oldDom oldBody bi)
          newDom newBody)
        (arity + 1) oldResidual newResidual

/-- Decompose a replacement of a known forall telescope into the exact
binder-aligned replacement trace. -/
theorem ExprReplacement.forallTelescopeReplacement
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      ExprReplacement.ForallTelescopeReplacement replaceNode input output
        arity residual restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil Hreplace⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | hit h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored⟩
      exact ⟨restoredResidual, .cons h hdom Hrestored⟩

theorem ExprReplacement.ForallTelescopeReplacement.oldTelescope
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    Expr.ForallTelescope input arity oldResidual := by
  induction H with
  | nil => exact .nil _
  | cons _ _ _ ih => exact .cons ih

theorem ExprReplacement.ForallTelescopeReplacement.newTelescope
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    Expr.ForallTelescope output arity newResidual := by
  induction H with
  | nil => exact .nil _
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    simpa [Expr.updateForallE!] using
      (Expr.ForallTelescope.cons (name := name) (dom := newDom)
        (bi := bi) ih)

theorem ExprReplacement.ForallTelescopeReplacement.residualReplacement
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    ExprReplacement replaceNode oldResidual newResidual := by
  induction H with
  | nil Hbody => exact Hbody
  | cons _ _ _ ih => exact ih

/-- Ordered data view of the binder-aligned replacement telescope.  Because
the replacement derivation lives in `Prop`, the list is exposed
existentially; each pair retains its exact relational replacement fact. -/
theorem ExprReplacement.ForallTelescopeReplacement.domainPairs
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    ∃ pairs : List (Expr × Expr),
      pairs.length = arity ∧
      ∀ pair ∈ pairs,
        ExprReplacement replaceNode pair.1 pair.2 := by
  induction H with
  | nil => exact ⟨[], rfl, by simp⟩
  | @cons name oldDomain oldBody bi newDomain newBody arity oldResidual
      newResidual Hnone Hdomain Hbody ih =>
    rcases ih with ⟨pairs, hlength, Hpairs⟩
    refine ⟨(oldDomain, newDomain) :: pairs, by simp [hlength], ?_⟩
    intro pair hpair
    rcases List.mem_cons.mp hpair with rfl | htail
    · exact Hdomain
    · exact Hpairs pair htail

/-- Existential target of a concrete expression which translates to an
abstract type in the indicated context. -/
def Expr.AbstractTypeTranslation
    (env : VEnv) (Us : List Name) (Δ : VLCtx) (source : Expr) : Prop :=
  ∃ target, TrExprS env Us Δ source target ∧
    env.IsType Us.length Δ.toCtx target

/-- Semantic fold over a binder-aligned replacement trace.  It isolates the
remaining restoration proof to typed translation of each restored domain and
of the final residual in their exact progressively extended contexts. -/
theorem ExprReplacement.ForallTelescopeReplacement.typeTranslation
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual)
    (Hdomains : ∀ {oldDomain newDomain},
      ExprReplacement replaceNode oldDomain newDomain →
      ∀ Δ, Expr.AbstractTypeTranslation env Us Δ newDomain)
    (Hresidual : ∀ Δ,
      Expr.AbstractTypeTranslation env Us Δ newResidual) :
    ∃ target,
      Expr.ForallTelescopeTypeTranslation env Us Δ output arity target := by
  induction H generalizing Δ with
  | nil Hbody =>
    rcases Hresidual Δ with ⟨target, Htr, Htype⟩
    exact ⟨target, .nil Htr Htype⟩
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    rcases Hdomains Hdom Δ with ⟨domain, Hdomain, HdomainType⟩
    rcases ih (Δ := (none, .vlam domain) :: Δ) Hresidual with
      ⟨body, HbodyTyped⟩
    refine ⟨.forallE domain body, ?_⟩
    simpa [Expr.updateForallE!] using
      (Expr.ForallTelescopeTypeTranslation.cons
        (name := name) (bi := bi) Hdomain HdomainType HbodyTyped)

/-- Lockstep semantic transport from an already typed old telescope to its
restored telescope.  Each callback receives the exact old translation and
typehood derivation together with the exact replacement proof that produced
the new concrete expression. -/
theorem ExprReplacement.ForallTelescopeReplacement.transportTypeTranslation
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual)
    (Hold : Expr.ForallTelescopeTypeTranslation oldEnv Us oldΔ input arity
      oldTarget)
    (Hdomains : ∀ {oldΔ newΔ oldDomain newDomain oldDomainTarget},
      ExprReplacement replaceNode oldDomain newDomain →
      TrExprS oldEnv Us oldΔ oldDomain oldDomainTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldDomainTarget →
      Expr.AbstractTypeTranslation newEnv Us newΔ newDomain)
    (Hresidual : ∀ {oldΔ newΔ oldResidualTarget},
      ExprReplacement replaceNode oldResidual newResidual →
      TrExprS oldEnv Us oldΔ oldResidual oldResidualTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldResidualTarget →
      Expr.AbstractTypeTranslation newEnv Us newΔ newResidual) :
    ∃ newTarget,
      Expr.ForallTelescopeTypeTranslation newEnv Us newΔ output arity
        newTarget := by
  induction H generalizing oldΔ newΔ oldTarget with
  | nil Hbody =>
    rcases Hresidual Hbody Hold.translation Hold.isType with
      ⟨target, Htr, Htype⟩
    exact ⟨target, .nil Htr Htype⟩
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    cases Hold with
    | cons HoldDom HoldDomType HoldBody =>
      rcases Hdomains Hdom HoldDom HoldDomType with
        ⟨newDomainTarget, HnewDomain, HnewDomainType⟩
      rcases ih HoldBody (Hresidual := Hresidual)
          (newΔ := (none, .vlam newDomainTarget) :: newΔ) with
        ⟨newBodyTarget, HnewBody⟩
      refine ⟨.forallE newDomainTarget newBodyTarget, ?_⟩
      simpa [Expr.updateForallE!] using
        (Expr.ForallTelescopeTypeTranslation.cons
          (name := name) (bi := bi) HnewDomain HnewDomainType HnewBody)

/-- Parameter-closing form of `transportTypeTranslation`.  Restoration first
opens common parameters as fresh fvars; the installed recursor then closes
them outside the suffix telescope.  This theorem performs that abstraction
at the exact suffix depth of every domain and residual. -/
theorem ExprReplacement.ForallTelescopeReplacement.transportAbstractedTypeTranslation
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual)
    (Hold : Expr.ForallTelescopeTypeTranslation oldEnv Us oldΔ
      (input.abstractList oldParams depth) arity oldTarget)
    (Hdomains : ∀ {oldΔ newΔ oldDomain newDomain oldDomainTarget}
        (binderDepth : Nat),
      ExprReplacement replaceNode oldDomain newDomain →
      TrExprS oldEnv Us oldΔ
        (oldDomain.abstractList oldParams binderDepth) oldDomainTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldDomainTarget →
      Expr.AbstractTypeTranslation newEnv Us newΔ
        (newDomain.abstractList newParams binderDepth))
    (Hresidual : ∀ {oldΔ newΔ oldResidualTarget},
      ExprReplacement replaceNode oldResidual newResidual →
      TrExprS oldEnv Us oldΔ
        (oldResidual.abstractList oldParams (depth + arity))
        oldResidualTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldResidualTarget →
      Expr.AbstractTypeTranslation newEnv Us newΔ
        (newResidual.abstractList newParams (depth + arity))) :
    ∃ newTarget,
      Expr.ForallTelescopeTypeTranslation newEnv Us newΔ
        (output.abstractList newParams depth) arity newTarget := by
  induction H generalizing oldΔ newΔ oldTarget depth with
  | nil Hbody =>
    rcases Hresidual Hbody Hold.translation Hold.isType with
      ⟨target, Htr, Htype⟩
    exact ⟨target, .nil Htr Htype⟩
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    rw [Expr.abstractList_forallE] at Hold
    cases Hold with
    | cons HoldDom HoldDomType HoldBody =>
      rcases Hdomains (oldΔ := oldΔ) (newΔ := newΔ) depth Hdom HoldDom
          HoldDomType with
        ⟨newDomainTarget, HnewDomain, HnewDomainType⟩
      rcases ih HoldBody (Hresidual := by
          intro oldΔ newΔ oldResidualTarget Hreplacement Htr Htype
          have Htransported := Hresidual (oldΔ := oldΔ) (newΔ := newΔ)
            Hreplacement (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Htr)
            Htype
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Htransported)
          (newΔ := (none, .vlam newDomainTarget) :: newΔ)
          (depth := depth + 1) with ⟨newBodyTarget, HnewBody⟩
      refine ⟨.forallE newDomainTarget newBodyTarget, ?_⟩
      simpa [Expr.updateForallE!, Expr.abstractList_forallE] using
        (Expr.ForallTelescopeTypeTranslation.cons
          (name := name) (bi := bi) HnewDomain HnewDomainType HnewBody)

/-- Accumulator-aware parameter-closing transport.  `newPrefix` is the list
of restored abstract domains already traversed, so every callback receives
the exact `abstractForallContext newPrefix newBase` in which its concrete
domain is translated. -/
theorem ExprReplacement.ForallTelescopeReplacement.transportAbstractedAt
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual)
    (Hold : Expr.ForallTelescopeTypeTranslation oldEnv Us oldΔ
      (input.abstractList oldParams depth) arity oldTarget)
    (Hdomains : ∀ {oldΔ oldDomain newDomain oldDomainTarget}
        (binderDepth : Nat) (newPrefix : List VExpr),
      ExprReplacement replaceNode oldDomain newDomain →
      TrExprS oldEnv Us oldΔ
        (oldDomain.abstractList oldParams binderDepth) oldDomainTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldDomainTarget →
      Expr.AbstractTypeTranslation newEnv Us
        (abstractForallContext newPrefix newBase)
        (newDomain.abstractList newParams binderDepth))
    (Hresidual : ∀ {oldΔ oldResidualTarget}
        (newPrefix : List VExpr),
      ExprReplacement replaceNode oldResidual newResidual →
      TrExprS oldEnv Us oldΔ
        (oldResidual.abstractList oldParams (depth + arity))
        oldResidualTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldResidualTarget →
      Expr.AbstractTypeTranslation newEnv Us
        (abstractForallContext newPrefix newBase)
        (newResidual.abstractList newParams (depth + arity))) :
    ∃ newTarget,
      Expr.ForallTelescopeTypeTranslation newEnv Us
        (abstractForallContext newPrefix newBase)
        (output.abstractList newParams depth) arity newTarget := by
  induction H generalizing oldΔ oldTarget depth newPrefix with
  | nil Hbody =>
    rcases Hresidual newPrefix Hbody Hold.translation Hold.isType with
      ⟨target, Htr, Htype⟩
    exact ⟨target, .nil Htr Htype⟩
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    rw [Expr.abstractList_forallE] at Hold
    cases Hold with
    | cons HoldDom HoldDomType HoldBody =>
      rcases Hdomains depth newPrefix Hdom HoldDom HoldDomType with
        ⟨newDomainTarget, HnewDomain, HnewDomainType⟩
      rcases ih HoldBody (Hresidual := by
          intro oldΔ oldResidualTarget extendedPrefix Hreplacement Htr Htype
          have Htransported := Hresidual extendedPrefix Hreplacement (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Htr)
            Htype
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Htransported)
          (depth := depth + 1)
          (newPrefix := newPrefix ++ [newDomainTarget]) with
        ⟨newBodyTarget, HnewBody⟩
      have HnewBody' : Expr.ForallTelescopeTypeTranslation newEnv Us
          ((none, .vlam newDomainTarget) ::
            abstractForallContext newPrefix newBase)
          (newBody.abstractList newParams (depth + 1)) arity
          newBodyTarget := by
        simpa [abstractForallContext, List.reverse_append,
          List.map_append, List.append_assoc] using HnewBody
      refine ⟨.forallE newDomainTarget newBodyTarget, ?_⟩
      simpa [Expr.updateForallE!, Expr.abstractList_forallE] using
        (Expr.ForallTelescopeTypeTranslation.cons
          (name := name) (bi := bi) HnewDomain HnewDomainType HnewBody')

/-- Position-indexed form of `transportAbstractedAt`.  The first restored
domain is presented at `position`; recursive calls increment it exactly once
per forall binder.  This is the bridge from the structural replacement fold
to the motive/minor/index/major slot layout of a generated recursor. -/
theorem ExprReplacement.ForallTelescopeReplacement.transportAbstractedAtFrom
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual)
    (Hold : Expr.ForallTelescopeTypeTranslation oldEnv Us oldΔ
      (input.abstractList oldParams depth) arity oldTarget)
    (limit position : Nat) (hspan : position + arity = limit)
    (HnewCtx : OnCtx (abstractForallContext newPrefix newBase).toCtx
      (newEnv.IsType Us.length))
    (Hdomains : ∀ {oldΔ oldDomain newDomain oldDomainTarget}
        (position binderDepth : Nat) (newPrefix : List VExpr),
      position < limit →
      OnCtx (abstractForallContext newPrefix newBase).toCtx
        (newEnv.IsType Us.length) →
      ExprReplacement replaceNode oldDomain newDomain →
      TrExprS oldEnv Us oldΔ
        (oldDomain.abstractList oldParams binderDepth) oldDomainTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldDomainTarget →
      Expr.AbstractTypeTranslation newEnv Us
        (abstractForallContext newPrefix newBase)
        (newDomain.abstractList newParams binderDepth))
    (Hresidual : ∀ {oldΔ oldResidualTarget}
        (newPrefix : List VExpr),
      OnCtx (abstractForallContext newPrefix newBase).toCtx
        (newEnv.IsType Us.length) →
      ExprReplacement replaceNode oldResidual newResidual →
      TrExprS oldEnv Us oldΔ
        (oldResidual.abstractList oldParams (depth + arity))
        oldResidualTarget →
      oldEnv.IsType Us.length oldΔ.toCtx oldResidualTarget →
      Expr.AbstractTypeTranslation newEnv Us
        (abstractForallContext newPrefix newBase)
        (newResidual.abstractList newParams (depth + arity))) :
    ∃ newTarget,
      Expr.ForallTelescopeTypeTranslation newEnv Us
        (abstractForallContext newPrefix newBase)
        (output.abstractList newParams depth) arity newTarget := by
  induction H generalizing oldΔ oldTarget depth position newPrefix with
  | nil Hbody =>
    rcases Hresidual newPrefix HnewCtx Hbody Hold.translation Hold.isType with
      ⟨target, Htr, Htype⟩
    exact ⟨target, .nil Htr Htype⟩
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    rw [Expr.abstractList_forallE] at Hold
    cases Hold with
    | cons HoldDom HoldDomType HoldBody =>
      rcases Hdomains position depth newPrefix (by omega) HnewCtx Hdom HoldDom
          HoldDomType with
        ⟨newDomainTarget, HnewDomain, HnewDomainType⟩
      have HnewCtx' : OnCtx
          (abstractForallContext (newPrefix ++ [newDomainTarget])
            newBase).toCtx (newEnv.IsType Us.length) := by
        rw [abstractForallContext_toCtx, List.reverse_append]
        simp only [List.reverse_singleton, List.singleton_append]
        change OnCtx (newPrefix.reverse ++ newBase.toCtx)
            (newEnv.IsType Us.length) ∧
          newEnv.IsType Us.length (newPrefix.reverse ++ newBase.toCtx)
            newDomainTarget
        exact ⟨by
          simpa [abstractForallContext_toCtx] using HnewCtx, by
          simpa [abstractForallContext_toCtx] using HnewDomainType⟩
      rcases ih HoldBody (Hresidual := by
          intro oldΔ oldResidualTarget extendedPrefix HextendedCtx
              Hreplacement Htr Htype
          have Htransported := Hresidual extendedPrefix HextendedCtx
            Hreplacement (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Htr)
            Htype
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Htransported)
          (depth := depth + 1) (position := position + 1)
          (hspan := by omega)
          (newPrefix := newPrefix ++ [newDomainTarget]) HnewCtx' with
        ⟨newBodyTarget, HnewBody⟩
      have HnewBody' : Expr.ForallTelescopeTypeTranslation newEnv Us
          ((none, .vlam newDomainTarget) ::
            abstractForallContext newPrefix newBase)
          (newBody.abstractList newParams (depth + 1)) arity
          newBodyTarget := by
        simpa [abstractForallContext, List.reverse_append,
          List.map_append, List.append_assoc] using HnewBody
      refine ⟨.forallE newDomainTarget newBodyTarget, ?_⟩
      simpa [Expr.updateForallE!, Expr.abstractList_forallE] using
        (Expr.ForallTelescopeTypeTranslation.cons
          (name := name) (bi := bi) HnewDomain HnewDomainType HnewBody')

theorem ExprReplacement.ofReplace
    (replaceNode : Expr → Option Expr) :
    ∀ input, ExprReplacement replaceNode input (input.replace replaceNode) := by
  intro input
  induction input with
  | bvar i =>
    cases h : replaceNode (.bvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.bvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | fvar i =>
    cases h : replaceNode (.fvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.fvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | mvar i =>
    cases h : replaceNode (.mvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.mvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | sort level =>
    cases h : replaceNode (.sort level) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.sort h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | const name levels =>
    cases h : replaceNode (.const name levels) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.const h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | lit literal =>
    cases h : replaceNode (.lit literal) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.lit h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | app fn arg hfn harg =>
    cases h : replaceNode (.app fn arg) with
    | none =>
      rw [Expr.replace_eq] at hfn harg
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .app h hfn harg
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)

  | lam name dom body bi hdom hbody =>
    cases h : replaceNode (.lam name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .lam h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | forallE name dom body bi hdom hbody =>
    cases h : replaceNode (.forallE name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .forallE h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | letE name type value body nondep htype hvalue hbody =>
    cases h : replaceNode (.letE name type value body nondep) with
    | none =>
      rw [Expr.replace_eq] at htype hvalue hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .letE h htype hvalue hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | mdata data body hbody =>
    cases h : replaceNode (.mdata data body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .mdata h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)
  | proj typeName index body hbody =>
    cases h : replaceNode (.proj typeName index body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .proj h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.hit h)

/-- The relational restoration traversal is functional and computes exactly
`Expr.replace`.  This lets later semantic inverse theorems consume the
abstract `ExprReplacement` witness retained by `NestedRestoration`. -/
theorem ExprReplacement.eq_replace
    (H : ExprReplacement replaceNode input output) :
    output = input.replace replaceNode := by
  induction H with
  | hit h => simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]
  | bvar h | fvar h | mvar h | sort h | const h | lit h =>
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]
  | app h hfn harg ihFn ihArg =>
    rw [Expr.replace_eq] at ihFn ihArg
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihFn, ← ihArg]
  | lam h hdom hbody ihDom ihBody =>
    rw [Expr.replace_eq] at ihDom ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihDom, ← ihBody]
  | forallE h hdom hbody ihDom ihBody =>
    rw [Expr.replace_eq] at ihDom ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihDom, ← ihBody]
  | letE h htype hvalue hbody ihType ihValue ihBody =>
    rw [Expr.replace_eq] at ihType ihValue ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihType, ← ihValue, ← ihBody]
  | mdata h hbody ihBody | proj h hbody ihBody =>
    rw [Expr.replace_eq] at ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihBody]

/-- The body traversal used by `restoreNested` is now related exactly to its
three independently specified node-restoration cases. -/
theorem restoreNested_body
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (body : Expr) :
    ExprReplacement (result.restoreNestedNode env As auxRec) body
      (body.replace (result.restoreNestedNode env As auxRec)) :=
  ExprReplacement.ofReplace _ body

/-- Mixed forall/lambda telescope accepted by nested restoration. The
production function preserves the outer kind chosen by the original root,
while both binder forms are accepted during opening. -/
inductive RestoreTelescope : Expr → Nat → Prop
  | done : RestoreTelescope e 0
  | forallE : RestoreTelescope body n →
      RestoreTelescope (.forallE name dom body bi) (n + 1)
  | lam : RestoreTelescope body n →
      RestoreTelescope (.lam name dom body bi) (n + 1)

theorem Expr.ForallTelescope.inferImplicit
    (H : Expr.ForallTelescope e arity residual)
    (max : Nat) (inferBinderTypes : Bool) :
    ∃ residual',
      Expr.ForallTelescope (e.inferImplicit max inferBinderTypes) arity
        residual' := by
  induction max generalizing e arity residual with
  | zero => exact ⟨residual, by simpa [Expr.inferImplicit] using H⟩
  | succ max ih =>
    cases H with
    | nil => exact ⟨_, .nil _⟩
    | cons Htail =>
      rcases ih Htail with ⟨residual', Htail'⟩
      exact ⟨residual', by
        simp only [Expr.inferImplicit]
        exact Expr.ForallTelescope.cons Htail'⟩

/-- `inferImplicit` changes binder annotations only, so the terminal
expression of a forall telescope is preserved literally. -/
theorem Expr.ForallTelescope.inferImplicit_sameResidual
    (H : Expr.ForallTelescope e arity residual)
    (Hresidual : residual.isForall = false)
    (max : Nat) (inferBinderTypes : Bool) :
    Expr.ForallTelescope (e.inferImplicit max inferBinderTypes) arity
      residual := by
  induction max generalizing e arity residual with
  | zero => simpa [Expr.inferImplicit] using H
  | succ max ih =>
    cases H with
    | nil =>
      have heq : e.inferImplicit (max + 1) inferBinderTypes = e := by
        cases e <;> simp_all [Expr.inferImplicit, Expr.isForall]
      rw [heq]
      exact .nil _
    | cons Htail =>
      simp only [Expr.inferImplicit]
      exact Expr.ForallTelescope.cons (ih Htail Hresidual)

/-- Any prefix of a generated forall telescope is accepted by nested
restoration. -/
theorem Expr.ForallTelescope.restorePrefix
    (H : Expr.ForallTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | cons Hbody =>
      apply RestoreTelescope.forallE
      exact ih Hbody (by omega)

/-- Any prefix of a generated lambda telescope is accepted by nested
restoration. -/
theorem Expr.LambdaTelescope.restorePrefix
    (H : Expr.LambdaTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | @cons body arity residual name dom bi Hbody =>
      apply RestoreTelescope.lam
      exact ih Hbody (by omega)

/-- Production iota RHSs always expose at least the common-parameter lambda
prefix consumed by `restoreNested`. -/
theorem BoundGeneratedRecursorRule.rhsRestoreTelescope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope rule.rhs nparams := by
  apply H.rhsLambdaTelescope.restorePrefix
  rw [hparams]
  have hp : stats.params.size = H.params_bound.fvars.length := by
    simpa using congrArg Array.size H.params_bound.expressions
  unfold BoundGeneratedRecursorRule.binders
  simp only [List.length_append]
  omega

/-- The production recursor type exposes the same retained parameter prefix
that was bound while generating its telescope. -/
theorem GeneratedRecursorEntry.typeRestoreTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hparams : LocalForallSelection c.lctx stats.params)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope H.info.type nparams := by
  rw [H.type, hparams]
  rcases (Hparams.forallTelescope _).inferImplicit 1000 false with
    ⟨residual, Htelescope⟩
  exact Htelescope.restorePrefix (Nat.le_refl _)

/-- The generated `RecursorVal.type` retains the complete five-part recursor
telescope even after production's implicit-binder annotation pass. -/
theorem GeneratedRecursorEntry.typeForallTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx) :
    ∃ residual,
      Expr.ForallTelescope H.info.type
        (stats.params.size + (recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)
        residual := by
  rw [H.type]
  exact (Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)).inferImplicit
        1000 false

/-- Binder-by-binder semantic decomposition of a generated recursor type.
The five lists are the abstract domains corresponding respectively to the
production parameter, motive, minor, index, and major binder groups.  Keeping
the translated residual in their exact abstract context makes the pieces that
must later be transported across nested restoration explicit. -/
structure GeneratedRecursorTelescopeTranslation
    (env : VEnv) (Us : List Name) (source : Expr) (target : VExpr)
    (numParams numMotives numMinors numIndices ownerIdx : Nat) where
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  result : VExpr
  target_eq : target = VExpr.wrapForalls
    (params ++ motives ++ minors ++ indices ++ major) result
  params_length : params.length = numParams
  motives_length : motives.length = numMotives
  minors_length : minors.length = numMinors
  indices_length : indices.length = numIndices
  major_length : major.length = 1
  typed : Expr.ForallTelescopeTypeTranslation env Us [] source
    (numParams + numMotives + numMinors + numIndices + 1) target
  residual : TrExprS env Us
    (abstractForallContext
      (params ++ motives ++ minors ++ indices ++ major) [])
    (concreteRecursorResult numMotives numMinors numIndices ownerIdx) result

/-- Any two retained decompositions of the same translated recursor type
have the same complete domain list and residual.  This lets later equation
frames freely choose their operational witness and import semantic facts
proved using another existential witness. -/
theorem GeneratedRecursorTelescopeTranslation.domainsResult_eq
    (T₁ T₂ : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    T₁.params ++ T₁.motives ++ T₁.minors ++ T₁.indices ++ T₁.major =
        T₂.params ++ T₂.motives ++ T₂.minors ++ T₂.indices ++ T₂.major ∧
      T₁.result = T₂.result := by
  let domains₁ :=
    T₁.params ++ T₁.motives ++ T₁.minors ++ T₁.indices ++ T₁.major
  let domains₂ :=
    T₂.params ++ T₂.motives ++ T₂.minors ++ T₂.indices ++ T₂.major
  have hlength₁ : domains₁.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains₁, List.length_append, T₁.params_length,
      T₁.motives_length, T₁.minors_length, T₁.indices_length,
      T₁.major_length]
  have hlength₂ : domains₂.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains₂, List.length_append, T₂.params_length,
      T₂.motives_length, T₂.minors_length, T₂.indices_length,
      T₂.major_length]
  have hwrapped : VExpr.wrapForalls domains₁ T₁.result =
      VExpr.wrapForalls domains₂ T₂.result := by
    rw [← T₁.target_eq, ← T₂.target_eq]
  have hdomains : domains₁ = domains₂ := by
    exact VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hlength₁ hlength₂ (by simpa using hwrapped)
  refine ⟨by simpa [domains₁, domains₂] using hdomains, ?_⟩
  apply VExpr.wrapForalls_left_cancel domains₂
  rw [hdomains] at hwrapped
  exact hwrapped

/-- Groupwise form of `domainsResult_eq`, using the five fixed production
arities to recover each retained telescope component. -/
theorem GeneratedRecursorTelescopeTranslation.groupsResult_eq
    (T₁ T₂ : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    T₁.params = T₂.params ∧ T₁.motives = T₂.motives ∧
      T₁.minors = T₂.minors ∧ T₁.indices = T₂.indices ∧
      T₁.major = T₂.major ∧ T₁.result = T₂.result := by
  have H := T₁.domainsResult_eq T₂
  have H₀ : T₁.params ++
        (T₁.motives ++ (T₁.minors ++ (T₁.indices ++ T₁.major))) =
      T₂.params ++
        (T₂.motives ++ (T₂.minors ++ (T₂.indices ++ T₂.major))) := by
    simpa [List.append_assoc] using H.1
  have hparamsLength : T₁.params.length = T₂.params.length := by
    rw [T₁.params_length, T₂.params_length]
  have hparams := List.append_inj_left H₀ hparamsLength
  have H₁ := List.append_inj_right H₀ hparamsLength
  have hmotivesLength : T₁.motives.length = T₂.motives.length := by
    rw [T₁.motives_length, T₂.motives_length]
  have hmotives := List.append_inj_left H₁ hmotivesLength
  have H₂ := List.append_inj_right H₁ hmotivesLength
  have hminorsLength : T₁.minors.length = T₂.minors.length := by
    rw [T₁.minors_length, T₂.minors_length]
  have hminors := List.append_inj_left H₂ hminorsLength
  have H₃ := List.append_inj_right H₂ hminorsLength
  have hindicesLength : T₁.indices.length = T₂.indices.length := by
    rw [T₁.indices_length, T₂.indices_length]
  have hindices := List.append_inj_left H₃ hindicesLength
  have hmajor := List.append_inj_right H₃ hindicesLength
  exact ⟨hparams, hmotives, hminors, hindices, hmajor, H.2⟩

/-- Retained recursor-telescope translations are proof-irrelevant once their
six computational components are fixed.  This upgrades `groupsResult_eq`
from a rewriting interface to literal witness equality, which is needed when
later evidence is dependently indexed by the chosen telescope value. -/
theorem GeneratedRecursorTelescopeTranslation.eq
    (T₁ T₂ : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    T₁ = T₂ := by
  rcases T₁.groupsResult_eq T₂ with
    ⟨hparams, hmotives, hminors, hindices, hmajor, hresult⟩
  cases T₁
  cases T₂
  simp only at hparams hmotives hminors hindices hmajor hresult
  subst hparams
  subst hmotives
  subst hminors
  subst hindices
  subst hmajor
  subst hresult
  rfl

/-- The common parameter/motive/minor portions of two possibly different
mutual recursors are definitionally equal once their concrete source binder
domains are known to agree at those positions.  Owner-specific index/major
arities and residuals are deliberately allowed to differ. -/
theorem GeneratedRecursorTelescopeTranslation.commonPrefixDefEqCtx
    (Henv : env.WF)
    (T₁ : GeneratedRecursorTelescopeTranslation env Us source₁ target₁
      numParams numMotives numMinors numIndices₁ owner₁)
    (T₂ : GeneratedRecursorTelescopeTranslation env Us source₂ target₂
      numParams numMotives numMinors numIndices₂ owner₂)
    (Hdomains : ∀ i,
      i < numParams + numMotives + numMinors →
      (hi₁ : i < numParams + numMotives + numMinors + numIndices₁ + 1) →
      (hi₂ : i < numParams + numMotives + numMinors + numIndices₂ + 1) →
      ∀ {domain₁ domain₂ : Expr},
        Expr.ForallBinderAt source₁ i domain₁ →
        Expr.ForallBinderAt source₂ i domain₂ →
        domain₁ = domain₂) :
    VEnv.IsDefEqCtx env Us.length []
      (T₁.params ++ T₁.motives ++ T₁.minors).reverse
      (T₂.params ++ T₂.motives ++ T₂.minors).reverse := by
  let common := numParams + numMotives + numMinors
  let outer₁ := T₁.params ++ T₁.motives ++ T₁.minors
  let outer₂ := T₂.params ++ T₂.motives ++ T₂.minors
  let full₁ := outer₁ ++ T₁.indices ++ T₁.major
  let full₂ := outer₂ ++ T₂.indices ++ T₂.major
  have houter₁ : outer₁.length = common := by
    simp [outer₁, common, T₁.params_length, T₁.motives_length,
      T₁.minors_length] <;> omega
  have houter₂ : outer₂.length = common := by
    simp [outer₂, common, T₂.params_length, T₂.motives_length,
      T₂.minors_length] <;> omega
  have hfull₁ : full₁.length =
      numParams + numMotives + numMinors + numIndices₁ + 1 := by
    simp [full₁, outer₁, T₁.params_length, T₁.motives_length,
      T₁.minors_length, T₁.indices_length, T₁.major_length] <;> omega
  have hfull₂ : full₂.length =
      numParams + numMotives + numMinors + numIndices₂ + 1 := by
    simp [full₂, outer₂, T₂.params_length, T₂.motives_length,
      T₂.minors_length, T₂.indices_length, T₂.major_length] <;> omega
  have Hprefix := T₁.typed.commonPrefixDefEqCtx Henv T₂.typed
    full₁ full₂ T₁.result T₂.result
    (by simpa [full₁, outer₁, List.append_assoc] using T₁.target_eq)
    (by simpa [full₂, outer₂, List.append_assoc] using T₂.target_eq)
    hfull₁ hfull₂ common (by omega) (by omega) (by
      intro i hiprefix hi₁ hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
      exact Hdomains i (by simpa [common] using hiprefix)
        hi₁ hi₂ Hbinder₁ Hbinder₂)
  have htake₁ : full₁.take common = outer₁ := by
    rw [← houter₁]
    simp [full₁]
  have htake₂ : full₂.take common = outer₂ := by
    rw [← houter₂]
    simp [full₂]
  rw [htake₁, htake₂] at Hprefix
  simpa [outer₁, outer₂] using Hprefix

/-- Expose the source and abstract domains of the motive binder selected by
the recursor owner.  In particular, the domain is checked before later
motives, all minors, and the recursor's own index/major suffix have entered
the context.  This is the structural side of the bridge to the independently
replayed canonical motive telescope. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveBinder
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < T.motives.length) :
    ∃ (suffixSource : Expr) (name : Name)
      (sourceDomain sourceBody : Expr) (bi : BinderInfo)
      (bodyTarget : VExpr),
      Expr.ForallTelescope source (T.params.length + ownerIdx) suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      TrExprS env Us
        (abstractForallContext
          (T.params ++ T.motives.take ownerIdx) [])
        sourceDomain (T.motives[ownerIdx]'howner) ∧
      env.IsType Us.length
        (abstractForallContext
          (T.params ++ T.motives.take ownerIdx) []).toCtx
        (T.motives[ownerIdx]'howner) := by
  let domains := T.params ++
    (T.motives ++ (T.minors ++ (T.indices ++ T.major)))
  have hlength : domains.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length,
      T.major_length]
    omega
  have hposition : T.params.length + ownerIdx <
      numParams + numMotives + numMinors + numIndices + 1 := by
    rw [T.params_length, ← T.motives_length] at *
    omega
  have htarget : target = VExpr.wrapForalls domains T.result := by
    simpa only [domains, List.append_assoc] using T.target_eq
  rcases T.typed.binderAt_target domains T.result htarget hlength
      (T.params.length + ownerIdx) hposition with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType, _Hbody⟩
  have htake : domains.take (T.params.length + ownerIdx) =
      T.params ++ T.motives.take ownerIdx := by
    change (T.params ++
      (T.motives ++ (T.minors ++ (T.indices ++ T.major)))).take
        (T.params.length + ownerIdx) = _
    rw [List.take_length_add_append]
    rw [List.take_append_of_le_length (Nat.le_of_lt howner)]
  have hselected : domains[T.params.length + ownerIdx] =
      (T.motives[ownerIdx]'howner) := by
    simp only [domains]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left howner]
  rw [htake, hselected] at Hdomain HdomainType
  exact ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, Hdomain, HdomainType⟩

/-- Expose the source and abstract domains of one flattened minor binder.
The domain is checked after all parameters and motives and the strictly
earlier minors, but before later minors and the owner-specific suffix. -/
theorem GeneratedRecursorTelescopeTranslation.minorBinder
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (hminor : minorIdx < T.minors.length) :
    ∃ (suffixSource : Expr) (name : Name)
      (sourceDomain sourceBody : Expr) (bi : BinderInfo)
      (bodyTarget : VExpr),
      Expr.ForallTelescope source
        (T.params.length + T.motives.length + minorIdx) suffixSource ∧
      suffixSource = .forallE name sourceDomain sourceBody bi ∧
      TrExprS env Us
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take minorIdx) [])
        sourceDomain (T.minors[minorIdx]'hminor) ∧
      env.IsType Us.length
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take minorIdx) []).toCtx
        (T.minors[minorIdx]'hminor) := by
  let domains := T.params ++
    (T.motives ++ (T.minors ++ (T.indices ++ T.major)))
  have hlength : domains.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length,
      T.major_length]
    omega
  have hposition : T.params.length + T.motives.length + minorIdx <
      numParams + numMotives + numMinors + numIndices + 1 := by
    rw [T.params_length, T.motives_length, ← T.minors_length] at *
    omega
  have htarget : target = VExpr.wrapForalls domains T.result := by
    simpa only [domains, List.append_assoc] using T.target_eq
  rcases T.typed.binderAt_target domains T.result htarget hlength
      (T.params.length + T.motives.length + minorIdx) hposition with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType, _Hbody⟩
  have htake : domains.take
      (T.params.length + T.motives.length + minorIdx) =
      T.params ++ T.motives ++ T.minors.take minorIdx := by
    change (T.params ++
      (T.motives ++ (T.minors ++ (T.indices ++ T.major)))).take
        (T.params.length + T.motives.length + minorIdx) = _
    rw [show T.params ++
        (T.motives ++ (T.minors ++ (T.indices ++ T.major))) =
      (T.params ++ T.motives) ++
        (T.minors ++ (T.indices ++ T.major)) by simp]
    rw [show T.params.length + T.motives.length + minorIdx =
      (T.params ++ T.motives).length + minorIdx by simp]
    rw [List.take_length_add_append]
    rw [List.take_append_of_le_length (Nat.le_of_lt hminor)]
  have hselected :
      domains[T.params.length + T.motives.length + minorIdx] =
        T.minors[minorIdx] := by
    simp only [domains]
    rw [List.getElem_append_right (by omega)]
    have hoffParams :
        T.params.length + T.motives.length + minorIdx - T.params.length =
          T.motives.length + minorIdx := by omega
    simp only [hoffParams]
    rw [List.getElem_append_right (by omega)]
    have hoffMotives :
        T.motives.length + minorIdx - T.motives.length = minorIdx := by omega
    simp only [hoffMotives]
    rw [List.getElem_append_left hminor]
  rw [htake, hselected] at Hdomain HdomainType
  exact ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, Hdomain, HdomainType⟩

/-- Applying the parameter, motive, and minor prefix of a translated
recursor to its canonical variables leaves exactly the index/major suffix.
This is the typed spine shared by every generated equation for the owner. -/
theorem GeneratedRecursorTelescopeTranslation.prefixTyping
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.Ordered)
    (hfn : env.HasType Us.length [] fn target) :
    env.HasType Us.length
      (T.params ++ T.motives ++ T.minors).reverse
      (VExpr.mkApps (fn.liftN
        (T.params ++ T.motives ++ T.minors).length 0)
        (recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length))
      (VExpr.wrapForalls (T.indices ++ T.major) T.result) := by
  have hfn' : env.HasType Us.length [] fn
      (VExpr.wrapForalls
        ((T.params ++ T.motives ++ T.minors) ++
          (T.indices ++ T.major)) T.result) := by
    rw [T.target_eq] at hfn
    simpa [List.append_assoc] using hfn
  have happ := VEnv.HasType.mkApps_wrapForalls_prefix_canonical henv hfn'
  simpa [recursorCanonicalVars] using happ

/-- The common parameter/motive/minor prefix is itself a well-formed local
context, independently of the owner-specific index and major suffix. -/
theorem GeneratedRecursorTelescopeTranslation.prefixContext
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.Ordered) :
    OnCtx (T.params ++ T.motives ++ T.minors).reverse
      (env.IsType Us.length) := by
  have htype := T.typed.isType
  change env.IsType Us.length [] target at htype
  rw [T.target_eq] at htype
  have htype' : env.IsType Us.length []
      (VExpr.wrapForalls
        (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major)
        T.result) := by
    simpa using htype
  have hgrouped : env.IsType Us.length []
      (VExpr.wrapForalls (T.params ++ T.motives ++ T.minors)
        (VExpr.wrapForalls (T.indices ++ T.major) T.result)) := by
    simpa [VExpr.wrapForalls_append, List.append_assoc] using htype'
  simpa using
    (VEnv.IsType.wrapForalls_inv henv (by trivial) hgrouped).1

/-- Opening the complete translated recursor telescope leaves a well-typed
residual in the exact five-group context.  This is the inversion premise
used to recover the dependency of the owner motive application on the
generated index/major suffix. -/
theorem GeneratedRecursorTelescopeTranslation.fullContextResultType
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.Ordered) :
    let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
    OnCtx domains.reverse (env.IsType Us.length) ∧
      env.IsType Us.length domains.reverse T.result := by
  let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
  have htype := T.typed.isType
  change env.IsType Us.length [] target at htype
  rw [T.target_eq] at htype
  have htype' : env.IsType Us.length []
      (VExpr.wrapForalls domains T.result) := by
    simpa [domains] using htype
  have Hopened := VEnv.IsType.wrapForalls_inv henv (by trivial) htype'
  change OnCtx domains.reverse (env.IsType Us.length) ∧
    env.IsType Us.length domains.reverse T.result
  simpa only [List.append_nil] using Hopened

/-- The residual of any retained recursor-telescope translation is literally
the owner motive applied to the canonical variables for the translated index
and major suffix.  Keeping this theorem on `T` avoids choosing a second,
potentially unrelated existential translation when the result shape is used
together with the owner-motive telescope. -/
theorem GeneratedRecursorTelescopeTranslation.resultShape
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < numMotives) :
    T.result = VExpr.mkApps
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      (((List.range numIndices).reverse.map fun index =>
          .bvar (index + 1)) ++ [.bvar 0]) := by
  have htotal :
      numParams + numMotives + numMinors + numIndices + 1 ≤
        (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).length := by
    simp only [List.length_append, T.params_length, T.motives_length,
      T.minors_length, T.indices_length, T.major_length]
    exact Nat.le_refl _
  exact TrExprS.concreteRecursorResult_eq howner htotal T.residual

/-- In the complete generated recursor context, the owner motive is found
beneath precisely the later motives, all minors, and the owner index/major
suffix.  Its lookup type is therefore its declaration domain lifted once
for itself and once for every one of those newer declarations. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveBvarTyping
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < T.motives.length) :
    let newer := T.motives.drop (ownerIdx + 1) ++ T.minors ++
      T.indices ++ T.major
    let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
    env.HasType Us.length domains.reverse (.bvar newer.length)
      ((T.motives[ownerIdx]'howner).liftN (newer.length + 1) 0) := by
  let newer := T.motives.drop (ownerIdx + 1) ++ T.minors ++
    T.indices ++ T.major
  let older := (T.motives.take ownerIdx).reverse ++ T.params.reverse
  let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
  have hsplit : T.motives = T.motives.take ownerIdx ++
      T.motives[ownerIdx] :: T.motives.drop (ownerIdx + 1) := by
    calc
      T.motives = T.motives.take (ownerIdx + 1) ++
          T.motives.drop (ownerIdx + 1) :=
        (List.take_append_drop (ownerIdx + 1) T.motives).symm
      _ = (T.motives.take ownerIdx ++ [T.motives[ownerIdx]]) ++
          T.motives.drop (ownerIdx + 1) := by
        rw [List.take_append_getElem howner]
      _ = T.motives.take ownerIdx ++ T.motives[ownerIdx] ::
          T.motives.drop (ownerIdx + 1) := by
        simp [List.append_assoc]
  have hlookup : Lookup
      (newer.reverse ++ T.motives[ownerIdx] :: older)
      newer.length
      ((T.motives[ownerIdx]'howner).liftN (newer.length + 1) 0) := by
    simpa [List.length_reverse] using
      Lookup.append_zero newer.reverse (T.motives[ownerIdx]'howner) older
  have hmotivesReverse : T.motives.reverse =
      (T.motives.drop (ownerIdx + 1)).reverse ++
        T.motives[ownerIdx] :: (T.motives.take ownerIdx).reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse hsplit
  have hcontext : domains.reverse =
      newer.reverse ++ T.motives[ownerIdx] :: older := by
    dsimp [domains, newer, older]
    rw [List.reverse_append, List.reverse_append, List.reverse_append,
      List.reverse_append, hmotivesReverse]
    simp [List.append_assoc]
  apply VEnv.HasType.bvar
  rw [hcontext]
  exact hlookup

/-- Numerical specialization of `ownerMotiveBvarTyping` matching the bvar
offset used by `concreteRecursorResult`. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveBvarTypingAtOffset
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < numMotives) :
    let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
    let offset := 1 + numIndices + numMinors +
      (numMotives - 1 - ownerIdx)
    env.HasType Us.length domains.reverse (.bvar offset)
      (T.motives[ownerIdx]!.liftN (offset + 1) 0) := by
  let newer := T.motives.drop (ownerIdx + 1) ++ T.minors ++
    T.indices ++ T.major
  let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
  let offset := 1 + numIndices + numMinors +
    (numMotives - 1 - ownerIdx)
  have howner' : ownerIdx < T.motives.length := by
    rw [T.motives_length]
    exact howner
  have hnewer : newer.length = offset := by
    simp only [newer, offset, List.length_append, List.length_drop,
      T.motives_length, T.minors_length, T.indices_length, T.major_length]
    omega
  have Htyping := T.ownerMotiveBvarTyping howner'
  simpa only [domains, newer, hnewer,
    getElem!_pos T.motives ownerIdx howner'] using Htyping

/-- Lookup form before the owner index/major suffix is opened.  This is the
function typing consumed by the generic canonical-application context
inversion. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveOuterBvarTyping
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (howner : ownerIdx < T.motives.length) :
    let later := T.motives.drop (ownerIdx + 1) ++ T.minors
    let outer := T.params ++ T.motives ++ T.minors
    env.HasType Us.length outer.reverse (.bvar later.length)
      ((T.motives[ownerIdx]'howner).liftN (later.length + 1) 0) := by
  let later := T.motives.drop (ownerIdx + 1) ++ T.minors
  let older := (T.motives.take ownerIdx).reverse ++ T.params.reverse
  let outer := T.params ++ T.motives ++ T.minors
  have hsplit : T.motives = T.motives.take ownerIdx ++
      T.motives[ownerIdx] :: T.motives.drop (ownerIdx + 1) := by
    calc
      T.motives = T.motives.take (ownerIdx + 1) ++
          T.motives.drop (ownerIdx + 1) :=
        (List.take_append_drop (ownerIdx + 1) T.motives).symm
      _ = (T.motives.take ownerIdx ++ [T.motives[ownerIdx]]) ++
          T.motives.drop (ownerIdx + 1) := by
        rw [List.take_append_getElem howner]
      _ = T.motives.take ownerIdx ++ T.motives[ownerIdx] ::
          T.motives.drop (ownerIdx + 1) := by
        simp [List.append_assoc]
  have hlookup : Lookup
      (later.reverse ++ T.motives[ownerIdx] :: older)
      later.length
      ((T.motives[ownerIdx]'howner).liftN (later.length + 1) 0) := by
    simpa [List.length_reverse] using
      Lookup.append_zero later.reverse (T.motives[ownerIdx]'howner) older
  have hmotivesReverse : T.motives.reverse =
      (T.motives.drop (ownerIdx + 1)).reverse ++
        T.motives[ownerIdx] :: (T.motives.take ownerIdx).reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse hsplit
  have hcontext : outer.reverse =
      later.reverse ++ T.motives[ownerIdx] :: older := by
    dsimp [outer, later, older]
    rw [List.reverse_append, List.reverse_append, hmotivesReverse]
    simp [List.append_assoc]
  apply VEnv.HasType.bvar
  rw [hcontext]
  exact hlookup

/-- A selected minor premise in the generated recursor prefix is found
beneath precisely the later flattened minors.  This is the minor analogue of
`ownerMotiveOuterBvarTyping`; constructor fields can subsequently weaken this
lookup into the complete equation context. -/
theorem GeneratedRecursorTelescopeTranslation.minorOuterBvarTyping
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (hminor : minorIdx < T.minors.length) :
    let later := T.minors.drop (minorIdx + 1)
    let outer := T.params ++ T.motives ++ T.minors
    env.HasType Us.length outer.reverse (.bvar later.length)
      ((T.minors[minorIdx]'hminor).liftN (later.length + 1) 0) := by
  let later := T.minors.drop (minorIdx + 1)
  let older := (T.minors.take minorIdx).reverse ++
    T.motives.reverse ++ T.params.reverse
  let outer := T.params ++ T.motives ++ T.minors
  have hsplit : T.minors = T.minors.take minorIdx ++
      T.minors[minorIdx] :: T.minors.drop (minorIdx + 1) := by
    calc
      T.minors = T.minors.take (minorIdx + 1) ++
          T.minors.drop (minorIdx + 1) :=
        (List.take_append_drop (minorIdx + 1) T.minors).symm
      _ = (T.minors.take minorIdx ++ [T.minors[minorIdx]]) ++
          T.minors.drop (minorIdx + 1) := by
        rw [List.take_append_getElem hminor]
      _ = T.minors.take minorIdx ++ T.minors[minorIdx] ::
          T.minors.drop (minorIdx + 1) := by
        simp [List.append_assoc]
  have hlookup : Lookup
      (later.reverse ++ T.minors[minorIdx] :: older)
      later.length
      ((T.minors[minorIdx]'hminor).liftN (later.length + 1) 0) := by
    simpa [List.length_reverse] using
      Lookup.append_zero later.reverse (T.minors[minorIdx]'hminor) older
  have hminorsReverse : T.minors.reverse =
      (T.minors.drop (minorIdx + 1)).reverse ++
        T.minors[minorIdx] :: (T.minors.take minorIdx).reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse hsplit
  have hcontext : outer.reverse =
      later.reverse ++ T.minors[minorIdx] :: older := by
    dsimp [outer, later, older]
    rw [List.reverse_append, List.reverse_append, hminorsReverse]
    simp [List.append_assoc]
  apply VEnv.HasType.bvar
  rw [hcontext]
  exact hlookup

/-- The oldest variable in the generated index/major suffix has the first
domain of the declared owner-motive telescope, weakened across all binders
newer than that motive.  This is the first dependent-domain equation exposed
by typing inversion of the literal generated result application. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveFirstArgumentTyping
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.WF)
    (howner : ownerIdx < numMotives)
    (motiveDomains : List VExpr) (resultLevel : VLevel)
    (hmotive : T.motives[ownerIdx]! =
      VExpr.wrapForalls motiveDomains (.sort resultLevel))
    (hlength : motiveDomains.length = numIndices + 1) :
    let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
    let offset := 1 + numIndices + numMinors +
      (numMotives - 1 - ownerIdx)
    ∃ first rest,
      motiveDomains = first :: rest ∧
      env.HasType Us.length domains.reverse (.bvar numIndices)
        (first.liftN (offset + 1) 0) := by
  let domains := T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major
  let offset := 1 + numIndices + numMinors +
    (numMotives - 1 - ownerIdx)
  cases motiveDomains with
  | nil => simp at hlength
  | cons first rest =>
    have Hfull := T.fullContextResultType henv.ordered
    change OnCtx domains.reverse (env.IsType Us.length) ∧
      env.IsType Us.length domains.reverse T.result at Hfull
    rcases Hfull with ⟨Hctx, resultType⟩
    rcases resultType with ⟨resultTypeLevel, Hresult⟩
    have HresultWF : VExpr.WF env Us.length domains.reverse T.result :=
      ⟨.sort resultTypeLevel, Hresult⟩
    rw [T.resultShape howner,
      concreteRecursorResultArgs_eq_canonical] at HresultWF
    have Howner := T.ownerMotiveBvarTypingAtOffset howner
    change env.HasType Us.length domains.reverse (.bvar offset)
      (T.motives[ownerIdx]!.liftN (offset + 1) 0) at Howner
    rw [hmotive] at Howner
    let liftedBody :=
      (VExpr.wrapForalls rest (.sort resultLevel)).liftN
        (offset + 1) 1
    have HownerForall : env.HasType Us.length domains.reverse
        (.bvar offset)
        (.forallE (first.liftN (offset + 1) 0) liftedBody) := by
      simpa [VExpr.wrapForalls, VExpr.liftN, liftedBody] using Howner
    have HresultWF' : VExpr.WF env Us.length domains.reverse
        (VExpr.mkApps (.bvar offset)
          (.bvar numIndices :: recursorCanonicalVars numIndices)) := by
      simpa [offset, recursorCanonicalVars_succ_cons] using HresultWF
    have Hfirst := VEnv.HasType.mkApps_head henv Hctx
      HownerForall HresultWF'
    refine ⟨first, rest, rfl, ?_⟩
    change env.HasType Us.length domains.reverse (.bvar numIndices)
      (first.liftN (offset + 1) 0)
    exact Hfirst

/-- The same oldest suffix variable also has the lookup type determined by
the first generated index/major declaration.  Together with
`ownerMotiveFirstArgumentTyping`, uniqueness compares the two domains. -/
theorem GeneratedRecursorTelescopeTranslation.suffixFirstBvarTyping
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    let outer := T.params ++ T.motives ++ T.minors
    let suffix := T.indices ++ T.major
    let domains := outer ++ suffix
    ∃ first rest,
      suffix = first :: rest ∧
      env.HasType Us.length domains.reverse (.bvar numIndices)
        (first.liftN (numIndices + 1) 0) := by
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let domains := outer ++ suffix
  have hsuffixLength : suffix.length = numIndices + 1 := by
    simp [suffix, T.indices_length, T.major_length]
  cases hsuffixEq : suffix with
  | nil => simp [hsuffixEq] at hsuffixLength
  | cons first rest =>
    have hrestLength : rest.length = numIndices := by
      simp [hsuffixEq] at hsuffixLength
      omega
    have Hlookup : Lookup (rest.reverse ++ first :: outer.reverse)
        rest.length (first.liftN (rest.length + 1) 0) := by
      simpa [List.length_reverse] using
        Lookup.append_zero rest.reverse first outer.reverse
    refine ⟨first, rest, hsuffixEq, ?_⟩
    have hcontext : domains.reverse =
        rest.reverse ++ first :: outer.reverse := by
      change (outer ++ suffix).reverse =
        rest.reverse ++ first :: outer.reverse
      rw [hsuffixEq, List.reverse_append, List.reverse_cons]
      simp [List.append_assoc]
    apply VEnv.HasType.bvar
    rw [hcontext]
    simpa [hrestLength] using Hlookup

/-- First dependent-domain alignment between the generated recursor suffix
and the owner motive.  The motive domain is weakened only across the later
motives and all minors; the common index/major weakening is removed from the
typing-uniqueness equation. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveFirstDomainDefEq
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.WF)
    (howner : ownerIdx < numMotives)
    (motiveDomains : List VExpr) (resultLevel : VLevel)
    (hmotive : T.motives[ownerIdx]! =
      VExpr.wrapForalls motiveDomains (.sort resultLevel))
    (hlength : motiveDomains.length = numIndices + 1) :
    let outer := T.params ++ T.motives ++ T.minors
    let suffix := T.indices ++ T.major
    let later := T.motives.drop (ownerIdx + 1) ++ T.minors
    ∃ generatedFirst generatedRest motiveFirst motiveRest,
      suffix = generatedFirst :: generatedRest ∧
      motiveDomains = motiveFirst :: motiveRest ∧
      env.IsDefEqU Us.length outer.reverse generatedFirst
        (motiveFirst.liftN (later.length + 1) 0) := by
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (ownerIdx + 1) ++ T.minors
  let domains := outer ++ suffix
  rcases T.suffixFirstBvarTyping with
    ⟨generatedFirst, generatedRest, hsuffix, Hgenerated⟩
  rcases T.ownerMotiveFirstArgumentTyping henv howner motiveDomains
      resultLevel hmotive hlength with
    ⟨motiveFirst, motiveRest, hmotiveDomains, Hmotive⟩
  have Hfull := T.fullContextResultType henv.ordered
  have Hctx : OnCtx domains.reverse (env.IsType Us.length) := by
    simpa [domains, outer, suffix, List.append_assoc] using Hfull.1
  have Hgenerated' : env.HasType Us.length domains.reverse
      (.bvar numIndices) (generatedFirst.liftN (numIndices + 1) 0) := by
    simpa [domains, outer, suffix, List.append_assoc] using Hgenerated
  have Hmotive' : env.HasType Us.length domains.reverse
      (.bvar numIndices)
      (motiveFirst.liftN
        (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx) + 1) 0) := by
    simpa [domains, outer, suffix, List.append_assoc] using Hmotive
  have Htypes := VEnv.IsDefEq.uniqU henv Hctx Hgenerated' Hmotive'
  have hsuffixLength : suffix.length = numIndices + 1 := by
    simp [suffix, T.indices_length, T.major_length]
  have hlaterLength : later.length =
      (numMotives - 1 - ownerIdx) + numMinors := by
    simp only [later, List.length_append, List.length_drop,
      T.motives_length, T.minors_length]
    omega
  have hshift :
      (later.length + 1) + (numIndices + 1) =
        (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)) + 1 := by
    omega
  have Htypes' : env.IsDefEqU Us.length domains.reverse
      (generatedFirst.liftN (numIndices + 1) 0)
      ((motiveFirst.liftN (later.length + 1) 0).liftN
        (numIndices + 1) 0) := by
    rw [VExpr.liftN_liftN, hshift]
    simpa [domains, outer, suffix] using Htypes
  have W : Ctx.LiftN suffix.length 0 outer.reverse domains.reverse := by
    simpa [domains, List.reverse_append] using
      (Ctx.LiftN.zero suffix.reverse (h := by simp) (Γ := outer.reverse))
  have Htypes'' :=
    (VEnv.IsDefEqU.weakN_iff henv Hctx W).mp (by
      simpa [hsuffixLength] using Htypes')
  exact ⟨generatedFirst, generatedRest, motiveFirst, motiveRest,
    hsuffix, hmotiveDomains, Htypes''⟩

/-- Complete dependent alignment of the generated owner index/major suffix
with the owner motive's declared domains.  The latter are weakened across
the later motive and minor declarations before the generic canonical-
application inversion compares the two completed contexts. -/
theorem GeneratedRecursorTelescopeTranslation.ownerMotiveSuffixContext
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (henv : env.WF)
    (howner : ownerIdx < numMotives)
    (motiveDomains : List VExpr) (resultLevel : VLevel)
    (hmotive : T.motives[ownerIdx]! =
      VExpr.wrapForalls motiveDomains (.sort resultLevel))
    (hlength : motiveDomains.length = numIndices + 1) :
    let outer := T.params ++ T.motives ++ T.minors
    let suffix := T.indices ++ T.major
    let later := T.motives.drop (ownerIdx + 1) ++ T.minors
    let expected :=
      (liftContextPrefixAt (later.length + 1) 0 motiveDomains.reverse).reverse
    VEnv.IsDefEqCtx env Us.length []
      (suffix.reverse ++ outer.reverse)
      (expected.reverse ++ outer.reverse) := by
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (ownerIdx + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0 motiveDomains.reverse).reverse
  have howner' : ownerIdx < T.motives.length := by
    rw [T.motives_length]
    exact howner
  have Howner := T.ownerMotiveOuterBvarTyping howner'
  change env.HasType Us.length outer.reverse (.bvar later.length)
    ((T.motives[ownerIdx]'howner').liftN (later.length + 1) 0) at Howner
  have hmotive' : T.motives[ownerIdx]'howner' =
      VExpr.wrapForalls motiveDomains (.sort resultLevel) := by
    simpa [getElem!_pos T.motives ownerIdx howner'] using hmotive
  rw [hmotive'] at Howner
  have Hfn : env.HasType Us.length outer.reverse (.bvar later.length)
      (VExpr.wrapForalls expected (.sort resultLevel)) := by
    simpa [expected, VExpr.liftN_wrapForalls, VExpr.liftN] using Howner
  have Hfull := T.fullContextResultType henv.ordered
  have Hctx : OnCtx (suffix.reverse ++ outer.reverse)
      (env.IsType Us.length) := by
    simpa [outer, suffix, List.reverse_append,
      List.append_assoc] using Hfull.1
  rcases Hfull.2 with ⟨typeLevel, Hresult⟩
  have HresultWF : VExpr.WF env Us.length
      (suffix.reverse ++ outer.reverse) T.result :=
    ⟨.sort typeLevel, by
      change env.HasType Us.length
        (suffix.reverse ++ outer.reverse) T.result (.sort typeLevel)
      simpa [outer, suffix, List.reverse_append,
        List.append_assoc] using Hresult⟩
  rw [T.resultShape howner,
    concreteRecursorResultArgs_eq_canonical] at HresultWF
  have hsuffixLength : suffix.length = numIndices + 1 := by
    simp [suffix, T.indices_length, T.major_length]
  have hlaterLength : later.length =
      (numMotives - 1 - ownerIdx) + numMinors := by
    simp only [later, List.length_append, List.length_drop,
      T.motives_length, T.minors_length]
    omega
  have hoffset : later.length + suffix.length =
      1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx) := by
    omega
  have hoffset' : later.length + (numIndices + 1) =
      1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx) := by
    omega
  have Happs : VExpr.WF env Us.length
      (suffix.reverse ++ outer.reverse)
      (VExpr.mkApps ((.bvar later.length : VExpr).liftN suffix.length 0)
        (recursorCanonicalVars suffix.length)) := by
    simpa [hsuffixLength, VExpr.liftN, liftVar_base, hoffset,
      hoffset'] using HresultWF
  have hexpectedLength : suffix.length = expected.length := by
    simp [expected, hsuffixLength, hlength]
  exact VEnv.HasType.canonicalApplicationContext henv suffix expected
    outer.reverse Hctx Hfn hexpectedLength Happs

/-- Remove the parameter/motive/minor prefix from the retained structural
translation.  The resulting certificate keeps the concrete production
suffix and identifies its abstract target with exactly `indices ++ major`,
not merely with an existential telescope of the same arity. -/
theorem GeneratedRecursorTelescopeTranslation.suffixTyped
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    let outerDomains := T.params ++ T.motives ++ T.minors
    ∃ sourceSuffix,
      Expr.ForallTelescope source outerDomains.length sourceSuffix ∧
      Expr.ForallTelescopeTypeTranslation env Us
        (abstractForallContext outerDomains []) sourceSuffix
        (T.indices ++ T.major).length
        (VExpr.wrapForalls (T.indices ++ T.major) T.result) := by
  let outerDomains := T.params ++ T.motives ++ T.minors
  have harity :
      numParams + numMotives + numMinors + numIndices + 1 =
        outerDomains.length + (T.indices ++ T.major).length := by
    simp only [outerDomains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length,
      T.major_length]
    omega
  have Htyped : Expr.ForallTelescopeTypeTranslation env Us [] source
      (outerDomains.length + (T.indices ++ T.major).length) target := by
    rw [← harity]
    exact T.typed
  rcases Htyped.dropPrefix with
    ⟨prefixDomains, sourceSuffix, suffixTarget, hprefixLength,
      Hsource, htarget, Hsuffix⟩
  have hprefixDomains : prefixDomains = outerDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq hprefixLength
      (rfl : outerDomains.length = outerDomains.length)
    calc
      VExpr.wrapForalls prefixDomains suffixTarget = target := htarget.symm
      _ = VExpr.wrapForalls
          (outerDomains ++ (T.indices ++ T.major)) T.result := by
        simpa [outerDomains, List.append_assoc] using T.target_eq
  subst prefixDomains
  have hsuffixTarget : suffixTarget =
      VExpr.wrapForalls (T.indices ++ T.major) T.result := by
    apply VExpr.wrapForalls_left_cancel outerDomains
    calc
      VExpr.wrapForalls outerDomains suffixTarget = target := htarget.symm
      _ = VExpr.wrapForalls outerDomains
          (VExpr.wrapForalls (T.indices ++ T.major) T.result) := by
        simpa [outerDomains, VExpr.wrapForalls_append, List.append_assoc] using
          T.target_eq
  subst suffixTarget
  exact ⟨sourceSuffix, Hsource, Hsuffix⟩

/-- Split the retained suffix at the exact index/major boundary.  Besides
the structural concrete telescopes, this exposes the single-major
binder-by-binder translation in the context of precisely `T.indices`. -/
theorem GeneratedRecursorTelescopeTranslation.indexMajorSplit
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    let outerDomains := T.params ++ T.motives ++ T.minors
    ∃ sourceSuffix sourceMajorSuffix,
      Expr.ForallTelescope source outerDomains.length sourceSuffix ∧
      Expr.ForallTelescope sourceSuffix T.indices.length sourceMajorSuffix ∧
      Expr.ForallTelescopeTypeTranslation env Us
        (abstractForallContext outerDomains []) sourceSuffix
        (T.indices ++ T.major).length
        (VExpr.wrapForalls (T.indices ++ T.major) T.result) ∧
      Expr.ForallTelescopeTypeTranslation env Us
        (abstractForallContext T.indices
          (abstractForallContext outerDomains []))
        sourceMajorSuffix T.major.length
        (VExpr.wrapForalls T.major T.result) := by
  let outerDomains := T.params ++ T.motives ++ T.minors
  rcases T.suffixTyped with ⟨sourceSuffix, HouterSource, Hsuffix⟩
  have HsuffixFull := Hsuffix
  have hsuffixArity : (T.indices ++ T.major).length =
      T.indices.length + T.major.length := List.length_append
  rw [hsuffixArity] at Hsuffix
  rcases Hsuffix.dropPrefix with
    ⟨indexDomains, sourceMajorSuffix, majorTarget, hindexLength,
      HindexSource, hsuffixTarget, Hmajor⟩
  have hindexDomains : indexDomains = T.indices := by
    apply VExpr.wrapForalls_prefix_domains_eq hindexLength
      (rfl : T.indices.length = T.indices.length)
    calc
      VExpr.wrapForalls indexDomains majorTarget =
          VExpr.wrapForalls (T.indices ++ T.major) T.result :=
        hsuffixTarget.symm
      _ = VExpr.wrapForalls (T.indices ++ T.major) T.result := rfl
  subst indexDomains
  have hmajorTarget : majorTarget = VExpr.wrapForalls T.major T.result := by
    apply VExpr.wrapForalls_left_cancel T.indices
    calc
      VExpr.wrapForalls T.indices majorTarget =
          VExpr.wrapForalls (T.indices ++ T.major) T.result :=
        hsuffixTarget.symm
      _ = VExpr.wrapForalls T.indices
          (VExpr.wrapForalls T.major T.result) := by
        simp [VExpr.wrapForalls_append]
  subst majorTarget
  exact ⟨sourceSuffix, sourceMajorSuffix, HouterSource, HindexSource,
    HsuffixFull, Hmajor⟩

def GeneratedRecursorTelescopeTranslation.mono
    (henv : env ≤ env')
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx) :
    GeneratedRecursorTelescopeTranslation env' Us source target
      numParams numMotives numMinors numIndices ownerIdx where
  params := T.params
  motives := T.motives
  minors := T.minors
  indices := T.indices
  major := T.major
  result := T.result
  target_eq := T.target_eq
  params_length := T.params_length
  motives_length := T.motives_length
  minors_length := T.minors_length
  indices_length := T.indices_length
  major_length := T.major_length
  typed := T.typed.mono henv
  residual := T.residual.mono henv

/-- The actual translated `.recInfo` emitted by production canonically
determines the five-group telescope certificate.  This contains no semantic
callback: it is obtained solely by inverting the retained executable
translation and the exact binder selections used by `declareRecursors`. -/
theorem GeneratedRecursorEntry.telescopeTranslation
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias) :
    Nonempty (GeneratedRecursorTelescopeTranslation env H.info.levelParams
      H.info.type entry.2.type stats.params.size
      (recInfos.map (·.motive)).size (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size ownerIdx) := by
  have Htranslated : TrExprS env H.info.levelParams [] H.info.type
      entry.2.type := by
    simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using H.translated.1.2.2
  have HrawTelescope := Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  rw [Hselections.residual_eq_concreteRecursorResult howner hnoalias] at HrawTelescope
  have Htelescope := HrawTelescope.inferImplicit_sameResidual (by rfl)
    1000 false
  rw [← H.type] at Htelescope
  have HtargetType : env.IsType H.info.levelParams.length [] entry.2.type :=
    TrExprS.isType_of_forallTelescope Htelescope (by omega) Htranslated
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope Htranslated HtargetType
  rcases TrExprS.forallTelescope_shape_with_context Htelescope Htranslated with
    ⟨domains, result, hdomainsLength, htarget, Hresult⟩
  rcases List.exists_append_five_of_length_eq domains stats.params.size
      (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size 1 hdomainsLength with
    ⟨params, motives, minors, indices, major, hdomains,
      hparams, hmotives, hminors, hindices, hmajor⟩
  refine ⟨⟨params, motives, minors, indices, major, result, ?_, hparams,
    hmotives, hminors, hindices, hmajor, Htyped, ?_⟩⟩
  · simpa [hdomains] using htarget
  · simpa [hdomains] using Hresult

/-- Pointwise five-group translation certificate for an entire generated
mutual recursor block. -/
def GeneratedRecursorTelescopeTranslations
    (env : VEnv) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (entries : List (ConstantInfo × VConstVal)) : Prop :=
  ∀ ownerIdx (hentry : ownerIdx < entries.length),
    ∃ info : RecursorVal,
      entries[ownerIdx].1 = .recInfo info ∧
      Nonempty (GeneratedRecursorTelescopeTranslation env info.levelParams
        info.type entries[ownerIdx].2.type stats.params.size
        (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx)

theorem GeneratedRecursorEntry.rulesRestoreTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (hparams : nparams = stats.params.size) :
    ∀ rule ∈ H.info.rules, RestoreTelescope rule.rhs nparams := by
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hctor : i < indTypes[ownerIdx]!.ctors.length := by
    rw [← H.rules.length]
    exact hi
  rcases H.rules.entry i hctor hi with ⟨Hrule⟩
  exact Hrule.rhsRestoreTelescope hparams

theorem RestoreTelescope.instantiate1'
    (H : RestoreTelescope e n) (arg : Expr) (depth : Nat) :
    RestoreTelescope (e.instantiate1' arg depth) n := by
  induction H generalizing depth with
  | done => exact .done
  | forallE H ih =>
    simp only [Expr.instantiate1']
    exact .forallE (ih (depth + 1))
  | lam H ih =>
    simp only [Expr.instantiate1']
    exact .lam (ih (depth + 1))

theorem RestoreTelescope.instantiate1
    (H : RestoreTelescope e n) (arg : Expr) :
    RestoreTelescope (e.instantiate1 arg) n := by
  rw [Expr.instantiate1_eq]
  exact H.instantiate1' arg 0


end VerifyInductive
end Lean4Lean
