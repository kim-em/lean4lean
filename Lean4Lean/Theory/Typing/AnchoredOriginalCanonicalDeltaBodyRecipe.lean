import Lean4Lean.Theory.Typing.AnchoredRecipePiSemantics
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaCoherence
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth

/-! A dependent row recipe retains the whole canonical type query. Its local
argument is a real finite binder demand; opening the canonical child and pure
Pi elimination do not recursively interpret a larger caller Pi derivation. -/


namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Resource-connected row elimination works under an arbitrary dependent
source context and paired tail realizations. This is the recursive body step
for a finite recipe, independent of which canonical root produced `whole`. -/
theorem TypeRelated.literalPiRowFromFrame
    {n : Nat} {key : Key n} {result ambient : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U (A :: source)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ (A :: source))
    (whole : TypeRelated env U registry target
      ((VExpr.forallE A B).subst σ.tail) ((VExpr.forallE A B).subst τ.tail)
      (.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows)
    (resource : (⟨n, key.input⟩ : Need) ∈ available 0)
    (anchor : key.anchor = σ 0) :
    TypeRelated env U registry target (B.subst σ) (B.subst τ) result := by
  obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed resource (Lookup.zero (Γ := source) (ty := A))
  have raw := substitutions.lookup (Lookup.zero (Γ := source) (ty := A))
  have paired := entry.related
  rw [lift_subst] at raw paired
  have output := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
    (by simpa only [subst] using whole) member anchor raw
    (show Related env U registry target (σ 0) (τ 0) (A.subst σ.tail) key.input entry.support from paired)
  have leftEq : σ.tail.cons (σ 0) = σ := by funext i; cases i <;> rfl
  have rightEq : τ.tail.cons (τ 0) = τ := by funext i; cases i <;> rfl
  simpa only [inst_lift_cons, leftEq, rightEq] using output

structure CanonicalDeltaBodyRecipe (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env) (domain body : VExpr)
    (key : Key n) (result : Profile n) where
  relevant : Bool
  prototypeDomain : VExpr
  prototypeBody : VExpr
  support : Profile n
  rows : List (Key n × Profile n)
  parent : CanonicalDeltaTypePacket env U registry target strata (.forallE domain body)
    relevant (.pi prototypeDomain prototypeBody support rows)
  selected : (key, result) ∈ rows

namespace CanonicalDeltaBodyRecipe
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {domain body : VExpr} {key : Key n} {result : Profile n}

noncomputable def depth
    (recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result) : Nat → Nat :=
  recipe.parent.chargeDepth

theorem formed (recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result) :
    result.HasType (.sort recipe.relevant) :=
  (Profile.HasType.pi_iff.mp recipe.parent.formed).2 key result recipe.selected

theorem closed (recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result) :
    domain.Closed ∧ body.ClosedN 1 := by
  change (VExpr.forallE domain body).Closed
  rw [recipe.parent.expressionEq]
  exact recipe.parent.typeClosed.instL

def need (_recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result) : Need :=
  ⟨n, key.input⟩

def footprint (recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result) : Footprint :=
  [(0, recipe.need)]

private theorem subst_head {expression : VExpr} (scope : expression.ClosedN 1) (σ : Subst) :
    expression.subst σ = expression.inst (σ 0) := by
  rw [inst_eq]
  apply subst_congr_closedN scope
  intro i hi
  have same : i = 0 := by omega
  subst i
  rfl

/-- Interpret the finite head need from the actual paired frame. The packet
supplies the closed whole-Pi capability; all argument evidence comes from the
same lookup witness and actual raw substitution. -/
theorem relatedFromFrame
    (recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE domain body) (.forallE domain body)
      (.pi recipe.prototypeDomain recipe.prototypeBody recipe.support recipe.rows))
    {context : ContextDerivation sourceEnv U (domain :: source)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ (domain :: source))
    (resources : recipe.footprint.Available available)
    (anchor : key.anchor = σ 0) :
    TypeRelated env U registry target (body.subst σ) (body.subst τ) result := by
  have member : recipe.need ∈ available 0 := resources 0 recipe.need (List.mem_singleton_self _)
  obtain ⟨entry, _⟩ := frame.lookup_allDepth henv formed member (.zero (Γ := source) (ty := domain))
  have raw := substitutions.lookup (Lookup.zero (Γ := source) (ty := domain))
  have paired := entry.related
  have domainEq : domain.lift.subst σ = domain := by
    rw [recipe.closed.1.lift_eq, recipe.closed.1.subst_eq .zero]
  rw [domainEq] at raw paired
  have output := TypeRelated.literalPiRowFromBinder henv hscoped formed whole recipe.selected
    anchor raw (show Related env U registry target (σ 0) (τ 0) domain key.input entry.support from paired)
  simpa only [subst_head recipe.closed.2] using output

/-- Canonical opening and body elimination are fused. The sole recursive
call is on the retained canonical formation at its computed empty-frame cost;
the actual caller body only contributes its finite paired binder resource. -/
theorem interpret
    (recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (bounded : EquationStratifiedFuel.WithinAbove cutoff fuel recipe.depth)
    (lower : recipe.parent.CodeBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    {context : ContextDerivation sourceEnv U (domain :: source)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ (domain :: source))
    (resources : recipe.footprint.Available available)
    (anchor : key.anchor = σ 0) :
    TypeRelated env U registry target (body.subst σ) (body.subst τ) result := by
  have whole := recipe.parent.interpret henv hscoped formed cutoff cutoffBound fuel
    constants callerSchedule bounded lower .id .id
  simp only [subst_id] at whole
  exact recipe.relatedFromFrame henv hscoped formed whole frame substitutions resources anchor

end CanonicalDeltaBodyRecipe

/-- The body endpoint remains an independent original occurrence. Only its
literal domain/body syntax and finite head resource match the stored recipe;
the destination need not retain or descend from the packet's parent proof. -/
structure CanonicalDeltaBodyAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env)
    (node : EndpointState sourceEnv U (domain :: source) body (.sort level))
    (locals : List Nat) (σ : Subst) (key : Key n) (result : Profile n) where
  recipe : CanonicalDeltaBodyRecipe env U registry target strata domain body key result
  localHead : 0 ∈ locals
  anchor : key.anchor = σ 0

def CanonicalDeltaBodyAt.reindex
    {node : EndpointState sourceEnv U (domain :: source) body (.sort level)}
    (query : CanonicalDeltaBodyAt sourceEnv env U registry target strata node locals σ key result)
    (destination : EndpointState destinationEnv U (domain :: destinationSource) body (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst)
    (localHead : 0 ∈ destinationLocals) (anchor : key.anchor = destinationSubst 0) :
    CanonicalDeltaBodyAt destinationEnv env U registry target strata destination
      destinationLocals destinationSubst key result :=
  ⟨query.recipe, localHead, anchor⟩

theorem CanonicalDeltaBodyAt.reindex_recipe
    {node : EndpointState sourceEnv U (domain :: source) body (.sort level)}
    (query : CanonicalDeltaBodyAt sourceEnv env U registry target strata node locals σ key result)
    (destination : EndpointState destinationEnv U (domain :: destinationSource) body (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst)
    (localHead : 0 ∈ destinationLocals) (anchor : key.anchor = destinationSubst 0) :
    (query.reindex destination destinationLocals destinationSubst localHead anchor).recipe = query.recipe := rfl

/-- Row extraction adds a real head resource but retains the complete
charged canonical packet, including every domain and body query in it. -/
def CanonicalDeltaTypeAt.piBody
    {node : EndpointState sourceEnv U source (.forallE domain body) (.sort level)}
    (query : CanonicalDeltaTypeAt sourceEnv env U registry target strata node locals σ relevant
      (.pi prototypeDomain prototypeBody support rows))
    (member : (key, result) ∈ rows)
    (destination : EndpointState destinationEnv U (domain :: destinationSource) body (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst)
    (localHead : 0 ∈ destinationLocals) (anchor : key.anchor = destinationSubst 0) :
    CanonicalDeltaBodyAt destinationEnv env U registry target strata destination
      destinationLocals destinationSubst key result :=
  ⟨⟨relevant, prototypeDomain, prototypeBody, support, rows, query.packet, member⟩, localHead, anchor⟩

theorem CanonicalDeltaTypeAt.piBody_depth
    {node : EndpointState sourceEnv U source (.forallE domain body) (.sort level)}
    (query : CanonicalDeltaTypeAt sourceEnv env U registry target strata node locals σ relevant
      (.pi prototypeDomain prototypeBody support rows))
    (member : (key, result) ∈ rows)
    (destination : EndpointState destinationEnv U (domain :: destinationSource) body (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst)
    (localHead : 0 ∈ destinationLocals) (anchor : key.anchor = destinationSubst 0) :
    (query.piBody member destination destinationLocals destinationSubst localHead anchor).recipe.depth =
      query.packet.chargeDepth := rfl

theorem CanonicalDeltaBodyAt.reindex_depth
    {node : EndpointState sourceEnv U (domain :: source) body (.sort level)}
    (query : CanonicalDeltaBodyAt sourceEnv env U registry target strata node locals σ key result)
    (destination : EndpointState destinationEnv U (domain :: destinationSource) body (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst)
    (localHead : 0 ∈ destinationLocals) (anchor : key.anchor = destinationSubst 0) :
    (query.reindex destination destinationLocals destinationSubst localHead anchor).recipe.depth = query.recipe.depth := rfl

end Lean4Lean.AnchoredSource.Adapted
