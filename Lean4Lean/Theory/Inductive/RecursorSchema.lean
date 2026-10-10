import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ConstructorMajor

/-! # The schema of a registered recursor

The data of a compiled declaration that the confluence development reads off a recursor
(section 4.2 of the design notes): the source families it owns, the generated signature and
the restoration table. On the verified-inductives branch this was the case-eliminator schema
(`CaseSchema`, with the per-family eliminator view); the ι pattern calculus has no abstract
eliminators, so only the three data fields remain.

`EquationBody` (the open body of a generated equation with its shared λ/∀ telescope) and the
closedness helpers of the telescope are here too; on the source branch they were part of the
case-reduction data. -/

namespace Lean4Lean.InductiveSignature

structure RecursorSchema where
  /-- Source families owned by this block, excluding auxiliary families. -/
  sourceFamilies : List Name
  signature : InductiveSignature
  restoration : Restoration

namespace RecursorSchema

/-- The source sort is specialized at the occurrence, independently of the
recursor's permitted elimination universe. -/
def sourceLevel (schema : RecursorSchema) (owner : Fin schema.signature.families.size)
    (levels : List VLevel) : VLevel :=
  schema.signature.families[owner].resultLevel.inst levels

/-- The open body of a generated equation, with its exact shared telescope. -/
structure EquationBody where
  domains : List VExpr
  lhs : VExpr
  rhs : VExpr
  type : VExpr

/-- Peel matching lambda binders and their forall type together. Mismatched
binder domains or telescope lengths are rejected. -/
def EquationBody.extract : VExpr → VExpr → VExpr → Option EquationBody
  | .lam domain lhs, .lam domain' rhs, .forallE domain'' type => do
    if domain ≠ domain' ∨ domain ≠ domain'' then none else
    let body ← extract lhs rhs type
    return { body with domains := domain :: body.domains }
  | .lam .., _, _ => none
  | lhs, rhs, type => some { domains := [], lhs, rhs, type }

/-- Extraction preserves both generated equation sides and their type. -/
theorem EquationBody.extract_sound {lhs rhs type : VExpr} {body : EquationBody}
    (h : EquationBody.extract lhs rhs type = some body) :
    VExpr.wrapLams body.domains body.lhs = lhs ∧
    VExpr.wrapLams body.domains body.rhs = rhs ∧
    VExpr.wrapForalls body.domains body.type = type := by
  induction lhs generalizing rhs type body with
  | lam domain lhs ihDomain ih =>
    cases rhs <;> cases type <;> simp [EquationBody.extract] at h
    obtain ⟨⟨rfl, rfl⟩, inner, hextract, rfl⟩ := h
    obtain ⟨hl, hr, ht⟩ := ih hextract
    simp [VExpr.wrapLams, VExpr.wrapForalls, ← hl, ← hr, ← ht]
  | _ => simp only [EquationBody.extract, Option.some.injEq] at h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- The extracted left body is not a λ. -/
theorem EquationBody.extracted_lhs_stripLams {lhs rhs type : VExpr} {body : EquationBody}
    (H : EquationBody.extract lhs rhs type = some body) :
    body.lhs.stripLams = body.lhs := by
  induction lhs generalizing rhs type body with
  | lam domain lhs ihDomain ih =>
    cases rhs <;> cases type <;> simp [EquationBody.extract] at H
    obtain ⟨⟨rfl, rfl⟩, inner, hi, rfl⟩ := H
    exact ih (body := inner) hi
  | _ => simp only [EquationBody.extract, Option.some.injEq] at H; cases H; rfl

end RecursorSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.VExpr

/-- An expression is the application of its head to its arguments. -/
theorem rebuild_spine (e : VExpr) :
    VExpr.mkApps e.getAppFnArgs.1 e.getAppFnArgs.2 = e := by
  suffices ∀ args, VExpr.mkApps (VExpr.getAppFnArgs.go e args).1
      (VExpr.getAppFnArgs.go e args).2 = VExpr.mkApps e args from this []
  induction e with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

theorem closed_wrapLams_body {domains : List VExpr} {body : VExpr} {k : Nat}
    (h : (VExpr.wrapLams domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapLams domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem closed_wrapForalls_body {domains : List VExpr} {body : VExpr} {k : Nat}
    (h : (VExpr.wrapForalls domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapForalls domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem closed_wrapForalls_domain {domains : List VExpr} {body : VExpr} {k i : Nat}
    (hc : (VExpr.wrapForalls domains body).ClosedN k)
    (hi : i < domains.length) : domains[i].ClosedN (k + i) := by
  induction domains generalizing k i with
  | nil => cases hi
  | cons domain domains ih =>
    cases i with
    | zero => exact hc.1
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih hc.2 (Nat.lt_of_succ_lt_succ hi)

/-- A scoped simultaneous substitution preserves the indicated scope. -/
theorem ClosedN.subst_closed {e : VExpr} {k n : Nat} {σ : Subst} (he : e.ClosedN k)
    (hσ : ∀ i < k, (σ i).ClosedN n) : (e.subst σ).ClosedN n := by
  induction e generalizing k n σ with (simp only [ClosedN, subst] at he ⊢)
  | bvar i => exact hσ i he
  | app _ _ ih1 ih2 => exact ⟨ih1 he.1 hσ, ih2 he.2 hσ⟩
  | proj _ _ _ ih => exact ih he hσ
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    refine ⟨ih1 he.1 hσ, ih2 he.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact (hσ i (by omega)).liftN

theorem ClosedN.wrapForalls_closed {domains : List VExpr} {body : VExpr} {n : Nat}
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapForalls domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

end Lean4Lean.VExpr
