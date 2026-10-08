import Lean4Lean.Theory.VExpr

/-! Pure telescope and application-spine syntax, below environments and typing. -/

namespace Lean4Lean

/-- Split exactly `n` leading forall binders, retaining domains in outermost to
innermost order. -/
def VExpr.takeForalls : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE dom body => do
    let (doms, result) ← body.takeForalls n
    return (dom :: doms, result)
  | _ + 1, _ => none

/-- Head and left-to-right arguments of an application spine. -/
def VExpr.getAppFnArgs (e : VExpr) : VExpr × List VExpr :=
  go e []
where
  go : VExpr → List VExpr → VExpr × List VExpr
    | .app fn arg, args => go fn (arg :: args)
    | fn, args => (fn, args)

def VExpr.wrapLams (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .lam body

def VExpr.wrapForalls (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .forallE body

@[simp] theorem VExpr.instL_wrapForalls (ds : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapForalls ds body).instL ls =
      VExpr.wrapForalls (ds.map (·.instL ls)) (body.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.instL, List.map_cons] at ih ⊢
    rw [ih]

theorem VExpr.takeForalls_eq_wrapForalls :
    ∀ {n : Nat} {type result : VExpr} {domains : List VExpr},
      type.takeForalls n = some (domains, result) →
      type = VExpr.wrapForalls domains result ∧ domains.length = n
  | 0, type, result, domains, H => by
    cases Option.some.inj H
    exact ⟨rfl, rfl⟩
  | n + 1, type, result, domains, H => by
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls n with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rw [VExpr.takeForalls, htail] at H
        cases Option.some.inj H
        have ih := VExpr.takeForalls_eq_wrapForalls htail
        exact ⟨congrArg (VExpr.forallE domain) ih.1, by simp [ih.2]⟩
    | bvar | sort | const | elim | app | lam | proj => simp [VExpr.takeForalls] at H

/-- Telescopes of the same length are equal only if their domains and bodies are. -/
theorem VExpr.wrapForalls_inj_of_length :
    ∀ {ds ds' : List VExpr} {b b' : VExpr}, ds.length = ds'.length →
      VExpr.wrapForalls ds b = VExpr.wrapForalls ds' b' → ds = ds' ∧ b = b'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, hl, h => by
    injection h with h1 h2
    have := VExpr.wrapForalls_inj_of_length (by simpa using hl) h2
    exact ⟨by rw [h1, this.1], this.2⟩

end Lean4Lean
