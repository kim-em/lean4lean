import Lean4Lean.Theory.Typing.AnchoredOriginalPayload

/-! Literal lambda bodies retained from original Strong children.

The terminal body keeps its original assigned type, which may differ from a
converted outer telescope's declared result. This module intentionally does
not assert a codomain conversion obtained by Pi inversion.
-/
namespace Lean4Lean.VEnv
open VExpr

/-- Formation and typing along the literal lambda spine. -/
def SourceLamFormation (P : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) : VExpr → Prop
  | .lam A body =>
      (∃ u, P Γ A (.sort u)) ∧
      (∃ type, P (A :: Γ) body type) ∧
      SourceLamFormation P (A :: Γ) body
  | _ => True

namespace SourceLamFormation

theorem lam (domain : P Γ A (.sort u)) (body : P (A :: Γ) e type)
    (rest : SourceLamFormation P (A :: Γ) e) :
    SourceLamFormation P Γ (.lam A e) := ⟨⟨u, domain⟩, ⟨type, body⟩, rest⟩

/-- Peeling follows the actual syntax, so the final source context is exact.
The body type is existential; this is not inversion of a converted outer type. -/
theorem telescope (root : ∃ type, P Γ (wrapLams domains body) type)
    (tree : SourceLamFormation P Γ (wrapLams domains body)) :
    (∀ index (bound : index < domains.length),
      ∃ level, P ((domains.take index).reverse ++ Γ) domains[index] (.sort level)) ∧
    (∃ type, P (domains.reverse ++ Γ) body type) ∧
      SourceLamFormation P (domains.reverse ++ Γ) body := by
  induction domains generalizing Γ with
  | nil => exact ⟨fun _ bound => (Nat.not_lt_zero _ bound).elim, root, tree⟩
  | cons domain rest ih =>
    obtain ⟨hd, hb⟩ := ih tree.2.1 tree.2.2
    constructor
    · intro index bound
      cases index with
      | zero => simpa using tree.1
      | succ index =>
        simpa only [List.take_succ_cons, List.reverse_cons, List.singleton_append,
          List.append_assoc, List.getElem_cons_succ] using
          hd index (Nat.lt_of_succ_lt_succ bound)
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hb

end SourceLamFormation
end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- Additional original-child payload for a declaration-stage motive.
`OriginalPayload` supplies the semantic component stored at each lambda edge. -/
structure OriginalLambdaPayload (sourceEnv finalEnv : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) {Γ : List VExpr} {left right type : VExpr}
    (_original : IsDefEqStrong sourceEnv U Γ left right type) : Prop where
  leftFormation : SourceLamFormation (OriginalTypePayload sourceEnv finalEnv U registry) Γ left
  rightFormation : SourceLamFormation (OriginalTypePayload sourceEnv finalEnv U registry) Γ right

namespace OriginalLambdaPayload
variable {sourceEnv finalEnv : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

/-- All syntactically non-lambda endpoint cases have no lambda-spine data. -/
theorem of_nonLambda {H : IsDefEqStrong sourceEnv U Γ left right type}
    (leftNot : ∀ A body, left ≠ .lam A body)
    (rightNot : ∀ A body, right ≠ .lam A body) :
    OriginalLambdaPayload sourceEnv finalEnv U registry H := by
  constructor
  · cases left <;> try trivial
    exact (leftNot _ _ rfl).elim
  · cases right <;> try trivial
    exact (rightNot _ _ rfl).elim

theorem symm {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalLambdaPayload sourceEnv finalEnv U registry H) :
    OriginalLambdaPayload sourceEnv finalEnv U registry H.symm :=
  ⟨payload.rightFormation, payload.leftFormation⟩

theorem trans {H₁ : IsDefEqStrong sourceEnv U Γ left middle type}
    {H₂ : IsDefEqStrong sourceEnv U Γ middle right type}
    (first : OriginalLambdaPayload sourceEnv finalEnv U registry H₁)
    (second : OriginalLambdaPayload sourceEnv finalEnv U registry H₂) :
    OriginalLambdaPayload sourceEnv finalEnv U registry (H₁.trans H₂) :=
  ⟨first.leftFormation, second.rightFormation⟩

theorem defeqDF (hu : u.WF U)
    {HT : IsDefEqStrong sourceEnv U Γ A B (.sort u)}
    {He : IsDefEqStrong sourceEnv U Γ e e' A}
    (term : OriginalLambdaPayload sourceEnv finalEnv U registry He) :
    OriginalLambdaPayload sourceEnv finalEnv U registry (.defeqDF hu HT He) :=
  ⟨term.leftFormation, term.rightFormation⟩

theorem lamDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A' (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HB' : IsDefEqStrong sourceEnv U (A' :: Γ) B B (.sort v)}
    {He : IsDefEqStrong sourceEnv U (A :: Γ) e e' B}
    {He' : IsDefEqStrong sourceEnv U (A' :: Γ) e e' B}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (body : OriginalPayload sourceEnv finalEnv U registry He)
    (body' : OriginalPayload sourceEnv finalEnv U registry He')
    (tree : OriginalLambdaPayload sourceEnv finalEnv U registry He)
    (tree' : OriginalLambdaPayload sourceEnv finalEnv U registry He') :
    OriginalLambdaPayload sourceEnv finalEnv U registry (.lamDF hu hv HA HB HB' He He') :=
  ⟨.lam (domain.leftType henv hscoped) (body.leftType henv hscoped) tree.leftFormation,
    .lam (domain.rightType henv hscoped) (body'.rightType henv hscoped) tree'.rightFormation⟩

theorem beta (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {He : IsDefEqStrong sourceEnv U (A :: Γ) e e B}
    {Ha : IsDefEqStrong sourceEnv U Γ a a A}
    {HBa : IsDefEqStrong sourceEnv U Γ (B.inst a) (B.inst a) (.sort v)}
    {Hea : IsDefEqStrong sourceEnv U Γ (e.inst a) (e.inst a) (B.inst a)}
    (instantiated : OriginalLambdaPayload sourceEnv finalEnv U registry Hea) :
    OriginalLambdaPayload sourceEnv finalEnv U registry (.beta hu hv HA HB He Ha HBa Hea) :=
  ⟨trivial, instantiated.leftFormation⟩

/-- Eta's new body is an application of two original children. Its semantic
payload is assembled by the closed app/bvar rules, never by an adequacy call
on the newly assembled raw application proof. -/
theorem eta (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HBlift : IsDefEqStrong sourceEnv U (A.lift :: A :: Γ) (B.liftN 1 1) (B.liftN 1 1) (.sort v)}
    {He : IsDefEqStrong sourceEnv U Γ e e (.forallE A B)}
    {Helift : IsDefEqStrong sourceEnv U (A :: Γ) e.lift e.lift (.forallE A.lift (B.liftN 1 1))}
    {HAlift : IsDefEqStrong sourceEnv U (A :: Γ) A.lift A.lift (.sort u)}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (bodyType : OriginalPayload sourceEnv finalEnv U registry HB)
    (liftedBodyType : OriginalPayload sourceEnv finalEnv U registry HBlift)
    (liftedTerm : OriginalPayload sourceEnv finalEnv U registry Helift)
    (liftedDomain : OriginalPayload sourceEnv finalEnv U registry HAlift)
    (term : OriginalLambdaPayload sourceEnv finalEnv U registry He) :
    OriginalLambdaPayload sourceEnv finalEnv U registry (.eta hu hv HA HB HBlift He Helift HAlift) := by
  have lookup : Lookup (A :: Γ) 0 A.lift := .zero
  have rawVariable := IsDefEqStrong.bvar lookup hu HAlift
  have result : IsDefEqStrong sourceEnv U (A :: Γ)
      ((B.liftN 1 1).inst (.bvar 0)) ((B.liftN 1 1).inst (.bvar 0)) (.sort v) := by
    simpa only [inst_liftN_bvar] using HB
  have raw : IsDefEqStrong sourceEnv U (A :: Γ) (.app e.lift (.bvar 0))
      (.app e.lift (.bvar 0)) B := by
    simpa only [inst_liftN_bvar] using
      IsDefEqStrong.appDF hu hv HAlift HBlift Helift rawVariable result
  have resultJoint : GradedJoint finalEnv U registry (A :: Γ)
      ((B.liftN 1 1).inst (.bvar 0)) ((B.liftN 1 1).inst (.bvar 0)) (.sort v) := by
    simpa only [inst_liftN_bvar] using bodyType.joint
  have joint : GradedJoint finalEnv U registry (A :: Γ)
      (.app e.lift (.bvar 0)) (.app e.lift (.bvar 0)) B := by
    simpa only [inst_liftN_bvar] using
      GradedJoint.appDF henv hscoped liftedDomain.joint liftedBodyType.joint liftedTerm.joint
        (GradedJoint.bvar henv hscoped lookup liftedDomain.joint) resultJoint
        (HAlift.defeq.mono hle) (HBlift.defeq.mono hle) (rawVariable.defeq.mono hle)
  exact ⟨.lam (domain.leftType henv hscoped) ⟨raw, joint⟩ trivial, term.leftFormation⟩

theorem proofIrrel
    {HP : IsDefEqStrong sourceEnv U Γ P P (.sort .zero)}
    {Hp : IsDefEqStrong sourceEnv U Γ p p P}
    {Hq : IsDefEqStrong sourceEnv U Γ q q P}
    (left : OriginalLambdaPayload sourceEnv finalEnv U registry Hp)
    (right : OriginalLambdaPayload sourceEnv finalEnv U registry Hq) :
    OriginalLambdaPayload sourceEnv finalEnv U registry (.proofIrrel HP Hp Hq) :=
  ⟨left.leftFormation, right.leftFormation⟩

end OriginalLambdaPayload
end Lean4Lean.AnchoredSource.Adapted
