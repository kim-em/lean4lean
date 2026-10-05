import Lean4Lean.Theory.Typing.Strong

/-!
Literal source Pi components retained through the original strong derivation.

The native case-template argument needs source-codomain observation transport,
in addition to the target Pi capabilities of whole-type adequacy. Its joint
induction must therefore retain the domain and codomain results of original
`forallEDF` children. Outer conversion does not erase this source information.

`SourcePiFormation` describes that recursive payload for a predicate `P`.
The theorem below checks its structural production for strong typing. It is
not the semantic fundamental theorem: that theorem must carry the analogous
payload in its induction motive, rather than recursively interpret the typing
proofs returned here as if they were new original induction children.
-/

namespace Lean4Lean.VEnv
open VExpr

/-- Formation information for every literal Pi component of a source term.
`P` may record a joint semantic result as well as its typing derivation. The
component sorts are their own sorts, not an asserted inversion of a converted
outer sort. -/
def SourcePiFormation (P : List VExpr → VExpr → VExpr → Prop)
    (Γ : List VExpr) : VExpr → Prop
  | .forallE A B =>
      (∃ u, P Γ A (.sort u)) ∧
      (∃ v, P (A :: Γ) B (.sort v)) ∧
      SourcePiFormation P Γ A ∧ SourcePiFormation P (A :: Γ) B
  | _ => True

namespace SourcePiFormation

theorem pi (hA : P Γ A (.sort u)) (hB : P (A :: Γ) B (.sort v))
    (pA : SourcePiFormation P Γ A) (pB : SourcePiFormation P (A :: Γ) B) :
    SourcePiFormation P Γ (.forallE A B) :=
  ⟨⟨u, hA⟩, ⟨v, hB⟩, pA, pB⟩

theorem domain (H : SourcePiFormation P Γ (.forallE A B)) :
    (∃ u, P Γ A (.sort u)) ∧ SourcePiFormation P Γ A :=
  ⟨H.1, H.2.2.1⟩

theorem codomain (H : SourcePiFormation P Γ (.forallE A B)) :
    (∃ v, P (A :: Γ) B (.sort v)) ∧ SourcePiFormation P (A :: Γ) B :=
  ⟨H.2.1, H.2.2.2⟩

/-- Read a generated telescope's source-domain capabilities at their exact
prefix contexts. These are retained payloads, not calls on newly generated
formation proofs. The tail keeps its own recursive Pi information, including
when a selected minor has a function-valued result. -/
theorem telescope (hroot : ∃ u, P Γ (wrapForalls domains body) (.sort u))
    (H : SourcePiFormation P Γ (wrapForalls domains body)) :
    (∀ j (hj : j < domains.length),
      (∃ u, P ((domains.take j).reverse ++ Γ) domains[j] (.sort u)) ∧
        SourcePiFormation P ((domains.take j).reverse ++ Γ) domains[j]) ∧
      (∃ u, P (domains.reverse ++ Γ) body (.sort u)) ∧
        SourcePiFormation P (domains.reverse ++ Γ) body := by
  induction domains generalizing Γ with
  | nil => exact ⟨fun j h => (Nat.not_lt_zero j h).elim, hroot, H⟩
  | cons d ds ih =>
    obtain ⟨hd, hb⟩ := ih H.codomain.1 H.codomain.2
    constructor
    · intro j hj
      cases j with
      | zero => simpa using H.domain
      | succ j =>
        simpa only [List.take_succ_cons, List.reverse_cons, List.singleton_append,
          List.append_assoc, List.getElem_cons_succ] using
          hd j (Nat.lt_of_succ_lt_succ hj)
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hb

private theorem const_apps :
    SourcePiFormation P Γ (mkApps (.const name levels) args) := by
  generalize he : mkApps (.const name levels) args = e
  cases e <;> try trivial
  exact (mkApps_ne_forallE (fn := .const name levels)
    (fun _ _ h => nomatch h) args he).elim

end SourcePiFormation

/-- Produce the literal-Pi formation trees of BOTH endpoints using only
original strong children. In particular, beta uses its explicit instantiated
term child, and native equations use their explicit endpoint typing children.
This needs neither environment well-formedness nor equality injectivity. -/
theorem IsDefEqStrong.sourcePiFormation
    (H : IsDefEqStrong env U Γ left right type) :
    SourcePiFormation (fun Γ e A => IsDefEqStrong env U Γ e e A) Γ left ∧
      SourcePiFormation (fun Γ e A => IsDefEqStrong env U Γ e e A) Γ right := by
  induction H with
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | forallEDF _ _ hA hB hB' ihA ihB ihB' =>
    exact ⟨.pi hA.hasType.1 hB.hasType.1 ihA.1 ihB.1,
      .pi hA.hasType.2 hB'.hasType.2 ihA.2 ihB'.2⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨trivial, ih.1⟩
  | eta _ _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ⟨trivial, ih.1⟩
  | proofIrrel _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.1⟩
  | extra _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.1⟩
  | elimIota _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.1⟩
  | projIota _ _ _ _ _ ih => exact ⟨trivial, ih.1⟩
  | structEta _ _ _ _ _ ih _ => exact ⟨SourcePiFormation.const_apps, ih.1⟩
  | unitLike _ _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.1⟩
  | bvar | sortDF | constDF | elimDF | appDF | projDF | lamDF => exact ⟨trivial, trivial⟩

end Lean4Lean.VEnv
