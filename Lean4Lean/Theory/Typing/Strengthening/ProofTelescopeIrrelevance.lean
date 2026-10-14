import Lean4Lean.Theory.Typing.Strengthening.SingletonTransportedOccurrence

/-! # Proof irrelevance through a dependent proposition telescope

Any two typed instances of a telescope consisting of propositions induce equal
substitutions. The telescope may depend on an arbitrary well-formed base context.
This compares extracted singleton witnesses with the old aligned witnesses.
-/
namespace Lean4Lean.VEnv
open VExpr

/-- Every domain is a proposition in the context of its predecessors. -/
inductive PropTelescope (env : VEnv) (U : Nat) (Γ : List VExpr) : List VExpr → Prop where
  | nil : PropTelescope env U Γ []
  | snoc : PropTelescope env U Γ ds → HasType env U (ds.reverse ++ Γ) d (.sort .zero) →
      PropTelescope env U Γ (ds ++ [d])

/-- A proposition telescope extends any well-formed base context. -/
theorem PropTelescope.wf (H : PropTelescope env U Γ ds) (hΓ : OnCtx Γ (env.IsType U)) :
    OnCtx (ds.reverse ++ Γ) (env.IsType U) := by
  induction H with
  | nil => exact hΓ
  | snoc _ hd ih =>
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
    exact ⟨ih, _, hd⟩

/-- Two typed proof-telescope instances give a common typed substitution.
Earlier proof equalities align the next domains before proof irrelevance is used. -/
theorem PropTelescope.substEq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : PropTelescope env U Γ ds) (ha : TelInst env U Γ ds args)
    (hb : TelInst env U Γ ds args') :
    Ctx.SubstEq env U Γ (Subst.ofList args) (Subst.ofList args') (ds.reverse ++ Γ) := by
  induction H generalizing args args' with
  | nil =>
    have h1 : args = [] := List.eq_nil_of_length_eq_zero ha.1
    have h2 : args' = [] := List.eq_nil_of_length_eq_zero hb.1
    subst args; subst args'
    exact Ctx.SubstEq.id henv.ordered hΓ
  | @snoc ds d H hd ih =>
    obtain ⟨as, a, rfl⟩ : ∃ as a, args = as ++ [a] := by
      rcases List.eq_nil_or_concat args with rfl | ⟨as, a, h⟩
      · have := ha.1; simp at this
      · exact ⟨as, a, by simpa using h⟩
    obtain ⟨bs, b, rfl⟩ : ∃ bs b, args' = bs ++ [b] := by
      rcases List.eq_nil_or_concat args' with rfl | ⟨bs, b, h⟩
      · have := hb.1; simp at this
      · exact ⟨bs, b, by simpa using h⟩
    have hla : as.length = ds.length := by have := ha.1; simpa using this
    have hlb : bs.length = ds.length := by have := hb.1; simpa using this
    have ha0 : TelInst env U Γ ds as := by
      have := ha.take (doms := ds) (more := [d]); simpa only [List.take_left' hla] using this
    have hb0 : TelInst env U Γ ds bs := by
      have := hb.take (doms := ds) (more := [d]); simpa only [List.take_left' hlb] using this
    have W := ih ha0 hb0
    have hdd := IsDefEq.substDF henv.orderedStrong (H.wf hΓ) hΓ W hd
    simp only [← instOuter_eq_subst, instOuter_sort] at hdd
    have hat : env.HasType U Γ a (d.instOuter as) := by
      have := ha.getD (j := ds.length) (by simp)
      rw [getD_append_right' (by omega), getD_append_right' (Nat.le_refl _),
        show ds.length - as.length = 0 by omega, Nat.sub_self, List.getD_cons_zero, List.take_left' hla] at this
      exact this
    have hbt : env.HasType U Γ b (d.instOuter bs) := by
      have := hb.getD (j := ds.length) (by simp)
      rw [getD_append_right' (by omega), getD_append_right' (Nat.le_refl _),
        show ds.length - bs.length = 0 by omega, Nat.sub_self, List.getD_cons_zero, List.take_left' hlb] at this
      exact this
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
    apply Ctx.SubstEq.cons
    · simpa only [Subst.ofList_snoc_tail] using W
    · exact hd
    · simpa only [Subst.ofList_snoc_head, Subst.ofList_snoc_tail, ← instOuter_eq_subst] using
        IsDefEq.proofIrrel hdd.hasType.1 hat (hdd.symm.defeq hbt)

/-- Every typed expression under proof binders has the same instantiated value
at any two typed witness lists. -/
theorem PropTelescope.instOuter_eq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : PropTelescope env U Γ ds) (ha : TelInst env U Γ ds args)
    (hb : TelInst env U Γ ds args') (he : env.HasType U (ds.reverse ++ Γ) e T) :
    env.IsDefEq U Γ (e.instOuter args) (e.instOuter args') (T.instOuter args) := by
  simpa only [← instOuter_eq_subst] using
    IsDefEq.substDF henv.orderedStrong (H.wf hΓ) hΓ (H.substEq henv hΓ ha hb) he

end Lean4Lean.VEnv

namespace Lean4Lean.SingletonLayout
open VExpr VEnv
variable {S : SingletonLayout}

/-- The entire generated cast telescope is propositional at arbitrary indices. -/
theorem tel_propTelescope (henv : env.WF) (heq : env.HasCanonicalEq)
    (T : S.Typed env U params) (hΓ : OnCtx Γ (env.IsType U))
    (hpa : TelInst env U Γ params pa)
    (hia : TelInst env U Γ (params ++ S.indices) (pa ++ ia))
    (hialen : ia.length = S.indices.length) : ∀ i, i ≤ S.fields.length →
      PropTelescope env U Γ (S.tel pa ia i).1 := by
  intro i
  induction i with
  | zero => intro _; exact .nil
  | succ i ih =>
    intro hi
    exact .snoc (ih (Nat.le_of_succ_le hi)) (step_domain_prop henv heq T hΓ hpa hia hialen hi)

end Lean4Lean.SingletonLayout
