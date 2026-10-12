import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.HeadInversion

/-! # The observation model as a tool for context strengthening (route B)

The glued observation model (`Theory/Typing/HeadInjectivity/Model/`) interprets a term `t` of a
source context `Γ` by its set of observations `Obs env U Δ σ S t` in a *target* context `Δ`,
under an anchor substitution `σ : Γ → Δ` and observation sets `S` for the variables. The
model is sound for every well-formed environment (`VEnv.WF.soundEnv`). This file states what
soundness says about a lifted equation `Q :: Γ ⊢ a↑ ≡ b↑`, as a statement about `a` and `b`
as terms of `Γ`.

* `KEq env U Γ a b`: the observations of `a` and `b` agree (mutual subsumption) in every
  well-formed target, at every typed anchor and typed observation sets. Sound (`KEq.sound`),
  an equivalence, and blind to proofs (`KEq.proofs`: two proofs of two propositions are
  `KEq`-related whatever the propositions, so no reflection of `KEq` can recover a typing).
* `KEqOn env U Γ P a b`: the same restricted to the targets and anchors satisfying `P`.
* **Source-lift invariance** (`KEq.lift_iff`): `KEq (Q :: Γ) a↑ b↑` is exactly
  `KEqOn Γ (fun Δ σ => ∃ q, Δ ⊢ q : Q.subst σ) a b`, agreement in the targets in which the
  removed binder's type is inhabited. The model never reads the source context: the
  observations of `a↑` under `(σ.cons q, S.cons X)` are those of `a` under `(σ, S)`
  (`Obs.lift_cons_iff`), and conversely every anchor for `Q :: Γ` is an anchor for `Γ` with an
  inhabitant of `Q`. So the lifted equation says nothing about the target `Δ = Γ` itself when
  `Q` is uninhabited there, and the semantic form of strengthening is the passage from
  inhabited targets to all targets (`ModelStrengthening`).

The companion files: `ModelDescent.lean` (what the inhabited targets do give: head shapes
through same-target extraction, with the exact residue at proofs) and `ModelObstruction.lean`
(`KeyFaithful ↔ TypedFront`: descending the model's declarative classes from `Q :: Γ` to `Γ` is
the fixed-type strengthening statement itself; and the refutation of unrestricted reflection
by two fresh axioms of a fresh type, so reflection of observations cannot replace it). -/

namespace Lean4Lean
namespace VEnv.StrengtheningModel
open VEnv _root_.Lean4Lean.VExpr VEnv.Model

variable {env : VEnv} {U : Nat}

/-- All well-formed targets, all typed anchors, and all backed, typed variable
observations. Equality here is mutual subsumption, not equality of raw sets. -/
def KEq (env : VEnv) (U : Nat) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∀ (Δ : List VExpr) (σ : VExpr.Subst) (S : ObSets),
    OnCtx Δ (env.IsType U) → Ctx.SubstEq env U Δ σ σ Γ →
    TV env U Δ Γ σ S →
    Ob.Sub (Obs env U Δ σ S a) (Obs env U Δ σ S b) ∧
    Ob.Sub (Obs env U Δ σ S b) (Obs env U Δ σ S a)

/-- `KEq` restricted to the targets and anchors satisfying `P`. -/
def KEqOn (env : VEnv) (U : Nat) (Γ : List VExpr) (P : List VExpr → VExpr.Subst → Prop)
    (a b : VExpr) : Prop :=
  ∀ (Δ : List VExpr) (σ : VExpr.Subst) (S : ObSets),
    OnCtx Δ (env.IsType U) → Ctx.SubstEq env U Δ σ σ Γ → P Δ σ →
    TV env U Δ Γ σ S →
    Ob.Sub (Obs env U Δ σ S a) (Obs env U Δ σ S b) ∧
    Ob.Sub (Obs env U Δ σ S b) (Obs env U Δ σ S a)

theorem KEq.toOn (H : KEq env U Γ a b) (P : List VExpr → VExpr.Subst → Prop) :
    KEqOn env U Γ P a b := fun Δ σ S hΔ hσ _ hS => H Δ σ S hΔ hσ hS

theorem KEqOn.toKEq (H : KEqOn env U Γ (fun _ _ => True) a b) : KEq env U Γ a b :=
  fun Δ σ S hΔ hσ hS => H Δ σ S hΔ hσ trivial hS

/-- Soundness: a definitional equality gives agreement of observations in every target. -/
theorem KEq.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEqU U Γ a b) :
    KEq env U Γ a b := by
  obtain ⟨T, H⟩ := H
  intro Δ σ S hΔ hσ hS
  have Hs := (henv.soundEnv hΔ (H.strong henv.orderedStrong hΓ)).1 σ σ S hσ hS hS
  exact ⟨Hs.1, Hs.2.1⟩

theorem KEq.symm (H : KEq env U Γ a b) : KEq env U Γ b a :=
  fun Δ σ S hΔ hσ hS => (H Δ σ S hΔ hσ hS).symm

theorem KEq.trans (H : KEq env U Γ a b) (H' : KEq env U Γ b c) : KEq env U Γ a c := by
  intro Δ σ S hΔ hσ hS
  have h := H Δ σ S hΔ hσ hS
  have h' := H' Δ σ S hΔ hσ hS
  exact ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem KEqOn.symm (H : KEqOn env U Γ P a b) : KEqOn env U Γ P b a :=
  fun Δ σ S hΔ hσ hP hS => (H Δ σ S hΔ hσ hP hS).symm

theorem KEqOn.trans (H : KEqOn env U Γ P a b) (H' : KEqOn env U Γ P b c) :
    KEqOn env U Γ P a c := by
  intro Δ σ S hΔ hσ hP hS
  have h := H Δ σ S hΔ hσ hP hS
  have h' := H' Δ σ S hΔ hσ hP hS
  exact ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-! ## Proofs have no observations -/

/-- A proof of a proposition has no observation, in any target and at any valuation: its
observations would be typed at observations of a proposition, which are typed at `sort 0`
only (`TypedOb.not_prop`). -/
theorem proof_no_observations (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hP : env.HasType U Γ P (.sort .zero))
    (ha : env.HasType U Γ a P) (hΔ : OnCtx Δ (env.IsType U))
    (hσ : Ctx.SubstEq env U Δ σ σ Γ) (hS : TV env U Δ Γ σ S) :
    ∀ o, ¬ Obs env U Δ σ S a o := by
  have ihP := (henv.soundEnv hΔ (hP.strong henv.orderedStrong hΓ)).1 σ σ S hσ hS hS
  have iha := (henv.soundEnv hΔ (ha.strong henv.orderedStrong hΓ)).1 σ σ S hσ hS hS
  intro o ho
  obtain ⟨τs, hτs, ht⟩ := iha.2.2.1 o ho
  exact ht.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (ihP.2.2.1 τ (hτs τ hτ))⟩

/-- `KEq` forgets the propositions of proofs: two proofs of two propositions are related.
A reflection principle for `KEq` must therefore carry a common type. -/
theorem KEq.proofs (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hP : env.HasType U Γ P (.sort .zero))
    (hQ : env.HasType U Γ Q (.sort .zero))
    (ha : env.HasType U Γ a P) (hb : env.HasType U Γ b Q) : KEq env U Γ a b := by
  intro Δ σ S hΔ hσ hS
  exact ⟨fun o ho => (proof_no_observations henv hΓ hP ha hΔ hσ hS o ho).elim,
    fun o ho => (proof_no_observations henv hΓ hQ hb hΔ hσ hS o ho).elim⟩

/-! ## Source-lift invariance

The model reads the source context only through the anchor and the observation sets. -/

/-- The anchor of an extended source context is an anchor of the context with an inhabitant
of the new binder's type. -/
theorem substEq_cons_inv (W : Ctx.SubstEq env U Δ σ σ' (Q :: Γ)) :
    Ctx.SubstEq env U Δ σ.tail σ'.tail Γ ∧ env.IsDefEq U Δ σ.head σ'.head (Q.subst σ.tail) := by
  cases W with
  | cons W _ h => exact ⟨W, h⟩

theorem subst_cons_tail_head (σ : VExpr.Subst) : σ.tail.cons σ.head = σ := by
  funext i; cases i <;> rfl

theorem obSets_cons_tail_head (S : ObSets) : ObSets.cons (fun i => S (i + 1)) (S 0) = S := by
  funext i; cases i <;> rfl

/-- Extending an anchor for `Γ` by an inhabitant of `Q.subst σ` gives an anchor for `Q :: Γ`. -/
theorem substEq_cons (hΓ : OnCtx (Q :: Γ) (env.IsType U)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (hq : env.HasType U Δ q (Q.subst σ)) :
    Ctx.SubstEq env U Δ (σ.cons q) (σ.cons q) (Q :: Γ) := by
  obtain ⟨_, u, hQ⟩ := hΓ
  refine .cons ?_ hQ ?_
  · rw [VExpr.Subst.cons_tail]; exact W
  · rw [VExpr.Subst.cons_tail, VExpr.Subst.cons_head]; exact hq

/-- A typed valuation for `Γ` extends by the empty observation set to a typed valuation for
`Q :: Γ` at an extended anchor: the lifted types' observations and classes are those of the
types below. -/
theorem tv_cons_empty (hS : TV env U Δ Γ σ S) (q : VExpr) :
    TV env U Δ (Q :: Γ) (σ.cons q) (S.cons (fun _ => False)) := by
  refine ⟨fun i => ?_, fun i A hL o ho => ?_⟩
  · cases i with
    | zero => intro o h; exact h.elim
    | succ i => exact hS.1 i
  · cases hL with
    | zero => exact ho.elim
    | @succ _ i A _ hL =>
      obtain ⟨τs, hτs, ht⟩ := hS.2 i A hL o ho
      refine ⟨τs, fun τ hτ => Obs.lift_cons_iff.2 (hτs τ hτ), ?_⟩
      have e : vcls env U Δ (σ.cons q) (.bvar (i + 1)) A.lift = vcls env U Δ σ (.bvar i) A := by
        simp only [vcls, lift_subst_cons]; rfl
      rw [e]; exact ht

/-- A typed valuation for `Q :: Γ` restricts to a typed valuation for `Γ`. -/
theorem tv_tail (hS : TV env U Δ (Q :: Γ) σ S) :
    TV env U Δ Γ σ.tail (fun i => S (i + 1)) := by
  refine ⟨fun i => hS.1 (i + 1), fun i A hL o ho => ?_⟩
  obtain ⟨τs, hτs, ht⟩ := hS.2 (i + 1) A.lift (.succ hL) o ho
  refine ⟨τs, fun τ hτ => ?_, ?_⟩
  · have := hτs τ hτ
    rwa [← subst_cons_tail_head σ, ← obSets_cons_tail_head S, Obs.lift_cons_iff] at this
  · have e : vcls env U Δ σ (.bvar (i + 1)) A.lift = vcls env U Δ σ.tail (.bvar i) A := by
      simp only [vcls]
      rw [← subst_cons_tail_head σ, lift_subst]; rfl
    rwa [e] at ht

/-- The inhabitation condition on a target: the removed binder's type has an inhabitant there. -/
def Inhabits (env : VEnv) (U : Nat) (Q : VExpr) (Δ : List VExpr) (σ : VExpr.Subst) : Prop :=
  ∃ q, env.HasType U Δ q (Q.subst σ)

/-- **Source-lift invariance.** The lifted equation's semantic content is agreement of the
observations of `a` and `b` in exactly the targets where `Q` is inhabited. -/
theorem KEq.lift_iff (hΓ : OnCtx (Q :: Γ) (env.IsType U)) :
    KEq env U (Q :: Γ) a.lift b.lift ↔ KEqOn env U Γ (Inhabits env U Q) a b := by
  constructor
  · intro H Δ σ S hΔ hσ ⟨q, hq⟩ hS
    have h := H Δ (σ.cons q) (S.cons (fun _ => False)) hΔ (substEq_cons hΓ hσ hq)
      (tv_cons_empty hS q)
    have e : ∀ t, Obs env U Δ (σ.cons q) (S.cons (fun _ => False)) t.lift =
        Obs env U Δ σ S t := fun t => funext fun o => propext Obs.lift_cons_iff
    rwa [e, e] at h
  · intro H Δ σ S hΔ hσ hS
    obtain ⟨hσ', hq⟩ := substEq_cons_inv hσ
    have h := H Δ σ.tail (fun i => S (i + 1)) hΔ hσ' ⟨_, hq.hasType.1⟩ (tv_tail hS)
    have e : ∀ t, Obs env U Δ σ.tail (fun i => S (i + 1)) t = Obs env U Δ σ S t.lift :=
      fun t => funext fun o => by
        have := Obs.lift_cons_iff (env := env) (U := U) (Δ := Δ) (σ := σ.tail) (x := σ.head)
          (S := fun i => S (i + 1)) (X := S 0) (t := t) (o := o)
        rw [subst_cons_tail_head σ, obSets_cons_tail_head S] at this
        exact (propext this).symm
    rwa [e, e] at h

/-- The semantic form of strengthening: agreement of observations in the inhabited targets
gives agreement in all targets. This is what the model route needs in addition to reflection;
it is not implied by soundness, since the target `Δ = Γ` with the identity anchor is excluded
when `Q` has no inhabitant in `Γ`. -/
def ModelStrengthening (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx (Q :: Γ) (env.IsType U) →
    KEqOn env U Γ (Inhabits env U Q) a b → KEq env U Γ a b

/-- With an inhabitant of `Q` in `Γ`, every target for `Γ` is an inhabited target. -/
theorem KEqOn.toKEq_of_inhabited (henv : env.OrderedStrong) (hq : env.HasType U Γ q Q)
    (H : KEqOn env U Γ (Inhabits env U Q) a b) : KEq env U Γ a b := by
  intro Δ σ S hΔ hσ hS
  exact H Δ σ S hΔ hσ ⟨_, hq.subst henv hσ hΔ⟩ hS

end VEnv.StrengtheningModel
end Lean4Lean
