import Lean4Lean.Theory.Typing.Strengthening.Candidates

/-! # The typing gap and the rigid binder

Continuation of the ledger of `Candidates.lean` (direction C of
`docs/inductives/STRENGTHENING_ATTEMPT_2026-10-09b.md`). The organising statement is Astra's
checked `not_cancel_iff_typing_gap` (round 8): `Cancel` fails exactly when some `q`-free term
is typable in `Q :: Γ` and at no type in `Γ`, for a `Q` with no inhabitant in `Γ`. This file
records what the gap can and cannot be:

* **A gap at a fixed lifted type reduces to a type-level `Cancel` failure.** If `t` is typed
  below at `T` and above at `A↑` then `T↑ ≡ A↑` above (`retyping_gap`); if moreover `t` is not
  typed below at `A`, the pair of types `(T, A)`, both typed below, is itself a failing `Cancel`
  instance (`typing_gap_is_type_cancel`, `typing_gap_cases`). In particular a `q`-free term
  typed above at `Q↑` either inhabits `Q` below, or is typable at no type below, or exhibits a
  type-level failure between types typed below.
* **A cast into `Q` inhabits `Q`.** `typeCast u M Q e m` with `e : M = Q` and `m : M` typed
  below is typed below at `Q`, so the instance is the inhabited one
  (`cast_into_binder_inhabits`, `cast_source_cancel`). A self-supporting pair of casts would
  need the typing of each piece above only, which by the previous bullet is a type-level
  failure between types typed below, or a piece typable at no type below.
* **The binder is a proof exactly when its sort level is `≈ 0`** (`binder_proof_iff_level`), a
  property of the level expression, not of its specialisations: `¬ u ≈ 0` is weaker than
  `u.IsNeverZero` (`param_nonzero_not_neverzero`, Astra), and it is the former that governs
  `proofIrrel` in the judgement at the given universe parameters.
* **Rigid binders.** For `Q = I args` with `I` rigid, `Q : Sort u`, `¬ u ≈ 0`, the variable `q`
  is never a proof (`rigid_binder_not_proof`), never a function (`rigid_binder_not_function`)
  and never an inhabitant of a registered structure (`rigid_binder_not_struct`). This excludes
  `proofIrrel`, `eta`, `structEta`, `unitLike` and projections on the *bare* variable only.
  Derived proofs `f q` with `f : Q → P`, `P : Prop`, are proof-irrelevant above
  (`derived_proof_irrel`, Astra), and the transfer theorem `prop_binder_transfer` turns every
  Prop-binder instance `P :: Γ ⊢ a↑ ≡ b↑` into a `Q`-binder instance over the context
  `(Q → P) :: Γ`, for any `Q` whatsoever, by substituting the Prop variable with `g q`.
  Consequently `RigidCancel` (`Cancel` restricted to rigid non-proposition binders) turns every
  Prop-binder instance into a `Π`-binder instance in the same context
  (`RigidCancel.prop_to_pi`): the rigid case contains the derived-proof mechanism of the Prop
  case and is not a simpler problem. The derived-proof route is harmless exactly when `P` is
  inhabited below (`transfer_inhabited`).
* **Fresh axiom types** give rigid binders in every well-formed environment with canonical
  `Eq`: `AxiomEnv` adds `I : Type` as an axiom (`axiomEnv_exists`, `AxiomEnv.wf`,
  `AxiomEnv.canonicalEq`, `AxiomEnv.rigid`). -/

namespace Lean4Lean
namespace VEnv.StrengtheningHunt
open VEnv VExpr StrengtheningKripke

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {Q A T P M a b t m e f : VExpr}

/-! ## 1. The typing gap at a fixed lifted type -/

/-- A `q`-free term typed below at `T` and above at `A↑` has `T↑ ≡ A↑` above. -/
theorem retyping_gap (henv : env.WF) (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (ht : env.HasType U Γ t T) (ht' : env.HasType U (Q :: Γ) t.lift A.lift) :
    env.IsDefEqU U (Q :: Γ) T.lift A.lift :=
  (ht.weak henv.ordered).uniqU henv hΓQ ht'

/-- A `q`-free term typed below, typed above at `A↑` but not below at `A`, is a type-level
failure of `Cancel` between the two types `T` and `A`, both typed below. -/
theorem typing_gap_is_type_cancel (henv : env.WF) (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (hA : env.HasType U Γ A (.sort u))
    (ht : env.HasType U Γ t T) (ht' : env.HasType U (Q :: Γ) t.lift A.lift)
    (hnot : ¬ env.HasType U Γ t A) :
    env.IsDefEqU U Γ (.lam Q T.lift) (.lam Q A.lift) ∧ ¬ env.IsDefEqU U Γ T A := by
  have hTA := retyping_gap henv hΓQ ht ht'
  obtain ⟨_, hQ⟩ := hΓQ.2
  have hA' : env.HasType U (Q :: Γ) A.lift (.sort u) := hA.weak henv.ordered
  refine ⟨⟨_, .lamDF hQ (hTA.of_r henv hΓQ hA')⟩, fun h => hnot ?_⟩
  exact HasType.defeqU_r henv hΓQ.1 h ht

/-- The three possibilities for a `q`-free term typed above at a lifted type. -/
theorem typing_gap_cases (henv : env.WF) (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (hA : env.HasType U Γ A (.sort u))
    (ht' : env.HasType U (Q :: Γ) t.lift A.lift) :
    env.HasType U Γ t A ∨ (∀ T, ¬ env.HasType U Γ t T) ∨
    ∃ T, env.HasType U Γ t T ∧
      env.IsDefEqU U Γ (.lam Q T.lift) (.lam Q A.lift) ∧ ¬ env.IsDefEqU U Γ T A := by
  classical
  by_cases h : env.HasType U Γ t A
  · exact .inl h
  by_cases h' : ∃ T, env.HasType U Γ t T
  · obtain ⟨T, hT⟩ := h'
    exact .inr (.inr ⟨T, hT, typing_gap_is_type_cancel henv hΓQ hA hT ht' h⟩)
  · exact .inr (.inl (by simpa using h'))

/-- A cast into `Q` along an equation available below inhabits `Q` below. -/
theorem cast_into_binder_inhabits (henv : env.Ordered) (heq : env.HasCanonicalEq) (hu : u.WF U)
    (hM : env.HasType U Γ M (.sort u)) (hQ : env.HasType U Γ Q (.sort u))
    (he : env.HasType U Γ e (eqApp (.succ u) (.sort u) M Q)) (hm : env.HasType U Γ m M) :
    env.HasType U Γ (typeCast u M Q e m) Q :=
  HasType.typeCast henv heq hu hM hQ he hm

/-- So the corresponding `Cancel` instance is the inhabited one. -/
theorem cast_source_cancel (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hu : u.WF U)
    (hM : env.HasType U Γ M (.sort u)) (hQ : env.HasType U Γ Q (.sort u))
    (he : env.HasType U Γ e (eqApp (.succ u) (.sort u) M Q)) (hm : env.HasType U Γ m M)
    (H : env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift)) : env.IsDefEqU U Γ a b :=
  Cancel.inhabited henv hΓ (cast_into_binder_inhabits henv.ordered heq hu hM hQ he hm) H

/-! ## 2. When is the binder a proof? -/

/-- The binder variable is a proof above exactly when the sort level of `Q` is equivalent to
zero. This is a property of the level expression `u` at the given universe parameters. -/
theorem binder_proof_iff_level (henv : env.WF) (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (hQ : env.HasType U Γ Q (.sort u)) :
    (∃ P, env.HasType U (Q :: Γ) P (.sort .zero) ∧ env.HasType U (Q :: Γ) (.bvar 0) P) ↔
      u ≈ .zero := by
  have hq : env.HasType U (Q :: Γ) (.bvar 0) Q.lift := .bvar .zero
  have hQ' : env.HasType U (Q :: Γ) Q.lift (.sort u) := hQ.weak henv.ordered
  constructor
  · rintro ⟨P, hP, hp⟩
    have ht := (hq.uniqU henv hΓQ hp).of_r henv hΓQ hP
    exact (hQ'.uniqU henv hΓQ ht.hasType.1).sort_inv henv hΓQ
  · intro h
    have hu : u.WF U := hQ.sort_r henv.ordered hΓQ.1
    exact ⟨Q.lift, (IsDefEq.sortDF (l' := .zero) hu trivial h).defeq hQ', hq⟩

/-- Astra's check (round 8): non-equivalence to zero is not positivity at every
specialisation. -/
theorem param_nonzero_not_neverzero :
    ¬ (VLevel.param 0 ≈ .zero) ∧ ¬ (VLevel.param 0).IsNeverZero := by
  constructor
  · intro h
    have hh := congrFun h [1]
    simp [VLevel.eval] at hh
  · intro h
    exact h [0] rfl

/-! ## 3. Rigid binders -/

/-- A binder of a rigid type at a level `u ≉ 0` is not a proof. -/
theorem rigid_binder_not_proof (henv : env.WF) (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (hQ : env.HasType U Γ Q (.sort u)) (hne : ¬ u ≈ .zero)
    (hP : env.HasType U (Q :: Γ) P (.sort .zero)) :
    ¬ env.HasType U (Q :: Γ) (.bvar 0) P :=
  fun hp => hne ((binder_proof_iff_level henv hΓQ hQ).1 ⟨P, hP, hp⟩)

/-- A binder of a rigid type is not a function. -/
theorem rigid_binder_not_function (henv : env.WF)
    (hΓQ : OnCtx (mkApps (.const I ls) args :: Γ) (env.IsType U))
    (hI : env.Rigid I) (hQ : env.HasType U Γ (mkApps (.const I ls) args) (.sort u)) :
    ¬ env.HasType U (mkApps (.const I ls) args :: Γ) (.bvar 0) (.forallE A B) := by
  intro hf
  have hq : env.HasType U (mkApps (.const I ls) args :: Γ) (.bvar 0)
      (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) := by
    simpa only [liftN_mkApps, liftN] using
      (HasType.bvar .zero : env.HasType U (mkApps (.const I ls) args :: Γ) (.bvar 0) _)
  have hQ' : env.HasType U (mkApps (.const I ls) args :: Γ)
      (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) (.sort u) := by
    have := hQ.weak henv.ordered (B := mkApps (.const I ls) args)
    simp only [lift, liftN_mkApps, liftN] at this
    exact this
  exact IsDefEqU.rigidApp_forallE_inv henv hΓQ hI hQ' (hq.uniqU henv hΓQ hf)

/-- A binder of a rigid type with no projections is not an inhabitant of a registered
structure. -/
theorem rigid_binder_not_struct (henv : env.WF)
    (hΓQ : OnCtx (mkApps (.const I ls) args :: Γ) (env.IsType U))
    (hI : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (hQ : env.HasType U Γ (mkApps (.const I ls) args) (.sort u))
    (hS : env.projections S info) :
    ¬ env.HasType U (mkApps (.const I ls) args :: Γ) (.bvar 0) (mkApps (.const S ls') ps) := by
  intro hs
  have hq : env.HasType U (mkApps (.const I ls) args :: Γ) (.bvar 0)
      (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) := by
    simpa only [liftN_mkApps, liftN] using
      (HasType.bvar .zero : env.HasType U (mkApps (.const I ls) args :: Γ) (.bvar 0) _)
  have hQ' : env.HasType U (mkApps (.const I ls) args :: Γ)
      (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) (.sort u) := by
    have := hQ.weak henv.ordered (B := mkApps (.const I ls) args)
    simp only [lift, liftN_mkApps, liftN] at this
    exact this
  have hne : I ≠ S := fun h => hn info (h ▸ hS)
  exact IsDefEqU.rigidApp_ne henv hΓQ hI (henv.projectionRigid hS) hne hQ'
    (hq.uniqU henv hΓQ hs)

/-- Astra's check (round 8): a derived proof `f q` is proof-irrelevant above, with no
inhabitant of `Q` and no proof status of `q` itself. -/
theorem derived_proof_irrel (henv : env.Ordered)
    (hP : env.HasType U Γ P (.sort .zero))
    (hf : env.HasType U Γ f (.forallE Q P.lift))
    (hh : env.HasType U Γ h P) :
    env.IsDefEq U (Q :: Γ) (.app f.lift (.bvar 0)) h.lift P.lift := by
  have ha : env.HasType U (Q :: Γ) (.app f.lift (.bvar 0)) P.lift := by
    simpa only [lift, liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv (B := Q)) (HasType.bvar (Lookup.zero (ty := Q)))
  exact .proofIrrel (hP.weak henv) ha (hh.weak henv)

/-- The derived proof `g q` as a term of `P` in the context `Q :: (Q → P) :: Γ`. -/
theorem derived_proof_typed :
    env.HasType U (Q.lift :: .forallE Q P.lift :: Γ) (.app (.bvar 1) (.bvar 0)) (P.liftN 2) := by
  have h1 : env.HasType U (Q.lift :: .forallE Q P.lift :: Γ) (.bvar 1)
      ((VExpr.forallE Q P.lift).lift.lift) := .bvar (.succ .zero)
  have h0 : env.HasType U (Q.lift :: .forallE Q P.lift :: Γ) (.bvar 0) Q.lift.lift := .bvar .zero
  have e1 : (VExpr.forallE Q P.lift).lift.lift = .forallE Q.lift.lift (P.liftN 3) := by
    show VExpr.forallE _ _ = _
    rw [liftN'_liftN' (e := P) (n1 := 1) (n2 := 1) (k1 := 0) (k2 := 1) (Nat.zero_le _) (by decide),
      liftN'_liftN' (e := P) (n1 := 2) (n2 := 1) (k1 := 0) (k2 := 1) (Nat.zero_le _) (by decide)]
  rw [e1] at h1
  have := HasType.app h1 h0
  rwa [show (3 : Nat) = 2 + 1 from rfl, inst_liftN'] at this

/-- **Transfer.** Every Prop-binder instance is a `Q`-binder instance over the context
extended by a function `g : Q → P`, for every `Q`: substitute the Prop variable by `g q`. -/
theorem prop_binder_transfer (henv : env.Ordered)
    (H : env.IsDefEqU U (P :: Γ) a.lift b.lift) :
    env.IsDefEqU U (Q.lift :: .forallE Q P.lift :: Γ) (a.liftN 2) (b.liftN 2) := by
  have W : Ctx.LiftN 2 1 (P :: Γ) (P.liftN 2 :: Q.lift :: .forallE Q P.lift :: Γ) :=
    .succ (.zero [Q.lift, .forallE Q P.lift])
  have H' := H.weakN henv W
  have H'' := H'.instN henv Ctx.InstN.zero (derived_proof_typed (env := env) (U := U))
  have e : ∀ x : VExpr, ((x.lift).liftN 2 1).inst (VExpr.app (.bvar 1) (.bvar 0)) 0 = x.liftN 2 :=
    fun x => by
      rw [liftN'_liftN' (e := x) (n1 := 1) (n2 := 2) (k1 := 0) (k2 := 1) (Nat.zero_le _) (by decide),
        show (1 + 2 : Nat) = 2 + 1 from rfl, inst_liftN']
  rwa [e, e] at H''

/-- The transferred instance is solved below whenever `P` is inhabited below: the derived
proof route is harmless exactly in that case. -/
theorem transfer_inhabited (henv : env.WF)
    (hh : env.HasType U Γ h P) (H : env.IsDefEqU U (P :: Γ) a.lift b.lift) :
    env.IsDefEqU U Γ a b :=
  IsDefEqU.strengthen_inhabited henv.ordered hh H

/-- `Cancel` restricted to binders that are applications of a rigid constant with no
projections, at a sort level not equivalent to zero: the variable is then never a proof, a
function or a structure inhabitant. -/
def RigidCancel (env : VEnv) : Prop :=
  ∀ ⦃U Γ I ls args u a b⦄, OnCtx Γ (env.IsType U) →
    env.Rigid I → (∀ info, ¬ env.projections I info) →
    env.HasType U Γ (mkApps (.const I ls) args) (.sort u) → ¬ u ≈ .zero →
    env.IsDefEqU U Γ (.lam (mkApps (.const I ls) args) a.lift)
      (.lam (mkApps (.const I ls) args) b.lift) →
    env.IsDefEqU U Γ a b

theorem Cancel.rigidCancel (h : Cancel env) : RigidCancel env :=
  fun _ _ _ _ _ _ _ _ hΓ _ _ _ _ H => h hΓ H

/-- **Rigidity does not help.** `RigidCancel` turns every Prop-binder instance into a
`Π`-binder instance in the same context: the Prop variable becomes the derived proof `g q`
of a rigid binder `q`, and the remaining binder is `g : Q → P`. -/
theorem RigidCancel.prop_to_pi (henv : env.WF) (hr : RigidCancel env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hI : env.Rigid I) (hn : ∀ info, ¬ env.projections I info)
    (hQ : env.HasType U Γ (mkApps (.const I ls) args) (.sort u)) (hu : ¬ u ≈ .zero)
    (hP : env.HasType U Γ P (.sort .zero))
    (H : env.IsDefEqU U Γ (.lam P a.lift) (.lam P b.lift)) :
    env.IsDefEqU U Γ (.lam (.forallE (mkApps (.const I ls) args) P.lift) a.lift)
      (.lam (.forallE (mkApps (.const I ls) args) P.lift) b.lift) := by
  have hbody := IsDefEqU.lam_body henv hΓ H
  have htr := prop_binder_transfer (Q := mkApps (.const I ls) args) henv.ordered hbody
  have hPi : env.HasType U Γ (.forallE (mkApps (.const I ls) args) P.lift)
      (.sort (.imax u .zero)) :=
    .forallE hQ (hP.weak henv.ordered)
  have hΓ' : OnCtx (VExpr.forallE (mkApps (.const I ls) args) P.lift :: Γ) (env.IsType U) :=
    ⟨hΓ, _, hPi⟩
  have hlift : (mkApps (.const I ls) args).lift =
      mkApps (.const I ls) (args.map fun arg => arg.liftN 1) := by
    simp only [liftN_mkApps, liftN]
  have hQ' : env.HasType U (VExpr.forallE (mkApps (.const I ls) args) P.lift :: Γ)
      (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) (.sort u) := by
    rw [← hlift]; exact hQ.weak henv.ordered
  obtain ⟨R, htr⟩ := htr
  have htr' : env.IsDefEq U ((mkApps (.const I ls) args).lift ::
      VExpr.forallE (mkApps (.const I ls) args) P.lift :: Γ) a.lift.lift b.lift.lift R := by
    simpa only [liftN_liftN] using htr
  rw [hlift] at htr'
  have hlam : env.IsDefEqU U (VExpr.forallE (mkApps (.const I ls) args) P.lift :: Γ)
      (.lam (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) a.lift.lift)
      (.lam (mkApps (.const I ls) (args.map fun arg => arg.liftN 1)) b.lift.lift) :=
    ⟨_, .lamDF hQ' htr'⟩
  obtain ⟨R', hab⟩ := hr hΓ' hI hn hQ' hu hlam
  exact ⟨_, .lamDF hPi hab⟩

/-! ## 4. Fresh axiom types -/

/-- The environment with a fresh axiom `I : Type`. -/
structure AxiomEnv (env : VEnv) (I : Name) (env' : VEnv) : Prop where
  add : env.addConst I ⟨0, .sort (.succ .zero)⟩ = some env'

theorem axiomEnv_exists (h : env.constants I = none) : ∃ env', AxiomEnv env I env' :=
  ⟨{ env with constants := fun n => if I = n then some ⟨0, .sort (.succ .zero)⟩ else env.constants n },
    ⟨by unfold VEnv.addConst; rw [h]⟩⟩

namespace AxiomEnv
variable (H : AxiomEnv env I env')
include H

theorem defeqs' : env'.defeqs = env.defeqs := VEnv.addConst_defeqs H.add
theorem projections' : env'.projections = env.projections := VEnv.addConst_projections H.add
theorem fresh : env.constants I = none := VEnv.addConst_fresh H.add
theorem le : env ≤ env' := VEnv.addConst_le H.add
theorem const : env'.constants I = some ⟨0, .sort (.succ .zero)⟩ := VEnv.addConst_self H.add

theorem typed : env'.HasType U Γ (.const I []) (.sort (.succ .zero)) :=
  HasType.const H.const (by simp) rfl

theorem wf (henv : env.WF) : env'.WF := by
  obtain ⟨ds, hds⟩ := henv
  exact ⟨_, .decl (.axiom (ci := (loopVal I).toVConstVal) sortOne_isType H.add) hds⟩

theorem canonicalEq (heq : env.HasCanonicalEq) : env'.HasCanonicalEq := heq.mono H.le

theorem rigid (henv : env.WF) : env'.Rigid I := by
  intro df hdf ls h
  rw [H.defeqs'] at hdf
  exact henv.rigid_of_fresh H.fresh df hdf ls h

theorem no_projections (hn : ∀ info, ¬ env.projections I info) :
    ∀ info, ¬ env'.projections I info := by
  rw [H.projections']; exact hn

end AxiomEnv

end VEnv.StrengtheningHunt
end Lean4Lean
