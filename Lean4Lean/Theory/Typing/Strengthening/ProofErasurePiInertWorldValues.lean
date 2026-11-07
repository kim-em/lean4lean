import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldSpines
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedValueChain

/-! # Typed beta predecessors retain neutral value evidence

A term may reduce to a neutral value without itself being neutral. Retaining
that concrete ordinary-core reduction preserves dependent application data;
actual source typing supplies the confluence needed for independent residuals.
No normalization theorem or arbitrary carrier-to-action promotion is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A typed raw source and an ordinary-core path construct the full retained
computation evidence. The typing witness is explicit, including for applications. -/
theorem PiInertEvidence.core_source
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HT : TypedSource Δ a) (R : Compute (ErasedLevelCore D) a b) :
    PiInertEvidence D n .compute Δ a b := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
  exact .core hs hc hΓ ht R

/-- Inferred comparison survives independently certified endpoint prefixes.
Each prefix's ordinary output tail feeds the corresponding comparison residual. -/
theorem PiInertWorldComparison.prefixes
    (RA : PiInertWorldComputation D n Δ a a')
    (RB : PiInertWorldComputation D n Δ b b')
    (H : PiInertWorldComparison D n Δ a' b') : PiInertWorldComparison D n Δ a b := by
  have go {Δ a b a' b'} (RA : PiInertInterpret D n .compute Δ a a')
      (RB : PiInertInterpret D n .compute Δ b b')
      (H : PiInertInterpret D n (.compare false) Δ a' b') :
      PiInertInterpret D n (.compare false) Δ a b := by
    intro left right RL RR
    obtain ⟨left', RS, RT⟩ := RA.2 RL
    obtain ⟨right', RU, RV⟩ := RB.2 RR
    exact .compute RS RU (H RT RV)
  refine ⟨go RA.base RB.base H.base, ?_⟩
  intro Δ' τ W left right RL RR
  exact go (RA.future W) (RB.future W) (H.future W) RL RR

/-- A core reduct of a variable spine remains a variable spine. -/
theorem ProofShape.AnchoredCarrier.level_core
    (H : AnchoredCarrier 0 e) (R : Compute (ErasedLevelCore D) e e') : AnchoredCarrier 0 e' := by
  obtain ⟨i, args, hi, rfl⟩ := H
  obtain ⟨args', E, _⟩ := R.level_core_bvar_spine
  exact ⟨i, args', hi, E⟩

/-- Native recovery at a source residual is already present in the original
recovery evidence; future core paths substitute directly. -/
theorem PiInertWorldRecovery.reduct
    (H : PiInertWorldRecovery D n Δ e T) (R : Compute (ErasedLevelCore D) e e') :
    PiInertWorldRecovery D n Δ e' T := by
  refine ⟨fun S => H.base (R.trans S), ?_⟩
  intro Δ' τ W out S
  exact H.future W ((R.subst (fun H => erased_level_core_subst H)).trans S)

/-- Both inferred comparison endpoints can follow independent core paths. -/
theorem PiInertWorldComparison.reducts (H : PiInertWorldComparison D n Δ a b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertWorldComparison D n Δ a' b' := by
  refine ⟨fun RL RR => H.base (RA.trans RL) (RB.trans RR), ?_⟩
  intro Δ' τ W left right RL RR
  exact H.future W ((RA.subst (fun R => erased_level_core_subst R)).trans RL)
    ((RB.subst (fun R => erased_level_core_subst R)).trans RR)

/-- Neutral packages retain their selected dependent type and further action
after independently reducing either endpoint. -/
theorem PiInertWorldNeutral.reducts (H : PiInertWorldNeutral D n Δ a b T)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertWorldNeutral D n Δ a' b' T :=
  ⟨H.left.level_core RA, H.right.level_core RB, H.recovery.reduct RA, H.comparison.reducts RA RB⟩

/-- A typed pair with concrete ordinary-core paths to a neutral pair. The
neutral result retains recovery at the selected left type and inferred
comparison. Source typing is not inferred merely from the selected raw type. -/
structure PiInertWorldValue (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (a b T : ProofShape) : Prop where
  leftSource : TypedSource Δ a
  rightSource : TypedSource Δ b
  reduct : ∃ f g, Compute (ErasedLevelCore D) a f ∧ Compute (ErasedLevelCore D) b g ∧
    PiInertWorldNeutral D n Δ f g T

/-- An already neutral pair supplies a value when both actual typing witnesses
are provided. Raw recovery alone is not treated as an actual typing derivation. -/
theorem PiInertWorldNeutral.value (H : PiInertWorldNeutral D n Δ a b T)
    (HA : TypedSource Δ a) (HB : TypedSource Δ b) : PiInertWorldValue D n Δ a b T :=
  ⟨HA, HB, a, b, .refl, .refl, H⟩

/-- Values move through core worlds: ordinary-core reductions substitute, and
typing and the neutral package retain their own corresponding future clauses. -/
theorem PiInertWorldValue.move (H : PiInertWorldValue D n Δ a b T)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertWorldValue D n Δ' (a.subst τ) (b.subst τ) (T.subst τ) := by
  obtain ⟨f, g, RA, RB, N⟩ := H.reduct
  exact ⟨H.leftSource.subst W.typed, H.rightSource.subst W.typed, _, _,
    RA.subst (fun R => erased_level_core_subst R), RB.subst (fun R => erased_level_core_subst R), N.move W⟩

/-- Raising the stage does not change the concrete source reductions. -/
theorem PiInertWorldValue.raise (hle : n ≤ m) (H : PiInertWorldValue D n Δ a b T) :
    PiInertWorldValue D m Δ a b T := by
  obtain ⟨f, g, RA, RB, N⟩ := H.reduct
  exact ⟨H.leftSource, H.rightSource, f, g, RA, RB, N.raise hle⟩

/-- A supplied retained type computation changes the selected result type.
This is not a conversion rule for arbitrary actual type equalities. -/
theorem PiInertWorldValue.convert (H : PiInertWorldValue D n Δ a b T)
    (R : PiInertWorldComputation D n Δ T U) : PiInertWorldValue D n Δ a b U := by
  obtain ⟨f, g, RA, RB, N⟩ := H.reduct
  exact ⟨H.leftSource, H.rightSource, f, g, RA, RB, N.convert R⟩

/-- Ordinary-core predecessors retain the entire value package when the new
sources are actually typed. This includes typed beta expansions. -/
theorem PiInertWorldValue.prefixes (H : PiInertWorldValue D n Δ a' b' T)
    (HA : TypedSource Δ a) (HB : TypedSource Δ b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertWorldValue D n Δ a b T := by
  obtain ⟨f, g, RF, RG, N⟩ := H.reduct
  exact ⟨HA, HB, f, g, RA.trans RF, RB.trans RG, N⟩

/-- Inferred comparison is read from a value using only typed ordinary-core
confluence for its two supplied prefixes. The complete core-world clause survives. -/
theorem PiInertWorldValue.comparison
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertWorldValue D n Δ a b T) : PiInertWorldComparison D n Δ a b := by
  obtain ⟨f, g, RA, RB, N⟩ := H.reduct
  exact N.comparison.prefixes
    (PiInertEvidence.core_source hs hc H.leftSource RA).world_computation
    (PiInertEvidence.core_source hs hc H.rightSource RB).world_computation

/-- Values supply carrier histories, including the original strengthening
readout, without discarding the neutral result needed for further application. -/
theorem PiInertWorldValue.history
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertWorldValue D n Δ a b T) : PiInertWorldHistory D n Δ C a b :=
  (H.comparison hs hc).history

/-- Neutral-returning value evidence cannot relate distinct bare variables.
Consequently it cannot replace carrier histories in a general interpretation:
subsingleton carrier equality may relate such variables. This is a boundary
of this value class, not a counterexample to declarative strengthening. -/
theorem PiInertWorldValue.bvar_injective
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertWorldValue D n Δ (.bvar i) (.bvar j) T) : i = j :=
  ((H.comparison hs hc).base .refl .refl).pi_inert_bvar_injective

/-- Every independent source core reduction has another neutral value witness.
Typed core confluence joins it with the retained witness, and the neutral
package follows the resulting residuals. No chosen normal form is required. -/
theorem PiInertWorldValue.reducts
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertWorldValue D n Δ a b T)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertWorldValue D n Δ a' b' T := by
  obtain ⟨f, g, RF, RG, N⟩ := H.reduct
  have join {a a' f} (HT : TypedSource Δ a)
      (RA : Compute (ErasedLevelCore D) a a') (RF : Compute (ErasedLevelCore D) a f) :
      ∃ out, Compute (ErasedLevelCore D) a' out ∧ Compute (ErasedLevelCore D) f out := by
    obtain ⟨Γ, e, A, hΓ, _, he, Ee⟩ := HT
    exact hc hΓ he (Ee ▸ RA) (Ee ▸ RF)
  obtain ⟨f', RL, RF'⟩ := join H.leftSource RA RF
  obtain ⟨g', RR, RG'⟩ := join H.rightSource RB RG
  exact ⟨(PiInertEvidence.core_source (n := n) hs hc H.leftSource RA).base.1,
    (PiInertEvidence.core_source (n := n) hs hc H.rightSource RB).base.1,
    f', g', RL, RR, N.reducts RF' RG'⟩

/-- A typed application returns the entire value at the left dependent result
type. The sources may be lambda-headed beta predecessors; only their supplied
core reducts must be neutral. Whole-application typing is an explicit premise. -/
theorem PiInertWorldValue.app (H : PiInertWorldValue D n Δ a b (.forallE A B))
    (HX : PiInertWorldHistory D n Δ A x y)
    (HA : TypedSource Δ (.app a x)) (HB : TypedSource Δ (.app b y)) :
    PiInertWorldValue D n Δ (.app a x) (.app b y) (B.inst x) := by
  obtain ⟨f, g, RA, RB, N⟩ := H.reduct
  exact ⟨HA, HB, _, _, .app RA .refl, .app RB .refl, N.app HX⟩

/-- A whole typed application chain supplies all intermediate application
typing witnesses. Its argument demands then preserve the complete value
through the finite dependent sequence, including beta-predecessor heads. -/
theorem PiInertWorldArguments.run_values (H : PiInertWorldArguments D n Δ T xs ys U)
    (N : PiInertWorldValue D n Δ a b T)
    (HA : TypedSource Δ (ProofShape.mkApps a xs)) (HB : TypedSource Δ (ProofShape.mkApps b ys)) :
    PiInertWorldValue D n Δ (ProofShape.mkApps a xs) (ProofShape.mkApps b ys) U := by
  induction H generalizing a b with
  | nil => exact N
  | cons R HX _ ih =>
    exact ih ((N.convert R).app HX (TypedSource.mkApps_head HA) (TypedSource.mkApps_head HB)) HA HB

/-- Actual application supplies the whole-application typing required by the
value rule and reconstructs precisely the left dependent result erasure.
The common typing comes from the original actual equality premises. -/
theorem PiInertWorldValue.apply_actual_nonproof
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.IsDefEq univs Γ f g (.forallE A B))
    (hX : env.IsDefEq univs Γ x y A) (hn : ¬ IsProof Γ (.app f x))
    (H : PiInertWorldValue D n (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)))
    (HX : PiInertWorldHistory D n (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertWorldValue D n (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) (proofErase Γ (B.inst x)) := by
  have hApp := hF.appDF hX
  have hn' : ¬ IsProof Γ (.app g y) := fun hp =>
    hn (isProof_of_common_type hΓ hApp.hasType.2 hApp.hasType.1 hp)
  obtain ⟨v, hPi⟩ := hF.hasType.1.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨w, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  rw [EP] at H
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
    show proofErase Γ (.app g y) = .app _ _ from if_neg hn',
    proofErase_instN hΓA hX.hasType.1 Ctx.InstN.zero hB]
  exact H.app HX ⟨Γ, _, _, hΓ, rfl, hApp.hasType.1, if_neg hn⟩
    ⟨Γ, _, _, hΓ, rfl, hApp.hasType.2, if_neg hn'⟩

/-- A supplied pair of instantiated lambda-body values constructs values for
the original beta applications. Written lambda annotations may differ from
each other and from the assigned Pi; actual typing licenses both prefixes.
General construction of the paired body values remains a separate obligation. -/
theorem PiInertWorldValue.lambda_apply
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : PiInertWorldValue D n (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) (proofErase Γ (B.inst x))) :
    PiInertWorldValue D n (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam C b) x)) (proofErase Γ (.app (.lam E c) y))
      (proofErase Γ (B.inst x)) :=
  H.prefixes ⟨Γ, _, _, hΓ, rfl, hf.app hx, rfl⟩ ⟨Γ, _, _, hΓ, rfl, hg.app hy, rfl⟩
    (.beta (proofErase_beta_forward hΓ (hf.app hx) .beta))
    (.beta (proofErase_beta_forward hΓ (hg.app hy) .beta))

/-- Conversely, typed beta applications with value evidence retain values for
their body instances. Together with lambda_apply this calibrates the exact
paired-body obligation, rather than inferring it from carrier-only evidence. -/
theorem PiInertWorldValue.lambda_body
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : PiInertWorldValue D n (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam C b) x)) (proofErase Γ (.app (.lam E c) y))
      (proofErase Γ (B.inst x))) :
    PiInertWorldValue D n (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) (proofErase Γ (B.inst x)) :=
  H.reducts hs hc (.beta (proofErase_beta_forward hΓ (hf.app hx) .beta))
    (.beta (proofErase_beta_forward hΓ (hg.app hy) .beta))

/-- Typed application behavior consuming and returning whole value packages.
The function pair itself may be displayed lambdas rather than neutral values.
Every source application must have actual typing; arbitrary carrier-related
raw arguments are not silently accepted as sufficient higher-order evidence. -/
structure PiInertTypedValueAction (D : Definitions) (Δ : List ProofShape)
    (A B f g : ProofShape) : Prop where
  act : ∀ {Δ' τ x y stage}, PiInertCoreWorld D Δ Δ' τ →
    PiInertWorldValue D stage Δ' x y (A.subst τ) →
    TypedSource Δ' (.app (f.subst τ) x) → TypedSource Δ' (.app (g.subst τ) y) →
    ∃ n, PiInertWorldValue D n Δ' (.app (f.subst τ) x) (.app (g.subst τ) y)
      ((B.subst τ.lift).inst x)

/-- A value at a selected Pi constructs typed value action. The input value
supplies its carrier history; application returns the complete output value. -/
theorem PiInertWorldValue.typed_action
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertWorldValue D n Δ f g (.forallE A B)) :
    PiInertTypedValueAction D Δ A B f g := by
  refine ⟨?_⟩
  intro Δ' τ x y stage W HX HA HB
  have HF := (H.move W).raise (Nat.le_max_left n stage)
  have HY := (HX.history hs hc (C := A.subst τ)).raise (Nat.le_max_right n stage)
  exact ⟨max n stage, HF.app HY HA HB⟩

/-- Typed action itself moves through the same variable worlds. Whole source
application typing is supplied in the final world, not reflected to an older one. -/
theorem PiInertTypedValueAction.move (H : PiInertTypedValueAction D Δ A B f g)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertTypedValueAction D Δ' (A.subst τ) (B.subst τ.lift) (f.subst τ) (g.subst τ) := by
  refine ⟨?_⟩
  intro Δ'' υ x y stage V HX HA HB
  simp only [ProofShape.subst_subst] at HX HA HB
  obtain ⟨n, HN⟩ := H.act (W.compose V) HX HA HB
  exact ⟨n, by simpa only [ProofShape.subst_subst, ProofShape.Subst.comp_lift] using HN⟩

omit [Params] in
private theorem value_inst_lift (a x : ProofShape) : (a.liftN 1).inst x = a := by
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id]

/-- Identity is a displayed lambda with typed value action. The supplied
argument value is retained at the same stage; typed beta predecessors preserve
all of its future application evidence, not just its carrier history. -/
theorem pi_inert_identity_typed_value_action :
    PiInertTypedValueAction D Δ A (A.liftN 1) (.lam A (.bvar 0)) (.lam A (.bvar 0)) := by
  refine ⟨?_⟩
  intro Δ' τ x y stage W HX HA HB
  simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift, value_inst_lift] at HA HB ⊢
  have beta (x : ProofShape) : Compute (ErasedLevelCore D) (.app (.lam (A.subst τ) (.bvar 0)) x) x := by
    apply ProofShape.Compute.beta
    simpa only [ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
      (ProofShape.BetaRed.beta (A := A.subst τ) (b := .bvar 0) (a := x))
  exact ⟨stage, HX.prefixes HA HB (beta x) (beta y)⟩

/-- The higher-order evaluator `fun h => h x` has typed value action when its
captured argument retains a carrier history. Function arguments supply whole
values, and the evaluator returns a whole dependent value after beta. Thus the
returned function, when demanded, can be applied again using typed_action.
This does not infer general lambda behavior from a whole-function history. -/
theorem pi_inert_evaluator_typed_value_action
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HX : PiInertWorldHistory D n Δ A x x) :
    PiInertTypedValueAction D Δ (.forallE A B) ((B.inst x).liftN 1)
      (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1)))
      (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1))) := by
  refine ⟨?_⟩
  intro Δ' τ f g stage W HF HA HB
  have beta (f : ProofShape) : Compute (ErasedLevelCore D)
      (.app ((ProofShape.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1))).subst τ) f)
      (.app f (x.subst τ)) := by
    have E : ((ProofShape.app (.bvar 0) (x.liftN 1)).subst τ.lift).inst f = .app f (x.subst τ) := by
      simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift,
        ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero]
      exact congrArg (ProofShape.app f) (value_inst_lift (x.subst τ) f)
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := (ProofShape.forallE A B).subst τ))
  have HTA := (PiInertEvidence.core_source (n := 0) hs hc HA (beta f)).base.1
  have HTB := (PiInertEvidence.core_source (n := 0) hs hc HB (beta g)).base.1
  have HN := (HF.raise (Nat.le_max_right n stage)).app
    ((HX.move W).raise (Nat.le_max_left n stage)) HTA HTB
  refine ⟨max n stage, ?_⟩
  simpa only [ProofShape.lift_subst_lift, value_inst_lift, ProofShape.subst_inst] using
    HN.prefixes HA HB (beta f) (beta g)

end Lean4Lean.VEnv.Strengthening
