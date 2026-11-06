import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertNextApplication

/-! # A primitive that loses the tracked constant through mixed continuations

Track constants through application, retained lambda and identity wrappers.
All administrative expansion forms preserve this grammar, as do beta and
endpoint substitution. A lost head therefore has a concrete counted primitive
cut, outside argument/annotation work irrelevant to the tracked occurrence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
open private lambda_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta
variable [Params]

/-- A constant head protected by retained lambdas or identity applications.
The identity constructor tracks its payload, rather than its bound variable.
Arguments and lambda annotations remain unrestricted. -/
inductive WrappedConstHead (c : Name) : ProofShape → Prop where
  | const : WrappedConstHead c (.const c ls)
  | app : WrappedConstHead c f → WrappedConstHead c (.app f a)
  | lam : WrappedConstHead c b → WrappedConstHead c (.lam A b)
  | identity : WrappedConstHead c e → WrappedConstHead c (.app (.lam A (.bvar 0)) e)

omit [Params] in
/-- The former retained-head invariant embeds without changing the term. -/
theorem RetainedConstHead.wrapped (H : RetainedConstHead c e) : WrappedConstHead c e := by
  induction H with
  | const => exact .const
  | app _ ih => exact .app ih
  | lam _ ih => exact .lam ih

omit [Params] in
/-- Arbitrary pending arguments do not change the tracked occurrence. -/
theorem WrappedConstHead.mkApps (H : WrappedConstHead c f) (args : List ProofShape) :
    WrappedConstHead c (ProofShape.mkApps f args) := by
  induction args generalizing f with
  | nil => exact H
  | cons a args ih => exact ih (.app H)

omit [Params] in
/-- Endpoint substitution preserves both the constant and identity binders. -/
theorem WrappedConstHead.subst (H : WrappedConstHead c e) (τ : ProofShape.Subst) :
    WrappedConstHead c (e.subst τ) := by
  induction H generalizing τ with
  | const => exact .const
  | app _ ih => exact .app (ih τ)
  | lam _ ih => exact .lam (ih τ.lift)
  | identity _ ih => exact .identity (ih τ)

omit [Params] in
/-- Weakening preserves the wrapped occurrence at arbitrary binder depth. -/
theorem WrappedConstHead.liftN (H : WrappedConstHead c e) (n k : Nat) :
    WrappedConstHead c (e.liftN n k) := by
  have HH := H.subst (fun i => (ProofShape.Subst.id i).liftN n k)
  simpa only [← ProofShape.liftN_subst, ProofShape.subst_id] using HH

/-- Beta steps preserve the tracked payload of identity wrappers as well as
the bodies of retained lambdas. Annotation computations do not affect it. -/
theorem WrappedConstHead.beta (H : WrappedConstHead c e) (R : BetaRed e e') :
    WrappedConstHead c e' := by
  induction R with
  | refl => exact H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | app RF _ ihf iha =>
    cases H with
    | app H => exact .app (ihf H)
    | identity H =>
      obtain ⟨A', rfl, _⟩ := (show ScopedCompute (PiInertStage Definitions.empty 0) [] _ _ from .beta RF).pi_inert_identity_lam
      exact .identity (iha H)
  | proj => cases H
  | lam _ _ _ ih => cases H with | lam H => exact .lam (ih H)
  | forallE => cases H
  | beta =>
    cases H with
    | app H =>
      cases H with | lam H =>
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H.subst (ProofShape.Subst.one _)
    | identity H =>
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
        ProofShape.Subst.one, ProofShape.Subst.cons] using H

omit [Params] in
/-- The ordinary head is the tracked constant unless a lambda protects it. -/
theorem WrappedConstHead.spine_form (H : WrappedConstHead c e) :
    (∃ ls args, e = ProofShape.mkApps (.const c ls) args) ∨
      ∃ A b args, e = ProofShape.mkApps (.lam A b) args := by
  induction H with
  | const => exact .inl ⟨_, [], rfl⟩
  | app _ ih =>
    rcases ih with ⟨ls, args, rfl⟩ | ⟨A, b, args, rfl⟩
    · exact .inl ⟨ls, args ++ [_], (ProofShape.mkApps_snoc ..).symm⟩
    · exact .inr ⟨A, b, args ++ [_], (ProofShape.mkApps_snoc ..).symm⟩
  | lam => exact .inr ⟨_, _, [], rfl⟩
  | identity => exact .inr ⟨_, _, [_], rfl⟩

/-- Wrapped Eq heads are incompatible with an exposed carrier. -/
theorem WrappedConstHead.eq_not_exposed (heq : env.HasCanonicalEq)
    (H : WrappedConstHead ``Eq.rec e) : ¬ CarrierExposure e := by
  intro HE
  rcases H.spine_form with ⟨ls, args, rfl⟩ | ⟨A, b, args, EE⟩
  · exact carrier_exposure_ne_eqRec heq HE (constHead_mkApps _ _)
  · exact HE.not_lambda_spine A b args EE

/-- A counted local loss of the tracked head. Both surrounding paths keep
their exact scopes and occurrence counts; the hole may lie under retained
binders or inside the payload of an identity application. -/
def WrappedHeadCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (c : Name) (source out : ProofShape) (cost : Nat) : Prop :=
  ∃ Θ a b, ∃ C : ScopedHole Δ Θ, ∃ cp ct,
    cp+1+ct = cost ∧ ScopedComputeCount (PiInertStage D n) cp Δ source (C.plug a) ∧
    PiInertStage D n Θ a b ∧ WrappedConstHead c a ∧ ¬ WrappedConstHead c b ∧
    ScopedComputeCount (PiInertStage D n) ct Δ (C.plug b) out

/-- Losing the wrapped head in an actual counted path selects a primitive
that loses it. Beta cannot be selected. Application arguments and annotations
are skipped unless the argument is the tracked identity payload. -/
theorem ProofShape.ScopedComputeCount.wrapped_head_cut
    (R : ScopedComputeCount (PiInertStage D n) cost Δ source out)
    (H : WrappedConstHead c source) (HN : ¬ WrappedConstHead c out) :
    WrappedHeadCut D n Δ c source out cost := by
  classical
  induction R with
  | base HR => exact ⟨_, _, _, .hole, 0, 0, rfl, .beta .refl, HR, H, HN, .beta .refl⟩
  | beta R => exact (HN (H.beta R)).elim
  | trans R₁ R₂ ih₁ ih₂ =>
    rename_i m Δ a mid j out
    by_cases HM : WrappedConstHead c mid
    · obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩ := ih₂ HM HN
      exact ⟨Θ, a, b, C, _, ct, by omega, R₁.trans RP, HR, HS, HN, RT⟩
    · obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩ := ih₁ H HM
      exact ⟨Θ, a, b, C, cp, _, by omega, RP, HR, HS, HN, RT.trans R₂⟩
  | app RF RX ihf ihx =>
    rename_i m Δ f f' j x x'
    cases H with
    | app H =>
      obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩ := ihf H (fun HH => HN (.app HH))
      refine ⟨Θ, a, b, .appFn C x, cp, ct+j, by omega, ?_, HR, HS, HN, ?_⟩
      · simpa only [ScopedHole.plug, Nat.add_zero] using RP.app (ScopedComputeCount.beta BetaRed.refl)
      · simpa only [ScopedHole.plug] using RT.app RX
    | identity H =>
      obtain ⟨A', rfl, _⟩ := RF.forget.pi_inert_identity_lam
      obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩ := ihx H (fun HH => HN (.identity HH))
      refine ⟨Θ, a, b, .appArg (.lam A' (.bvar 0)) C, m+cp, ct, by omega,
        ?_, HR, HS, HN, ?_⟩
      · simpa only [ScopedHole.plug] using RF.app RP
      · simpa only [ScopedHole.plug, Nat.zero_add] using ScopedComputeCount.app (ScopedComputeCount.beta BetaRed.refl) RT
  | proj => cases H
  | lam RA RB ihA ihb =>
    rename_i m Δ A A' j body body'
    cases H with
    | lam H =>
      obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩ := ihb H (fun HH => HN (.lam HH))
      refine ⟨Θ, a, b, .lamBody A C, cp, m+ct, by omega, ?_, HR, HS, HN, ?_⟩
      · simpa only [ScopedHole.plug, Nat.zero_add] using ScopedComputeCount.lam (ScopedComputeCount.beta BetaRed.refl) RP
      · simpa only [ScopedHole.plug] using RA.lam RT
  | forallE => cases H

/-- Actual typing at the original path source supplies the exact selected
root's typing in its hole context. Both counted paths remain unchanged. -/
theorem WrappedHeadCut.typed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source) (H : WrappedHeadCut D n Δ c source out cost) :
    ∃ Θ a b, ∃ C : ScopedHole Δ Θ, ∃ cp ct,
      cp+1+ct = cost ∧ ScopedComputeCount (PiInertStage D n) cp Δ source (C.plug a) ∧
      TypedSource Θ a ∧ PiInertStage D n Θ a b ∧ WrappedConstHead c a ∧ ¬ WrappedConstHead c b ∧
      ScopedComputeCount (PiInertStage D n) ct Δ (C.plug b) out := by
  obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩ := H
  exact ⟨Θ, a, b, C, cp, ct, hc, RP, C.typed (HT.pi_inert_compute heq hs RP.forget), HR, HS, HN, RT⟩

/-- A head-losing path selected from the actual execution, with its typed
source and a local primitive count bounded by the original continuation cost.
The local cut retains both paths and its hole; target Eq argument ancestry
through the earlier scopes is not yet part of this witness. -/
def TypedWrappedHeadLoss (D : Definitions) (c : Name) (budget : Nat) : Prop :=
  ∃ Δ n cost source endpoint, cost ≤ budget ∧ TypedSource Δ source ∧
    WrappedHeadCut D n Δ c source endpoint cost

/-- Follow the actual mixed continuation until one of its application paths
loses the Eq head. Retained lambdas, identity payloads and arbitrary endpoint
substitutions preserve the invariant between paths. The selected path has its
actual source typing and costs at most the original continuation. -/
theorem PiInertTypedContinuationRun.wrapped_head_loss
    (heq : env.HasCanonicalEq)
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck)
    (HC : WrappedConstHead ``Eq.rec e) (HE : CarrierExposure out) :
    TypedWrappedHeadLoss D ``Eq.rec ck := by
  classical
  induction H with
  | terminal => exact (HC.eq_not_exposed heq HE).elim
  | application HToriginal W HT R HK ih =>
    rename_i Δ e Θ τ args n cs e' K ck
    have HS := (HC.subst τ).mkApps args
    by_cases HH : WrappedConstHead ``Eq.rec e'
    · obtain ⟨Ξ, m, cost, source, endpoint, hcost, HT, Hcut⟩ := ih HH
      exact ⟨Ξ, m, cost, source, endpoint, by omega, HT, Hcut⟩
    · exact ⟨Θ, n, cs, _, e', by omega, HT, R.wrapped_head_cut HS HH⟩
  | retained _ _ _ _ _ ih => exact ih ((WrappedConstHead.lam HC).mkApps _)

/-- A typed Eq minimum ending at an exposed carrier contains a head-losing
primitive in its body or its actual continuation, even with arbitrarily many
retained and application frames. The selected local path is cost bounded;
no assumption of exposure at an intermediate endpoint is used. -/
theorem PiInertTypedContinuationMinimum.wrapped_head_loss
    (heq : env.HasCanonicalEq)
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost)
    (HC : WrappedConstHead ``Eq.rec source) (HE : CarrierExposure out) :
    TypedWrappedHeadLoss D ``Eq.rec cost := by
  classical
  obtain ⟨K, n, cb, ck, e, HT, R, HR, hc, _⟩ := H
  by_cases HH : WrappedConstHead ``Eq.rec e
  · obtain ⟨Ξ, m, localCost, localSource, endpoint, hcost, HT, Hcut⟩ := HR.wrapped_head_loss heq HH HE
    exact ⟨Ξ, m, localCost, localSource, endpoint, by omega, HT, Hcut⟩
  · exact ⟨Δ, n, cb, source, e, by omega, HT, R.wrapped_head_cut HC HH⟩

/-- Pi-inert root restriction forces a wrapped head at a selected primitive
to be an ordinary constant spine. A retained lambda or identity application
cannot itself be the source of a root primitive. -/
theorem WrappedConstHead.primitive_source
    (H : WrappedConstHead c source) (HR : PiInertStage D n Δ source target) :
    ∃ ls args, source = ProofShape.mkApps (.const c ls) args := by
  rcases H.spine_form with HS | ⟨A, b, args, rfl⟩
  · exact HS
  · rcases HR.2 with HH | ⟨u, E⟩
    · exact (lambda_spine_not_primitive A b args HH).elim
    · cases args using List.snoc_induction with
      | nil => cases E
      | snoc args x => rw [ProofShape.mkApps_snoc] at E; cases E

/-- Level conversion, constant expansion, identity and function eta all
preserve a wrapped head. A selected head-losing root excludes all four,
independently of any minimality or raw guarded substitution premise. -/
theorem WrappedConstHead.loss_exclusions
    (H : WrappedConstHead c source) (HN : ¬ WrappedConstHead c target) :
    ¬ LevelPrimitive univs source target ∧ ¬ ConstantExpansion source target ∧
      (∀ Recovery, ¬ NativeIdentityExpansion Recovery Δ source target) ∧
      (∀ Recovery, ¬ NativeEtaExpansion Recovery Δ source target) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro HL
    cases HL with
    | sort => cases H
    | const => cases H; exact HN .const
  · intro HC
    cases HC
    exact HN (.app (.lam (H.liftN 1 0)))
  · intro Recovery HI
    cases HI
    exact HN (.identity H)
  · intro Recovery HEta
    cases HEta
    exact HN (.lam (.app (H.liftN 1 0)))

/-- Extract the typed constant-spine root from a cost-bounded actual loss.
It excludes levels and all three administrative expansions, including native
function eta. The argument vector's original target completion remains a
separate ancestry requirement for semantic singleton readout. -/
theorem TypedWrappedHeadLoss.root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedWrappedHeadLoss D c budget) :
    ∃ Δ Θ n source endpoint ls args target cp ct, ∃ C : ScopedHole Δ Θ,
      cp+1+ct ≤ budget ∧ TypedSource Δ source ∧
      ScopedComputeCount (PiInertStage D n) cp Δ source (C.plug (ProofShape.mkApps (.const c ls) args)) ∧
      TypedSource Θ (ProofShape.mkApps (.const c ls) args) ∧
      PiInertStage D n Θ (ProofShape.mkApps (.const c ls) args) target ∧
      ¬ WrappedConstHead c target ∧
      ¬ LevelPrimitive univs (ProofShape.mkApps (.const c ls) args) target ∧
      ¬ ConstantExpansion (ProofShape.mkApps (.const c ls) args) target ∧
      (∀ Recovery, ¬ NativeIdentityExpansion Recovery Θ (ProofShape.mkApps (.const c ls) args) target) ∧
      (∀ Recovery, ¬ NativeEtaExpansion Recovery Θ (ProofShape.mkApps (.const c ls) args) target) ∧
      ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint := by
  obtain ⟨Δ, n, cost, source, endpoint, hcost, HT, H⟩ := H
  obtain ⟨Θ, a, b, C, cp, ct, hc, RP, HTroot, HR, HS, HN, RT⟩ := H.typed heq hs HT
  obtain ⟨ls, args, rfl⟩ := HS.primitive_source HR
  obtain ⟨HL, HC, HI, HE⟩ := HS.loss_exclusions (Δ := Θ) HN
  exact ⟨Δ, Θ, n, source, endpoint, ls, args, b, cp, ct, C,
    by omega, HT, RP, HTroot, HR, HN, HL, HC, HI, HE, RT⟩

/-- A short Eq head-losing primitive can only be one of the two singleton
forms. Native eta is excluded by the head invariant itself. This theorem
still needs the actual short-arity bound, not just root typing. -/
theorem pi_inert_short_eq_head_loss_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length ≤ 5)
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target) :
    ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∨
      ∃ k, k < n ∧ CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
  have HS := (WrappedConstHead.const (c := ``Eq.rec) (ls := ls)).mkApps args
  obtain ⟨HL, HC, HI, HE⟩ := HS.loss_exclusions (Δ := Δ) HN
  rcases pi_inert_eq_short_guarded_root heq hs hreg hoff hRec HT hlen HR HL HC HI with
    HQ | ⟨k, hk, HG | HEta⟩
  · exact .inl HQ
  · exact .inr ⟨k, hk, HG⟩
  · exact (HE _ HEta).elim

end Lean4Lean.VEnv.Strengthening
