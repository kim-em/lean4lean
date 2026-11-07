import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRankedDomainTransport

/-! # Retained function action through typed futures and dependent conversion

Function action is an additional induction component, not an extraction from
completed function histories. Lambda action is exactly paired body evidence;
type conversion uses hereditary transport of the domain and instantiated
codomain, without reconstructing a larger strong derivation for recursion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The missing carrier-transport component quantified over actual typed
substitutions. Each future may choose its own finite stages. No completeness
or uniform bound over arbitrary future substitutions is asserted. -/
def HereditaryFiniteCarrierTransport (D : Definitions) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∀ {Γ₀ σ}, OnCtx Γ₀ (env.IsType univs) → Ctx.SubstEq env univs Γ₀ σ σ Γ →
    FiniteCarrierTransport D Γ₀ (A.subst σ) (B.subst σ)

/-- A supplied argument extends a typed substitution directly. The hereditary
codomain hypothesis is used in its original scope, with no new strong proof
or rank bound for its instantiated equality. -/
theorem HereditaryFiniteCarrierTransport.instantiate
    (H : HereditaryFiniteCarrierTransport D (A::Γ) B C)
    (hA : env.HasType univs Γ A (.sort u))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hx : env.HasType univs Γ₀ x (A.subst σ)) :
    FiniteCarrierTransport D Γ₀ ((B.subst σ.lift).inst x) ((C.subst σ.lift).inst x) := by
  rw [VExpr.inst_lift_cons, VExpr.inst_lift_cons]
  exact H hΓ₀ (Ctx.SubstEq.cons W hA hx)

/-- Function action at all actual typed futures and all carrier-related
argument pairs. The output keeps the left dependent carrier. This is evidence
to construct simultaneously with term histories, not a consequence of a
completed history for f and g at their assigned Pi. -/
def FinitePiInertFunctionAction (D : Definitions) (Γ : List VExpr) (A B f g : VExpr) : Prop :=
  ∀ {Γ₀ σ x y stage}, OnCtx Γ₀ (env.IsType univs) → Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ₀ x (A.subst σ) → env.HasType univs Γ₀ y (A.subst σ) →
    PiInertCarrierHistory D stage (proofEraseCtx Γ₀) (proofErase Γ₀ (A.subst σ))
      (proofErase Γ₀ x) (proofErase Γ₀ y) →
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ₀)
      (proofErase Γ₀ ((B.subst σ.lift).inst x))
      (proofErase Γ₀ (.app (f.subst σ) x)) (proofErase Γ₀ (.app (g.subst σ) y))

/-- The paired-body induction component needed by lambda action. The two
arguments may differ and need only have a carrier history, not joined argument
histories. Its general construction from strong body derivations remains open. -/
def FinitePiInertPairedBody (D : Definitions) (Γ : List VExpr) (A B b c : VExpr) : Prop :=
  ∀ {Γ₀ σ x y stage}, OnCtx Γ₀ (env.IsType univs) → Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ₀ x (A.subst σ) → env.HasType univs Γ₀ y (A.subst σ) →
    PiInertCarrierHistory D stage (proofEraseCtx Γ₀) (proofErase Γ₀ (A.subst σ))
      (proofErase Γ₀ x) (proofErase Γ₀ y) →
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ₀)
      (proofErase Γ₀ ((B.subst σ.lift).inst x))
      (proofErase Γ₀ ((b.subst σ.lift).inst x)) (proofErase Γ₀ ((c.subst σ.lift).inst y))

/-- Paired body evidence constructs action for two actual lambdas at their
assigned Pi. Written domains may differ from the assigned domain and each
other. Ordinary beta prefixes preserve the exact left dependent carrier and
all residual/future clauses of the returned history. -/
theorem FinitePiInertPairedBody.lambda_action
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (H : FinitePiInertPairedBody D Γ A B b c) :
    FinitePiInertFunctionAction D Γ A B (.lam C b) (.lam E c) := by
  intro Γ₀ σ x y stage hΓ₀ W hx hy HX
  obtain ⟨n, HB⟩ := H hΓ₀ W hx hy HX
  have hf' : env.HasType univs Γ₀ ((VExpr.lam C b).subst σ)
      (.forallE (A.subst σ) (B.subst σ.lift)) := hf.subst henv.orderedStrong W hΓ₀
  have hg' : env.HasType univs Γ₀ ((VExpr.lam E c).subst σ)
      (.forallE (A.subst σ) (B.subst σ.lift)) := hg.subst henv.orderedStrong W hΓ₀
  have hfx := hf'.app hx
  have hgy := hg'.app hy
  exact ⟨n, PiInertCarrierHistory.prefixes
    (PiInertEvidence.core hs hc hΓ₀ hfx (.beta (proofErase_beta_forward hΓ₀ hfx .beta)))
    (PiInertEvidence.core hs hc hΓ₀ hgy (.beta (proofErase_beta_forward hΓ₀ hgy .beta))) HB⟩

/-- Conversely lambda action returns the exact paired body instances by beta
reduction. This does not extract action from a completed function history; it
calibrates the extra action component at displayed lambdas. -/
theorem FinitePiInertFunctionAction.lambda_body
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (H : FinitePiInertFunctionAction D Γ A B (.lam C b) (.lam E c)) :
    FinitePiInertPairedBody D Γ A B b c := by
  intro Γ₀ σ x y stage hΓ₀ W hx hy HX
  obtain ⟨n, HA⟩ := H hΓ₀ W hx hy HX
  have hf' : env.HasType univs Γ₀ ((VExpr.lam C b).subst σ)
      (.forallE (A.subst σ) (B.subst σ.lift)) := hf.subst henv.orderedStrong W hΓ₀
  have hg' : env.HasType univs Γ₀ ((VExpr.lam E c).subst σ)
      (.forallE (A.subst σ) (B.subst σ.lift)) := hg.subst henv.orderedStrong W hΓ₀
  have hfx := hf'.app hx
  have hgy := hg'.app hy
  exact ⟨n, HA.endpoint_reducts
    (.beta (proofErase_beta_forward hΓ₀ hfx .beta))
    (.beta (proofErase_beta_forward hΓ₀ hgy .beta))⟩

/-- At actual displayed lambdas, retained action and paired body evidence are
exactly equivalent. No fixed output stage or common argument reduct is required. -/
theorem finite_pi_inert_lambda_action_iff
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B)) :
    FinitePiInertFunctionAction D Γ A B (.lam C b) (.lam E c) ↔
      FinitePiInertPairedBody D Γ A B b c :=
  ⟨FinitePiInertFunctionAction.lambda_body hf hg,
    FinitePiInertPairedBody.lambda_action hs hc hf hg⟩

/-- Action changes its dependent function type using hereditary transport of
the domain and codomain. Future argument typings are converted by the actual
domain equality, their carrier history uses its retained semantic transport,
and the output carrier uses the codomain hypothesis instantiated at the left
argument. No global application law or new recursive strong cut is used. -/
theorem FinitePiInertFunctionAction.convert
    (hAC : env.IsDefEq univs Γ A C (.sort u))
    (domains : HereditaryFiniteCarrierTransport D Γ A C)
    (codomains : HereditaryFiniteCarrierTransport D (C::Γ) B E)
    (H : FinitePiInertFunctionAction D Γ A B f g) :
    FinitePiInertFunctionAction D Γ C E f g := by
  intro Γ₀ σ x y stage hΓ₀ W hx hy HX
  have hAC' := hAC.subst henv.orderedStrong W hΓ₀
  have hxA := hAC'.symm.defeq hx
  have hyA := hAC'.symm.defeq hy
  obtain ⟨m, HM⟩ := (domains hΓ₀ W (proofErase Γ₀ x) (proofErase Γ₀ y)).mpr ⟨stage, HX⟩
  obtain ⟨n, HN⟩ := H hΓ₀ W hxA hyA HM
  exact (codomains.instantiate hAC.hasType.2 hΓ₀ W hx
    (proofErase Γ₀ (.app (f.subst σ) x)) (proofErase Γ₀ (.app (g.subst σ) y))).mp ⟨n, HN⟩

/-- The type-conversion action case at forallEDF uses the actual rank-k
domain and right-context codomain children of its rank-(k+1) equality. The
hereditary IH is consumed before substitution, so no instantiated strong
height is required and no rank-increasing symmetry proof is recursively used. -/
theorem strong_forall_function_action_of_lower
    (hA : StrongBounded env univs k Γ A C (.sort u))
    (hBE : StrongBounded env univs k (C::Γ) B E (.sort v))
    (lower : ∀ {j Δ X Y w}, j < k+1 → StrongBounded env univs j Δ X Y (.sort w) →
      HereditaryFiniteCarrierTransport D Δ X Y)
    (H : FinitePiInertFunctionAction D Γ A B f g) :
    FinitePiInertFunctionAction D Γ C E f g :=
  H.convert hA.strong.defeq (lower (Nat.lt_succ_self k) hA) (lower (Nat.lt_succ_self k) hBE)

/-- At a lambda parent, the paired-body component is requested only for the
original rank-k body equality. Formation and endpoint typings are supplied
separately, not converted into new higher-rank body proofs for recursion. -/
theorem strong_lambda_action_of_lower
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (hbody : StrongBounded env univs k (A::Γ) b c B)
    (lower : ∀ {j b c}, j < k+1 → StrongBounded env univs j (A::Γ) b c B →
      FinitePiInertPairedBody D Γ A B b c) :
    FinitePiInertFunctionAction D Γ A B (.lam C b) (.lam E c) :=
  FinitePiInertPairedBody.lambda_action hs hc hf hg (lower (Nat.lt_succ_self k) hbody)

/-- Action supplies the fresh-body history by a genuine weakening future and
a reflexive fresh argument. This is the easy direction: no function-history
inversion or uniform stage across all futures is assumed. -/
theorem FinitePiInertFunctionAction.fresh_body
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : FinitePiInertFunctionAction D Γ A B f g) :
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx (A::Γ)) (proofErase (A::Γ) B)
      (proofErase (A::Γ) (.app f.lift (.bvar 0)))
      (proofErase (A::Γ) (.app g.lift (.bvar 0))) := by
  let σ : VExpr.Subst := VExpr.Subst.id.lift_r (.skip .refl)
  have EW (e : VExpr) : e.subst σ = e.lift := by
    simp only [σ, ← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift']
  have EC : σ.cons (.bvar 0) = VExpr.Subst.id := by
    funext i
    cases i <;> rfl
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W : Ctx.SubstEq env univs (A::Γ) σ σ Γ := (Ctx.SubstEq.id henv.ordered hΓ).skip henv.ordered
  have hx : env.HasType univs (A::Γ) (.bvar 0) (A.subst σ) := by
    rw [EW]
    exact .bvar .zero
  have HR : PiInertEvidence D 0 .compute (proofEraseCtx (A::Γ))
      (proofErase (A::Γ) (.bvar 0)) (proofErase (A::Γ) (.bvar 0)) :=
    .core hs hc hΓA hx .refl
  have HX : PiInertCarrierHistory D 0 (proofEraseCtx (A::Γ)) (proofErase (A::Γ) (A.subst σ))
      (proofErase (A::Γ) (.bvar 0)) (proofErase (A::Γ) (.bvar 0)) :=
    (HR.join hc HR).carrier_history
  obtain ⟨n, HN⟩ := H hΓA W hx hx HX
  exact ⟨n, by simpa only [EW, VExpr.inst_lift_cons, EC, VExpr.subst_id] using HN⟩

/-- Retained action implies an ordinary completed history for actual functions.
Thus action strengthens the old induction component; the converse is neither
used nor asserted. Proof-valued functions use proof erasure, and other functions
use the newly obtained fresh-body history with the existing function rule. -/
theorem FinitePiInertFunctionAction.history
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (H : FinitePiInertFunctionAction D Γ A B f g) :
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ f) (proofErase Γ g) := by
  by_cases hp : IsProof Γ f
  · have hq := isProof_of_common_type hΓ hf hg hp
    have HR : PiInertEvidence D 0 .compute (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ f) :=
      .core hs hc hΓ hf .refl
    have HC := (HR.join hc HR).carrier_history (C := proofErase Γ (.forallE A B))
    rw [proofErase_eq_proof.2 hp] at HC
    exact ⟨0, by simpa only [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hq] using HC⟩
  have hq : ¬ IsProof Γ g := fun hq => hp (isProof_of_common_type hΓ hg hf hq)
  obtain ⟨n, HB⟩ := H.fresh_body hs hc hΓ hA
  rw [proofEraseCtx, proofErase_eta_body hΓ hA hf hp, proofErase_eta_body hΓ hA hg hq] at HB
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  refine ⟨n, ?_⟩
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
  exact HB.function hs (DomainSort.of_typed hΓ hA)

/-- The variable body of identity consumes the supplied argument history
exactly, at its original stage, after every typed future. This seed requires
neither a common argument reduct nor any carrier-transport assumption. -/
theorem finite_pi_inert_identity_body :
    FinitePiInertPairedBody D Γ A A.lift (.bvar 0) (.bvar 0) := by
  intro Γ₀ σ x y stage hΓ₀ W hx hy HX
  refine ⟨stage, ?_⟩
  simpa only [VExpr.lift_subst_lift, VExpr.inst_lift, VExpr.subst,
    VExpr.Subst.lift, VExpr.inst, VExpr.instVar_zero] using HX

/-- The actual identity function has full retained action for arbitrary typed
carrier-related arguments, including those without a shared computation result.
No universal completed-history-to-action rule is used. -/
theorem finite_pi_inert_identity_action
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hA : env.HasType univs Γ A (.sort u)) :
    FinitePiInertFunctionAction D Γ A A.lift (.lam A (.bvar 0)) (.lam A (.bvar 0)) :=
  FinitePiInertPairedBody.lambda_action hs hc (.lam hA (.bvar .zero)) (.lam hA (.bvar .zero))
    finite_pi_inert_identity_body

end Lean4Lean.VEnv.Strengthening
