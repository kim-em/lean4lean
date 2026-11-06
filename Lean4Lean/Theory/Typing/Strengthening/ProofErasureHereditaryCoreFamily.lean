import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFamilyFeedback

/-! # Constructing substitution-stable full-core computation histories

Stability is retained for a particular history, rather than postulated for
every CoreFamilyCast certificate. Typed core and eta seeds construct it;
composition, joins and residuals preserve it. Cast consumers reconstruct their
typed syntax after substitution and consume the retained endpoint history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A particular full-core certificate together with its reconstructed instances
under every interpreted typed substitution. There is deliberately no promotion
from arbitrary earlier comparison leaves. The constructors below prove this
property for concrete seeds and recursively composed histories. -/
structure CoreFamilyCast.Hereditary (D : Definitions) (n : Nat) (kind : CoreFamilyKind)
    (Δ : List ProofShape) (a b : ProofShape) : Prop where
  base : CoreFamilyCast D n kind Δ a b
  future : ∀ {Δ' τ}, ContextSubstitution Δ Δ' τ →
    CoreFamilyCast D n kind Δ' (a.subst τ) (b.subst τ)

/-- An instance retains all later instances by composing actual context
substitutions. Its finite stage is unchanged. -/
theorem CoreFamilyCast.Hereditary.substitute
    (H : CoreFamilyCast.Hereditary D n kind Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    CoreFamilyCast.Hereditary D n kind Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.comp V)

/-- Ordinary full-core paths are substitution-stable typed seeds; the output
may be a raw reduct and need not have a selected original representative. -/
theorem CoreFamilyCast.Hereditary.core
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) out) :
    CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ) (proofErase Γ e) out := by
  refine ⟨.core hΓ ht R, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have R' := R.subst (fun H => erased_level_core_subst H) (σ := τ)
  rw [← proofErase_subst_with hΓ₀ WS ht ES] at R' ⊢
  rw [← EΓ₀]
  exact .core hΓ₀ (ht.subst henv.orderedStrong WS hΓ₀) R'

/-- Typed displayed eta is a stable common-mode seed even when its endpoints
do not join in the ordinary core. The two actual source typings share a type. -/
theorem CoreFamilyCast.Hereditary.eta
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a T)
    (hb : env.HasType univs Γ b T) (H : EtaHead (proofErase Γ a) (proofErase Γ b)) :
    CoreFamilyCast.Hereditary D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨.raise (Nat.zero_le n) (.prior (.prior (.core (.eta hΓ ha hb H)))), ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have H' := H.subst (σ := τ)
  rw [← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H' ⊢
  rw [← EΓ₀]
  exact .raise (Nat.zero_le n) (.prior (.prior (.core (.eta hΓ₀
    (ha.subst henv.orderedStrong WS hΓ₀) (hb.subst henv.orderedStrong WS hΓ₀) H'))))

/-- A retained common body comparison constructs common lambda comparison.
The written domains may differ, and all future domain computation is handled
by the interpreted body children in the recursive grammar. -/
theorem CoreFamilyCast.Hereditary.lamCommon
    (H : CoreFamilyCast.Hereditary D n (.compare true) (A :: Δ) b c) :
    CoreFamilyCast.Hereditary D n (.compare true) Δ (.lam A b) (.lam C c) := by
  refine ⟨.lamCommon (fun W => H.future W), ?_⟩
  intro Δ' τ W
  exact .lamCommon (fun V => (H.substitute W.cons).future V)

/-- Shared domain sorts and retained common domain comparison give lambda
comparison in either mode. Body histories survive arbitrary future substitution
and computation of the displayed domains. -/
theorem CoreFamilyCast.Hereditary.lamSorted
    (SA : DomainSort Δ A u) (SC : DomainSort Δ C u)
    (HA : CoreFamilyCast.Hereditary D n (.compare true) Δ A C)
    (HB : CoreFamilyCast.Hereditary D n (.compare mode) (A :: Δ) b c) :
    CoreFamilyCast.Hereditary D n (.compare mode) Δ (.lam A b) (.lam C c) := by
  refine ⟨.lamSorted SA SC HA.base (fun W => HB.future W), ?_⟩
  intro Δ' τ W
  exact .lamSorted (W.sort SA) (W.sort SC) (HA.future W)
    (fun V => (HB.substitute W.cons).future V)

/-- Dependent Pi domains and bodies retain their actual common sorts. The body
certificates are transported into the computed left-domain context at readout. -/
theorem CoreFamilyCast.Hereditary.forallSorted
    (SA : DomainSort Δ A u) (SC : DomainSort Δ C u)
    (SB : DomainSort (A :: Δ) B v) (SE : DomainSort (A :: Δ) E v)
    (HA : CoreFamilyCast.Hereditary D n (.compare true) Δ A C)
    (HB : CoreFamilyCast.Hereditary D n (.compare true) (A :: Δ) B E) :
    CoreFamilyCast.Hereditary D n (.compare mode) Δ (.forallE A B) (.forallE C E) := by
  refine ⟨.forallSorted SA SC SB SE HA.base (fun W => HB.future W), ?_⟩
  intro Δ' τ W
  exact .forallSorted (W.sort SA) (W.sort SC)
    (ContextSubstitution.sort W.cons SB) (ContextSubstitution.sort W.cons SE)
    (HA.future W) (fun V => (HB.substitute W.cons).future V)

/-- Sequential computation retains the same substituted intermediate. -/
theorem CoreFamilyCast.Hereditary.trans
    (H : CoreFamilyCast.Hereditary D n .compute Δ a b)
    (K : CoreFamilyCast.Hereditary D n .compute Δ b c) :
    CoreFamilyCast.Hereditary D n .compute Δ a c :=
  ⟨.trans H.base K.base, fun W => .trans (H.future W) (K.future W)⟩

/-- A common output stays common after substitution, giving either comparison
mode without an assumption of confluence for any guarded stage. -/
theorem CoreFamilyCast.Hereditary.join
    (H : CoreFamilyCast.Hereditary D n .compute Δ a shared)
    (K : CoreFamilyCast.Hereditary D n .compute Δ b shared) :
    CoreFamilyCast.Hereditary D n (.compare mode) Δ a b :=
  ⟨.join H.base K.base, fun W => .join (H.future W) (K.future W)⟩

/-- Computation prefixes and a retained comparison compose after every future
substitution, including substitutions that expose new beta redexes. -/
theorem CoreFamilyCast.Hereditary.prefixes
    (H : CoreFamilyCast.Hereditary D n .compute Δ a a')
    (K : CoreFamilyCast.Hereditary D n .compute Δ b b')
    (C : CoreFamilyCast.Hereditary D n (.compare mode) Δ a' b') :
    CoreFamilyCast.Hereditary D n (.compare mode) Δ a b :=
  ⟨.prefixes H.base K.base C.base,
    fun W => .prefixes (H.future W) (K.future W) (C.future W)⟩

/-- Residual histories persist because the entire ordinary core is closed
under raw substitution; fresh reductions are handled by certificate readout. -/
theorem CoreFamilyCast.Hereditary.reducts
    (H : CoreFamilyCast.Hereditary D n (.compare mode) Δ a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a')
    (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    CoreFamilyCast.Hereditary D n (.compare mode) Δ a' b' :=
  ⟨.reducts H.base RA RB, fun W => .reducts (H.future W)
    (RA.subst (fun R => erased_level_core_subst R))
    (RB.subst (fun R => erased_level_core_subst R))⟩

/-- Symmetry preserves the retained substitution histories. -/
theorem CoreFamilyCast.Hereditary.symm
    (H : CoreFamilyCast.Hereditary D n (.compare mode) Δ a b) :
    CoreFamilyCast.Hereditary D n (.compare mode) Δ b a :=
  ⟨.symm H.base, fun W => .symm (H.future W)⟩

/-- Stage raising is independent of the future substitution. -/
theorem CoreFamilyCast.Hereditary.raise (hle : n ≤ m)
    (H : CoreFamilyCast.Hereditary D n kind Δ a b) :
    CoreFamilyCast.Hereditary D m kind Δ a b :=
  ⟨.raise hle H.base, fun W => .raise hle (H.future W)⟩

/-- A certified cast inside any typed consumer retains its history under
arbitrary typed substitutions. The child supplies common-mode endpoint checks
at the same earlier stage; no inferred substitution closure is invoked. -/
theorem CoreFamilyCast.Hereditary.castConsumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (H : CoreFamilyCast.Hereditary D n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ X) (proofErase Γ Y)) :
    CoreFamilyCast.Hereditary D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  refine ⟨.castConsumer hu hΓ hX hY hq hx ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have HXY := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY
    (.carrierChecked (H.base.forward heq hs hl hcon hc hreg hoff hD .refl .refl))
  have hcast : env.HasType univs Γ (typeCast u X Y q x) X :=
    HXY.symm.defeq (IsDefEq.typeCast_refl henv heq hu hΓ HXY hq hx).hasType.1
  have hleft := ht.instN henv Ctx.InstN.zero hcast
  have hright := ht.instN henv Ctx.InstN.zero hx
  have hX' := hX.subst henv.orderedStrong WS hΓ₀
  have hY' := hY.subst henv.orderedStrong WS hΓ₀
  have hq' := hq.subst henv.orderedStrong WS hΓ₀
  have hx' := hx.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hX) ⟨hΓ₀, u, hX'⟩
  have H' := H.future W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hX ES,
    ← proofErase_subst_with hΓ₀ WS hY ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, VExpr.typeCast_subst]
  exact .castConsumer hu hΓ₀ hX' hY' (by simpa only [VExpr.eqApp_subst, VExpr.subst] using hq')
    hx' ht' H'

/-- Annotation consumers preserve substitution histories with either mode of
domain comparison. The actual shared sort is retained through each residual;
no conversion of arbitrary common checks into inferred checks is assumed. -/
theorem CoreFamilyCast.Hereditary.annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (H : CoreFamilyCast.Hereditary D n (.compare domainMode) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C)) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
  refine ⟨.annotation hΓ hA hC hb ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨v, hS⟩ := hA.isType henv hΓ
  have HAC := ((proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hA hC
    (H.base.forward heq hs hl hcon hc hreg hoff hD .refl .refl)).1 ⟨_, hS⟩).of_l henv hΓ hA
  have HL := IsDefEq.lamDF HAC hb
  have hleft := ht.instN henv Ctx.InstN.zero HL.hasType.1
  have hright := ht.instN henv Ctx.InstN.zero HL.hasType.2
  obtain ⟨w, hPi⟩ := HL.hasType.1.isType henv hΓ
  have hA' := hA.subst henv.orderedStrong WS hΓ₀
  have hC' := hC.subst henv.orderedStrong WS hΓ₀
  have hb' := hb.subst henv.orderedStrong (WS.lift henv.ordered hA) ⟨hΓ₀, u, hA'⟩
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hPi)
    ⟨hΓ₀, w, hPi.subst henv.orderedStrong WS hΓ₀⟩
  have H' := H.future W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hA ES,
    ← proofErase_subst_with hΓ₀ WS hC ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, VExpr.subst]
  exact .annotation hΓ₀ hA' hC' hb' ht' H'

end Lean4Lean.VEnv.Strengthening
