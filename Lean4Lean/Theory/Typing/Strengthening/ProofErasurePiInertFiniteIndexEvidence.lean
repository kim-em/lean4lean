import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConversionCoverageFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecConsumer

/-! # Eq-index evidence with a stage chosen after substitution

Paired interpretation supplies a finite world history separately for each
typed substitution. It does not supply one stage uniform over all typed
substitutions. Eq consumers need only the former: each selected instance keeps
its stage across core-world futures. The resulting computations construct
carrier transport and recursive call conversion without a uniform-stage gap.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Finite index evidence with its stage chosen after a typed substitution.
Every chosen history still retains that stage across all core-world futures.
Construction for arbitrary original strong comparisons remains open; this
definition does not exchange the substitution and stage quantifiers. -/
def PiInertFiniteHistory (D : Definitions) (Δ : List ProofShape) (T a b : ProofShape) : Prop :=
  ∀ {Λ σ}, ContextSubstitution Δ Λ σ →
    ∃ n, PiInertWorldHistory D n Λ (T.subst σ) (a.subst σ) (b.subst σ)

/-- Directed computation with a finite stage for each typed-substitution
instance. The retained ordinary-core output tail and all core-world futures
belong to that same chosen instance. No uniform stage is asserted. -/
def PiInertFiniteComputation (D : Definitions) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∀ {Λ σ}, ContextSubstitution Δ Λ σ →
    ∃ n, PiInertWorldComputation D n Λ (a.subst σ) (b.subst σ)

/-- Paired interpretation supplies diagonal index evidence when its variable
requirements have diagonal realizations. This premise is explicit; arbitrary
typed substitution does not automatically interpret every recursive image. -/
theorem PiInertGuardedPairInterpretation.finite_history
    (H : PiInertGuardedPairInterpretation D Δ uses a b T U p q)
    (images : ∀ {Λ σ}, ContextSubstitution Δ Λ σ → PiInertGuardedPairImages D Δ Λ σ σ uses) :
    PiInertFiniteHistory D Δ T a b := by
  intro Λ σ W
  exact (H.run W W (images W)).forward.base.ground.history

/-- Empty image requirements construct the diagonal environments outright.
The source interpreter may have arbitrary recursive result profiles. -/
theorem PiInertGuardedPairInterpretation.empty_finite_history
    (H : PiInertGuardedPairInterpretation D Δ [] a b T U p q) :
    PiInertFiniteHistory D Δ T a b := by
  intro Λ σ W
  exact H.finite_history (fun _ _ _ h => nomatch h) W

/-- Finite histories keep their quantifier order after typed substitution. -/
theorem PiInertFiniteHistory.substitute (H : PiInertFiniteHistory D Δ T a b)
    (W : ContextSubstitution Δ Λ σ) :
    PiInertFiniteHistory D Λ (T.subst σ) (a.subst σ) (b.subst σ) := by
  intro Ξ τ V
  simp only [ProofShape.subst_subst]
  exact H (W.comp V)

/-- Finite computations likewise compose their typed-substitution inputs. -/
theorem PiInertFiniteComputation.substitute (H : PiInertFiniteComputation D Δ a b)
    (W : ContextSubstitution Δ Λ σ) :
    PiInertFiniteComputation D Λ (a.subst σ) (b.subst σ) := by
  intro Ξ τ V
  simp only [ProofShape.subst_subst]
  exact H (W.comp V)

/-- Uniform interpreted computation supplies the weaker per-instance bound. -/
theorem PiInertEvidence.finite_computation (H : PiInertEvidence D n .compute Δ a b) :
    PiInertFiniteComputation D Δ a b := fun W => ⟨n, (H.substitute W).world_computation⟩

/-- Uniform common comparison supplies finite index history at any carrier. -/
theorem PiInertEvidence.finite_history (H : PiInertEvidence D n (.compare true) Δ a b) :
    PiInertFiniteHistory D Δ T a b := by
  intro Λ σ W
  exact ⟨n, ((H.substitute W).carrier_history).world_history⟩

/-- A typed open term supplies reflexive index evidence under every typed
substitution. It needs no paired image assumptions, since both endpoints use
the same substitution rather than two unrelated environments. -/
theorem PiInertFiniteHistory.refl
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HA : TypedSource Δ a) :
    PiInertFiniteHistory D Δ T a a := by
  have R : PiInertEvidence D 0 .compute Δ a a := .of_core_join hc HA HA .refl
  intro Λ σ W
  exact (R.join (mode := true) hc R).finite_history W

/-- Independently retained endpoint computations preserve finite index
history. The maximum is chosen after substitution, and the three histories
retain it across the same core-world futures. No term transitivity is used. -/
theorem PiInertFiniteHistory.prefixes
    (H : PiInertFiniteHistory D Δ T a b)
    (RA : PiInertFiniteComputation D Δ a' a) (RB : PiInertFiniteComputation D Δ b' b) :
    PiInertFiniteHistory D Δ T a' b' := by
  intro Λ σ W
  obtain ⟨n, H⟩ := H W
  obtain ⟨m, RA⟩ := RA W
  obtain ⟨k, RB⟩ := RB W
  exact ⟨max n (max m k), PiInertWorldHistory.prefixes
    (RA.raise (by omega)) (RB.raise (by omega)) (H.raise (by omega))⟩

/-- A retained carrier computation preserves the complete finite index
history without strengthening its substitution quantifiers. -/
theorem PiInertFiniteHistory.carrier_prefix
    (H : PiInertFiniteHistory D Δ T a b) (R : PiInertFiniteComputation D Δ U T) :
    PiInertFiniteHistory D Δ U a b := by
  intro Λ σ W
  obtain ⟨n, H⟩ := H W
  obtain ⟨m, R⟩ := R W
  exact ⟨max n m, (H.raise (Nat.le_max_left n m)).carrier_prefix (R.raise (Nat.le_max_right n m))⟩

/-- Sequential finite computations choose a maximum only after substitution.
This does not assert a bound common to every substituted instance. -/
theorem PiInertFiniteComputation.trans (H : PiInertFiniteComputation D Δ a b)
    (K : PiInertFiniteComputation D Δ b c) : PiInertFiniteComputation D Δ a c := by
  intro Λ σ W
  obtain ⟨n, H⟩ := H W
  obtain ⟨m, K⟩ := K W
  exact ⟨max n m, (H.raise (Nat.le_max_left n m)).trans (K.raise (Nat.le_max_right n m))⟩

/-- The original instance of finite history reflects actual common-typed
equality. This derives typing information only, without promoting the history
to an interpretation uniform over arbitrary substitutions. -/
theorem PiInertFiniteHistory.actual_defeq
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    env.IsDefEq univs Γ a b A := by
  have W := PiInertCoreWorld.of_exact_actual (D := D) heq hc hΓ ContextRenaming.identity
  obtain ⟨n, K⟩ := H W.typed
  simp only [ProofShape.subst_id] at K
  exact proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((K.base .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))

/-- Eq computation inside any typed consumer needs only world-history
futures for its index comparison. The same selected stage plus one works
through those worlds, including beta duplication inside the consumer. -/
theorem PiInertWorldHistory.eq_rec_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t S)
    (H : PiInertWorldHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertWorldComputation D (n+1) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) (proofErase Γ (t.inst m)) := by
  refine ⟨PiInertInterpret.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ hr ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W.typed hΓ rfl
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H.base .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have hm := (eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T hr).hasType.2
  have hleft := ht.instN henv Ctx.InstN.zero hr
  have hright := ht.instN henv Ctx.InstN.zero hm
  obtain ⟨u, hT⟩ := hr.isType henv hΓ
  have hT' := hT.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hT) ⟨hΓ₀, u, hT'⟩
  have H' := H.move W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hα ES,
    ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, eqRecApp_subst]
  exact PiInertInterpret.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ₀
    (by simpa only [eqRecApp_subst] using hr.subst henv.orderedStrong WS hΓ₀) ht' H'.base

/-- Per-substitution index histories construct per-substitution computations
for arbitrary typed Eq consumers. Each instance chooses its own finite stage;
no uniform bound over the interpreter's typed substitutions is needed. -/
theorem PiInertFiniteHistory.eq_rec_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t S)
    (H : PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertFiniteComputation D (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) (proofErase Γ (t.inst m)) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  have hab := H.actual_defeq heq hs hc hΓ ha hb
  have hm := (eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T hr).hasType.2
  have hleft := ht.instN henv Ctx.InstN.zero hr
  have hright := ht.instN henv Ctx.InstN.zero hm
  obtain ⟨u, hT⟩ := hr.isType henv hΓ
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨n, H'⟩ := H W
  have hT' := hT.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hT) ⟨hΓ₀, u, hT'⟩
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hα ES,
    ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, eqRecApp_subst]
  exact ⟨n+1, H'.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ₀
    (by simpa only [eqRecApp_subst] using hr.subst henv.orderedStrong WS hΓ₀) ht'⟩

/-- A type-valued probe is the identity-consumer instance. Its proposition
indices can be supplied by finite paired interpretation rather than uniform
PiInertEvidence at a globally chosen stage. -/
theorem PiInertFiniteHistory.type_probe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ (.sort .zero))
      (proofErase Γ P) (proofErase Γ Q)) :
    PiInertFiniteComputation D (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) (proofErase Γ S) := by
  have hr := eqTypeProbe_typed heq hΓ hS hP hQ hq
  have ht : env.HasType univs (.sort u :: Γ) (.bvar 0) (VExpr.sort u).lift := .bvar .zero
  intro Λ σ W
  simpa only [eqTypeProbe, VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, VExpr.liftN_zero] using
    H.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ hr ht W

/-- Two per-instance computations to the same unit type construct full
carrier transport. Each target history uses its own chosen finite stage;
the input history and endpoint shapes are unrestricted. -/
theorem PiInertCarrierTransport.finite_unit_aliases
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (RT : PiInertFiniteComputation D Δ T (.const family ls))
    (RU : PiInertFiniteComputation D Δ U (.const family ls)) :
    PiInertCarrierTransport D Δ T U := by
  intro Λ σ W a b
  obtain ⟨n, RT⟩ := RT W
  obtain ⟨m, RU⟩ := RU W
  have HT : PiInertWorldHistory D n Λ (T.subst σ) a b :=
    (pi_inert_unit_carrier_history hi hp hx hf hD).world_history.carrier_prefix RT
  have HU : PiInertWorldHistory D m Λ (U.subst σ) a b :=
    (pi_inert_unit_carrier_history hi hp hx hf hD).world_history.carrier_prefix RU
  exact ⟨fun _ => ⟨m, HU⟩, fun _ => ⟨n, HT⟩⟩

/-- A finite computation suffices for recursive call supply. Its result
supply stays under the written binder and has the same per-instance discipline. -/
theorem PiInertTreeSupply.finite_call
    (R : PiInertFiniteComputation D Δ T (.forallE A B))
    (S : PiInertTreeSupply D (A::Δ) q B) : PiInertTreeSupply D Δ (.call A B p q) T := by
  intro Λ σ W
  obtain ⟨n, R⟩ := R W
  refine ⟨⟨n, R⟩, ?_⟩
  intro Ξ τ x V HX
  exact S (ContextSubstitution.cons_assigned (W.comp V.typed) HX)

/-- Recursive call conversion also accepts finite target-alias computation
without a stage uniform over all typed substitutions. -/
theorem PiInertTreeTransport.finite_target_call_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertTreeTransport D Δ p T (.call A B r s) U)
    (R : PiInertFiniteComputation D Δ V U) :
    PiInertTreeTransport D Δ p T (.call A B r s) V := by
  intro Λ σ W a b X HA HB
  obtain ⟨n, path⟩ := R W
  have result := H W X (HA.world_computation heq hs path) (HB.world_computation heq hs path)
  exact result.call_prefix HA HB path

/-- The hidden-unit carrier transport consumes the finite histories actually
returned by paired interpretation. No uniform index stage or exposure of the
probe is an additional premise. -/
theorem PiInertFiniteHistory.unit_probe_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ (.sort .zero))
      (proofErase Γ P) (proofErase Γ Q)) :
    PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ (.const family ls))
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) := by
  have RS := PiInertEvidence.core (stage := 0) hs hc hΓ hS
    (.refl (e := proofErase Γ (.const family ls)))
  have RT : PiInertFiniteComputation D (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) (proofErase Γ (.const family ls)) :=
    H.type_probe heq hs hl hcon hc hreg hoff hRec hΓ hS hP hQ hq
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  rw [ES] at RS RT ⊢
  intro Λ σ W a b
  exact PiInertCarrierTransport.finite_unit_aliases hi hp hx hf hD RS.finite_computation RT W a b

/-- An interpreted proposition-index child constructs the converted unit
interpreter outright. The source index profiles may be arbitrary; their ground
histories suffice. Empty variable requirements supply every diagonal instance,
and stages may vary with substitution. This does not construct the index
interpreter from an arbitrary original derivation or discard image requirements. -/
theorem PiInertGuardedPairInterpretation.unit_probe_from_indices
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (ha : env.HasType univs Γ a (.const family ls)) (hb : env.HasType univs Γ b (.const family ls))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ P) (proofErase Γ Q) (proofErase Γ (.sort .zero)) (proofErase Γ (.sort .zero)) r s) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b)
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q))
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) (.plain .ground) (.plain .ground) := by
  have index : PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ (.sort .zero))
      (proofErase Γ P) (proofErase Γ Q) := H.empty_finite_history
  have CT : PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ (.const family ls))
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) :=
    index.unit_probe_transport heq hs hl hcon hc hreg hoff hRec hi hp hx hf hD hΓ hS hP hQ hq
  have HE := eqTypeProbe_defeq heq hΓ hS hP hQ hq (index.actual_defeq heq hs hc hΓ hP hQ).toU
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  rw [ES] at CT
  have original := PiInertGuardedPairInterpretation.unit_ground hi hp hx hf hD
    (ES ▸ TypedAt.of_typed hΓ ha) (ES ▸ TypedAt.of_typed hΓ hb)
  exact original.convert_ground heq hs CT CT
    (.of_typed hΓ (HE.symm.defeq ha)) (.of_typed hΓ (HE.symm.defeq hb))

end Lean4Lean.VEnv.Strengthening
