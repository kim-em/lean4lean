import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBinders

/-! # Recursive finite-demand derivations with nested lambdas

A derivation records its supported demand and finite variable requirements.
Lambda abstraction infers its argument demand from the body's uses; it does
not claim arbitrary arrow demands. Domains have their own ground derivations,
so related substituted domains are proved rather than assumed at every lambda.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- A body interpreter at one supported demand, with actual source witnesses.
Only the listed image demands are assumed under paired typed substitutions. -/
structure PiInertDemandInterpretation (D : Definitions) (Δ : List ProofShape)
    (uses : List (Nat × PiInertDemand)) (e T : ProofShape) (p : PiInertDemand) : Prop where
  source : TypedSource Δ e
  typeSource : TypedSource Δ T
  run : ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
    PiInertDemandImages D Δ Λ σ τ uses →
    PiInertDemandValue p D Λ (e.subst σ) (e.subst τ) (T.subst σ)

/-- A recursive body interpreter closes lambda abstraction. Domain and body
requirements are combined, and fresh uses determine the supported input
demand. The body may itself interpret nested lambdas. -/
theorem PiInertDemandInterpretation.lam
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u)
    (HD : PiInertDemandInterpretation D Δ domainUses A (.sort u) .ground)
    (HB : PiInertDemandInterpretation D (A::Δ) bodyUses b B q)
    (HF : TypedSource Δ (.lam A b)) (HT : TypedSource Δ (.forallE A B)) :
    PiInertDemandInterpretation D Δ (domainUses ++ PiInertDemand.tailUses bodyUses)
      (.lam A b) (.forallE A B) (.arrow (.all (PiInertDemand.headUses bodyUses)) q) := by
  refine ⟨HF, HT, ?_⟩
  intro Λ σ τ WL WR images
  have domain := HD.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
  have old : PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses bodyUses) :=
    fun i p hi => images i p (List.mem_append_right _ hi)
  obtain ⟨m, HA⟩ := domain.base.history
  have VL : ContextSubstitution (A::Δ) (A.subst σ :: Λ) σ.lift := WL.cons
  have VR : ContextSubstitution (A::Δ) (A.subst σ :: Λ) τ.lift :=
    ContextSubstitution.paired_lift heq hs WL WR S HA
  have VEL : ContextSubstitution (A::Δ) (A.subst σ :: Λ) (σ.etaLift u) :=
    ContextSubstitution.eta_lift VL S
  have VER : ContextSubstitution (A::Δ) (A.subst σ :: Λ) (τ.etaLift u) :=
    ContextSubstitution.eta_lift VR S
  have body := HB.run VEL VER (old.binder heq hs hc hRigid (ContextSubstitution.sort WL S))
  rw [HB.source.subst_etaLift S VL, HB.source.subst_etaLift S VR,
    HB.typeSource.subst_etaLift S VL] at body
  obtain ⟨n, history⟩ := body.base.history
  have test := PiInertEvidence.raw_lambda_test (n := n) hs hc S HF
  have HL := test.substitute VL
  have HR := test.substitute VR
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at HL HR
  have ground := (history.prefixes HL.world_computation HR.world_computation).function
    heq hs hc (ContextSubstitution.sort WL S)
  refine ⟨⟨HF.subst WL, HF.subst WR, HT.subst WL, n, ground⟩, ?_⟩
  intro Ξ κ C E x y W HP J HX HLeft HRight HResult
  have PL : ContextSubstitution Δ Ξ (σ.comp κ) := ContextSubstitution.comp WL W.typed
  have PR : ContextSubstitution Δ Ξ (τ.comp κ) := ContextSubstitution.comp WR W.typed
  simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at J HLeft HRight
  obtain ⟨JD, JB⟩ := J.level_core_pi_parts
  have HArg := HX.core_join hs hc (HD.source.subst PL) JD.symm
  have BL : ContextSubstitution (A::Δ) Ξ ((σ.comp κ).cons x) :=
    ContextSubstitution.lambda_argument PL HLeft
  have BR : ContextSubstitution (A::Δ) Ξ ((τ.comp κ).cons y) :=
    ContextSubstitution.lambda_argument PR HRight
  have result := HB.run BL BR ((old.move W).cons_pair HArg)
  have JE : ComputeJoin (ErasedLevelCore D) (B.subst ((σ.comp κ).cons x)) (E.inst x) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst_subst, ProofShape.Subst.lift_comp_one] using
      JB.subst (fun R => erased_level_core_subst R) (σ := ProofShape.Subst.one x)
  have beta (υ : ProofShape.Subst) (z : ProofShape) : Compute (ErasedLevelCore D)
      (.app (.lam (A.subst υ) (b.subst υ.lift)) z) (b.subst (υ.cons z)) := by
    have E : (b.subst υ.lift).inst z = b.subst (υ.cons z) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
        ProofShape.subst_subst, ProofShape.Subst.lift_comp_one]
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := A.subst υ))
  simpa only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] using
    (result.core_join hs hc HResult JE).prefixes hs hc HLeft HRight
      (beta (σ.comp κ) x) (beta (τ.comp κ) y)

/-- A finite syntax-directed derivation of a supported demand. Lambda nodes
may occur recursively in function or argument position. Application requires
matching supported argument/result demands; it is not an unrestricted strong
typing rule. General definitional type conversion and recursive constant
function action remain outside these constructors. -/
inductive PiInertDemandDerivation (D : Definitions) :
    List ProofShape → List (Nat × PiInertDemand) → ProofShape → ProofShape → PiInertDemand → Prop where
  | bvar (i : Nat) (p : PiInertDemand) :
      TypedSource Δ (.bvar i) → TypedSource Δ (contextOracle Δ i) →
      PiInertDemandDerivation D Δ [(i, p)] (.bvar i) (contextOracle Δ i) p
  | closed : (∀ σ, e.subst σ = e) → TypedSource Δ e → TypedSource Δ T →
      PiInertDemandDerivation D Δ [] e T .ground
  | proof : TypedSource Δ .proof → TypedSource Δ T →
      PiInertDemandDerivation D Δ [] .proof T p
  | app : PiInertDemandDerivation D Δ fs f (.forallE A B) (.arrow p q) →
      PiInertDemandDerivation D Δ xs x A p →
      TypedSource Δ (.app f x) → TypedSource Δ (B.inst x) →
      PiInertDemandDerivation D Δ (fs ++ xs) (.app f x) (B.inst x) q
  | lam : DomainSort Δ A u →
      PiInertDemandDerivation D Δ ds A (.sort u) .ground →
      PiInertDemandDerivation D (A::Δ) bs b B q →
      TypedSource Δ (.lam A b) → TypedSource Δ (.forallE A B) →
      PiInertDemandDerivation D Δ (ds ++ PiInertDemand.tailUses bs)
        (.lam A b) (.forallE A B) (.arrow (.all (PiInertDemand.headUses bs)) q)
  | ground : PiInertDemandDerivation D Δ uses e T p →
      PiInertDemandDerivation D Δ uses e T .ground
  | both : PiInertDemandDerivation D Δ ps e T p → PiInertDemandDerivation D Δ qs e T q →
      PiInertDemandDerivation D Δ (ps ++ qs) e T (.both p q)
  | coreType : PiInertDemandDerivation D Δ uses e T p → TypedSource Δ U →
      ComputeJoin (ErasedLevelCore D) T U → PiInertDemandDerivation D Δ uses e U p

/-- Every supported recursive derivation has its actual endpoint and carrier
sources. These witnesses do not assert completeness of the demand grammar. -/
theorem PiInertDemandDerivation.sources (H : PiInertDemandDerivation D Δ uses e T p) :
    TypedSource Δ e ∧ TypedSource Δ T := by
  induction H with
  | bvar _ _ HE HT | closed _ HE HT | proof HE HT | app _ _ HE HT | lam _ _ _ HE HT => exact ⟨HE, HT⟩
  | ground _ ih => exact ih
  | both _ _ ih _ => exact ih
  | coreType _ HT _ ih => exact ⟨ih.1, HT⟩

/-- Structural induction interprets all nested demand derivations under two
actual typed substitutions. No substituted strong derivation is recursively
invoked, and no arbitrary-substitution future is added to value histories. -/
theorem PiInertDemandDerivation.interpret
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertDemandDerivation D Δ uses e T p) :
    PiInertDemandInterpretation D Δ uses e T p := by
  induction H with
  | bvar i p HE HT =>
    refine ⟨HE, HT, ?_⟩
    intro Λ σ τ WL WR images
    exact images i p (by simp)
  | closed stable HE HT =>
    refine ⟨HE, HT, ?_⟩
    intro Λ σ τ WL WR _
    rw [stable σ, stable τ]
    exact PiInertDemandBase.refl hc (stable σ ▸ HE.subst WL) (HT.subst WL)
  | proof HE HT =>
    refine ⟨HE, HT, ?_⟩
    intro Λ σ τ WL WR _
    exact pi_inert_proof_demand_value hc (HE.subst WL) (HT.subst WL)
  | app F X HE HT ihF ihX =>
    refine ⟨HE, HT, ?_⟩
    intro Λ σ τ WL WR images
    have NF := ihF.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
    have NX := ihX.run WL WR (fun i p hi => images i p (List.mem_append_right _ hi))
    have HL := HE.subst WL
    have HR := HE.subst WR
    have HU := HT.subst WL
    simp only [ProofShape.subst, ProofShape.subst_inst] at NF HL HR HU ⊢
    exact NF.app heq hc NX HL HR HU
  | lam S HD HB HF HT ihD ihB => exact PiInertDemandInterpretation.lam heq hs hc hRigid S ihD ihB HF HT
  | ground H ih => exact ⟨ih.source, ih.typeSource, fun WL WR images => (ih.run WL WR images).base⟩
  | both P Q ihP ihQ =>
    refine ⟨ihP.source, ihP.typeSource, ?_⟩
    intro Λ σ τ WL WR images
    exact ⟨ihP.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi)),
      ihQ.run WL WR (fun i p hi => images i p (List.mem_append_right _ hi))⟩
  | coreType H HU J ih =>
    refine ⟨ih.source, HU, ?_⟩
    intro Λ σ τ WL WR images
    exact (ih.run WL WR images).core_join hs hc (HU.subst WL)
      (J.subst (fun R => erased_level_core_subst R))

/-- Every earlier native application tree constructs a recursive derivation
at each requested result demand. The richer grammar therefore retains that
fragment while adding lambdas at explicitly supported profiles. -/
theorem PiInertDemandTree.derivation (H : PiInertDemandTree D Δ e T) (p : PiInertDemand) :
    ∃ uses, PiInertDemandDerivation D Δ uses e T p := by
  induction H generalizing p with
  | bvar i HE HT => exact ⟨[(i, p)], .bvar i p HE HT⟩
  | app q F X HE HT ihF ihX =>
    obtain ⟨fs, DF⟩ := ihF (.arrow q p)
    obtain ⟨xs, DX⟩ := ihX q
    exact ⟨fs ++ xs, .app DF DX HE HT⟩
  | coreType F HT J ih =>
    obtain ⟨uses, DF⟩ := ih p
    exact ⟨uses, .coreType DF HT J⟩

/-- A native actual variable supports any chosen finite demand, retaining its
literal lookup carrier and the corresponding one-variable requirement. -/
theorem PiInertDemandDerivation.actual_bvar (p : PiInertDemand)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i T) (hn : ¬ IsProof Γ (.bvar i)) :
    PiInertDemandDerivation D (proofEraseCtx Γ) [(i, p)]
      (proofErase Γ (.bvar i)) (proofErase Γ T) p := by
  have hv : env.HasType univs Γ (.bvar i) T := .bvar hl
  obtain ⟨u, hT⟩ := hv.isType henv hΓ
  have EO : contextOracle (proofEraseCtx Γ) i = proofErase Γ T := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl]
  have EV : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  rw [EV, ← EO]
  exact .bvar i p ⟨Γ, _, _, hΓ, rfl, hv, EV⟩ ⟨Γ, _, _, hΓ, rfl, hT, EO.symm⟩

/-- Actual non-proof application connects matching supported demands, with
the result at its exact erased dependent carrier. Either child can contain
nested lambdas; the argument must supply the demand its function consumes. -/
theorem PiInertDemandDerivation.actual_app
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (F : PiInertDemandDerivation D (proofEraseCtx Γ) fs
      (proofErase Γ f) (proofErase Γ (.forallE A B)) (.arrow p q))
    (X : PiInertDemandDerivation D (proofEraseCtx Γ) xs (proofErase Γ x) (proofErase Γ A) p) :
    PiInertDemandDerivation D (proofEraseCtx Γ) (fs ++ xs)
      (proofErase Γ (.app f x)) (proofErase Γ (B.inst x)) q := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨_, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  have EE : proofErase Γ (.app f x) = .app (proofErase Γ f) (proofErase Γ x) := if_neg hn
  have ET := proofErase_instN hΓA hx Ctx.InstN.zero hB
  rw [EP] at F
  rw [EE, ET]
  exact .app F X ⟨Γ, _, _, hΓ, rfl, hf.app hx, EE⟩
    ⟨Γ, _, _, hΓ, rfl, hB.instN henv Ctx.InstN.zero hx, ET⟩

/-- An actual non-proof lambda constructs a recursive abstraction node from
its annotated domain and body derivations, including a nested lambda body. -/
theorem PiInertDemandDerivation.actual_lam
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A::Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (HD : PiInertDemandDerivation D (proofEraseCtx Γ) ds (proofErase Γ A) (.sort u) .ground)
    (HB : PiInertDemandDerivation D (proofEraseCtx (A::Γ)) bs
      (proofErase (A::Γ) b) (proofErase (A::Γ) B) q) :
    PiInertDemandDerivation D (proofEraseCtx Γ) (ds ++ PiInertDemand.tailUses bs)
      (proofErase Γ (.lam A b)) (proofErase Γ (.forallE A B))
      (.arrow (.all (PiInertDemand.headUses bs)) q) := by
  have hf := HasType.lam hA hb
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EF : proofErase Γ (.lam A b) =
      .lam (proofErase Γ A) (proofErase (A::Γ) b) := if_neg hn
  have ET : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  rw [EF, ET]
  simp only [proofEraseCtx] at HB
  exact .lam (DomainSort.of_typed hΓ hA) HD HB
    ⟨Γ, _, _, hΓ, rfl, hf, EF⟩ ⟨Γ, _, _, hΓ, rfl, hPi, ET⟩

/-- A substitution-invariant actual type has a ground domain derivation.
The selected carrier is its actual sort, with no erased-sort ambiguity. -/
theorem PiInertDemandDerivation.actual_closed_type
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (stable : ∀ σ, (proofErase Γ A).subst σ = proofErase Γ A) :
    PiInertDemandDerivation D (proofEraseCtx Γ) [] (proofErase Γ A) (.sort u) .ground := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    HasType.sort (hA.sort_r henv hΓ)
  exact .closed stable ⟨Γ, _, _, hΓ, rfl, hA, rfl⟩
    ⟨Γ, _, _, hΓ, rfl, hU, if_neg (not_isProof_of_sort hΓ hU)⟩

/-- A derivation with no free image requirements yields its actual supported
demand by identity interpretation. No normalization or uniform stage bound
is used in discharging the empty requirement list. -/
theorem PiInertDemandDerivation.empty_value
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertDemandDerivation D Δ [] e T p) : PiInertDemandValue p D Δ e e T := by
  have W := PiInertCoreWorld.identity_source heq hc H.sources.1
  have HV := (H.interpret heq hs hc hRigid).run W.typed W.typed (fun _ _ h => nomatch h)
  simpa only [ProofShape.subst_id] using HV

/-- A concrete higher-order example uses a nested lambda in function position
and a lambda argument: (fun f => fun x => f x) (fun y => y). Here x and y
have type Prop -> Prop, so the returned function's result can itself support
further function demands. The inferred argument requirements are explicit. -/
theorem pi_inert_nested_evaluator_demand
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (q : PiInertDemand) :
    let A := VExpr.forallE (.sort .zero) (.sort .zero)
    let F := VExpr.forallE A A
    let e := VExpr.app (.lam F (.lam A (.app (.bvar 1) (.bvar 0)))) (.lam A (.bvar 0))
    PiInertDemandValue (.arrow (.all [.all [q]]) q) D []
      (proofErase [] e) (proofErase [] e) (proofErase [] F) := by
  dsimp only
  let A := VExpr.forallE (.sort .zero) (.sort .zero)
  let F := VExpr.forallE A A
  let p := PiInertDemand.all [q]
  have hA {Γ} : env.HasType univs Γ A (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hF {Γ} : env.HasType univs Γ F (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (by trivial) (by trivial) VLevel.imax_self).defeq (HasType.forallE hA hA)
  have hFF {Γ} : env.HasType univs Γ (.forallE F F) (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (by trivial) (by trivial) VLevel.imax_self).defeq (HasType.forallE hF hF)
  have ES {Γ} (hΓ : OnCtx Γ (env.IsType univs)) :
      proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  have EA {Γ} (hΓ : OnCtx Γ (env.IsType univs)) :
      proofErase Γ A = .forallE (.sort .zero) (.sort .zero) := by
    have E : proofErase Γ A =
        .forallE (proofErase Γ (.sort .zero)) (proofErase (.sort .zero :: Γ) (.sort .zero)) :=
      if_neg (not_isProof_of_sort hΓ hA)
    rw [E, ES hΓ, ES (show OnCtx (.sort .zero :: Γ) (env.IsType univs) from
      ⟨hΓ, _, HasType.sort (by trivial)⟩)]
  have EF {Γ} (hΓ : OnCtx Γ (env.IsType univs)) :
      proofErase Γ F = .forallE (.forallE (.sort .zero) (.sort .zero))
        (.forallE (.sort .zero) (.sort .zero)) := by
    have E : proofErase Γ F = .forallE (proofErase Γ A) (proofErase (A::Γ) A) :=
      if_neg (not_isProof_of_sort hΓ hF)
    rw [E, EA hΓ, EA (show OnCtx (A::Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩)]
  have DA {Γ} (hΓ : OnCtx Γ (env.IsType univs)) :
      PiInertDemandDerivation D (proofEraseCtx Γ) [] (proofErase Γ A) (.sort (.succ .zero)) .ground :=
    .actual_closed_type hΓ hA (by intro σ; rw [EA hΓ]; rfl)
  have DF {Γ} (hΓ : OnCtx Γ (env.IsType univs)) :
      PiInertDemandDerivation D (proofEraseCtx Γ) [] (proofErase Γ F) (.sort (.succ .zero)) .ground :=
    .actual_closed_type hΓ hF (by intro σ; rw [EF hΓ]; rfl)
  have hΓ : OnCtx ([] : List VExpr) (env.IsType univs) := trivial
  have hΓF : OnCtx [F] (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hΓAF : OnCtx [A, F] (env.IsType univs) := ⟨hΓF, _, hA⟩
  have hΓA : OnCtx [A] (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hf : env.HasType univs [A, F] (.bvar 1) F := .bvar (.succ .zero)
  have hx : env.HasType univs [A, F] (.bvar 0) A := .bvar .zero
  have hb : env.HasType univs [A, F] (.app (.bvar 1) (.bvar 0)) A := hf.app hx
  have hfD := PiInertDemandDerivation.actual_bvar (D := D) (.arrow p q) hΓAF
    (Lookup.succ Lookup.zero) (not_proof_at_positive_type hΓAF hF hf)
  have hxD := PiInertDemandDerivation.actual_bvar (D := D) p hΓAF Lookup.zero
    (not_proof_at_positive_type hΓAF hA hx)
  have hbD := PiInertDemandDerivation.actual_app hΓAF hf hx
    (not_proof_at_positive_type hΓAF hA hb) hfD hxD
  have hInner : env.HasType univs [F] (.lam A (.app (.bvar 1) (.bvar 0))) F := .lam hA hb
  have innerD := PiInertDemandDerivation.actual_lam hΓF hA hb
    (not_proof_at_positive_type hΓF hF hInner) (DA hΓF) hbD
  have hOuter : env.HasType univs [] (.lam F (.lam A (.app (.bvar 1) (.bvar 0)))) (.forallE F F) :=
    .lam hF hInner
  have outerD := PiInertDemandDerivation.actual_lam hΓ hF hInner
    (not_proof_at_positive_type hΓ hFF hOuter) (DF hΓ) innerD
  have hy : env.HasType univs [A] (.bvar 0) A := .bvar .zero
  have hyD := PiInertDemandDerivation.actual_bvar (D := D) q hΓA Lookup.zero
    (not_proof_at_positive_type hΓA hA hy)
  have hId : env.HasType univs [] (.lam A (.bvar 0)) F := .lam hA hy
  have idD := PiInertDemandDerivation.actual_lam hΓ hA hy
    (not_proof_at_positive_type hΓ hF hId) (DA hΓ) hyD
  have idBoth := PiInertDemandDerivation.both idD idD.ground
  have application := PiInertDemandDerivation.actual_app hΓ hOuter hId
    (not_proof_at_positive_type hΓ hF (hOuter.app hId)) outerD idBoth
  exact application.empty_value heq hs hc hRigid

end Lean4Lean.VEnv.Strengthening
