import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandValues

/-! # Finite demands for application bodies under paired substitutions

Application trees retain actual raw source witnesses and selected native
carriers. Their finite variable requirements support repeated uses at different
demands. Interpretation consumes image evidence after two actual typed
substitutions; it does not add arbitrary substitution futures to histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private value_inst_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues
variable [Params] {D : Definitions}

/-- A finite collection of demands retains each member and a ground payload
when the collection is empty. It adds no uniform checker-stage requirement. -/
def PiInertDemand.all : List PiInertDemand → PiInertDemand
  | [] => .ground
  | p :: ps => .both p (PiInertDemand.all ps)

/-- Every member of a demand collection remains available at the same terms
and selected carrier, including when one variable is used several times. -/
theorem PiInertDemandValue.of_all (H : PiInertDemandValue (.all ps) D Δ a b T)
    (hp : p ∈ ps) : PiInertDemandValue p D Δ a b T := by
  induction ps with
  | nil => cases hp
  | cons r rs ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · exact H.1
    · exact ih H.2 hp

/-- Finite variable-use requirements for a body. The two substituted images
are compared at the left substituted native carrier. -/
def PiInertDemandImages (D : Definitions) (Δ Λ : List ProofShape)
    (σ τ : ProofShape.Subst) (uses : List (Nat × PiInertDemand)) : Prop :=
  ∀ i p, (i, p) ∈ uses → PiInertDemandValue p D Λ (σ i) (τ i) ((contextOracle Δ i).subst σ)

/-- A variable/application body with explicit actual source witnesses.
Each application chooses the argument demand that its function must consume.
Only ordinary-core selected-type conversion is included; general conversion,
constants, projections and nested lambda bodies are not covered by this tree. -/
inductive PiInertDemandTree (D : Definitions) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | bvar (i : Nat) : TypedSource Δ (.bvar i) → TypedSource Δ (contextOracle Δ i) →
      PiInertDemandTree D Δ (.bvar i) (contextOracle Δ i)
  | app (argument : PiInertDemand) :
      PiInertDemandTree D Δ f (.forallE A B) → PiInertDemandTree D Δ x A →
      TypedSource Δ (.app f x) → TypedSource Δ (B.inst x) →
      PiInertDemandTree D Δ (.app f x) (B.inst x)
  | coreType : PiInertDemandTree D Δ e T → TypedSource Δ U →
      ComputeJoin (ErasedLevelCore D) T U → PiInertDemandTree D Δ e U

/-- Every tree retains actual typing of its endpoint and selected carrier. -/
theorem PiInertDemandTree.sources (H : PiInertDemandTree D Δ e T) :
    TypedSource Δ e ∧ TypedSource Δ T := by
  induction H with
  | bvar _ HE HT => exact ⟨HE, HT⟩
  | app _ _ _ HE HT => exact ⟨HE, HT⟩
  | coreType _ HT _ ih => exact ⟨ih.1, HT⟩

/-- A finite application tree infers finite variable demands for any requested
result demand. The paired substitution theorem is proved by tree induction;
no substituted strong derivation is recursively invoked. Every requested
variable retains its original source witnesses for later binder instantiation. -/
theorem PiInertDemandTree.requirements
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertDemandTree D Δ e T) (q : PiInertDemand) :
    ∃ uses : List (Nat × PiInertDemand),
      (∀ i p, (i, p) ∈ uses → TypedSource Δ (.bvar i) ∧ TypedSource Δ (contextOracle Δ i)) ∧
      ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
        PiInertDemandImages D Δ Λ σ τ uses →
        PiInertDemandValue q D Λ (e.subst σ) (e.subst τ) (T.subst σ) := by
  induction H generalizing q with
  | bvar i HE HT =>
    refine ⟨[(i, q)], ?_, ?_⟩
    · intro j p hp
      have E := List.mem_singleton.1 hp
      cases E
      exact ⟨HE, HT⟩
    · intro Λ σ τ _ _ images
      exact images i q (by simp)
  | app p F X HE HT ihF ihX =>
    obtain ⟨fs, VF, HF⟩ := ihF (.arrow p q)
    obtain ⟨xs, VX, HX⟩ := ihX p
    refine ⟨fs ++ xs, ?_, ?_⟩
    · intro i r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact VF i r hr
      · exact VX i r hr
    · intro Λ σ τ WL WR images
      have NF := HF WL WR (fun i r hr => images i r (List.mem_append_left xs hr))
      have NX := HX WL WR (fun i r hr => images i r (List.mem_append_right fs hr))
      have HL := HE.subst WL
      have HR := HE.subst WR
      have HU := HT.subst WL
      simp only [ProofShape.subst, ProofShape.subst_inst] at NF HL HR HU ⊢
      exact NF.app heq hc NX HL HR HU
  | coreType F HT J ih =>
    obtain ⟨uses, valid, run⟩ := ih q
    refine ⟨uses, valid, ?_⟩
    intro Λ σ τ WL WR images
    exact (run WL WR images).core_join hs hc (HT.subst WL)
      (J.subst (fun R => erased_level_core_subst R))

/-- Typing of an applied raw lambda supplies a genuine interpretation of its
written binder by the argument. Actual application inversion, not carrier
history or unrelated endpoint typing, justifies the binder substitution. -/
theorem ProofShape.TypedSource.lambda_argument
    (H : TypedSource Δ (.app (.lam A b) x)) :
    ContextSubstitution (A::Δ) Δ (ProofShape.Subst.one x) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, he, Ee⟩ := H
  obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
  obtain ⟨C, body, rfl, _, EC, _⟩ := erase_lam_inv Ef
  have ha := he.app_lam_arg hΓ
  obtain ⟨_, _, hf, _⟩ := he.app_inv henv hΓ
  obtain ⟨⟨u, hC⟩, _, _⟩ := hf.lam_inv henv hΓ
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have W : ContextSubstitution (proofEraseCtx (C::Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ a)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓC ha)
      (erasedSubstAgreement_one hΓC ha)
  simp only [proofEraseCtx, EC, EΓ, Ea] at W
  intro Γ' hΓ' E
  exact W hΓ' E

omit [Params] in
/-- Substitution under a binder followed by its typed argument is the ordinary
cons substitution on raw terms. This is a syntax identity only. -/
theorem ProofShape.Subst.lift_comp_one (σ : ProofShape.Subst) (x : ProofShape) :
    σ.lift.comp (ProofShape.Subst.one x) = σ.cons x := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change ((σ i).liftN 1).subst (ProofShape.Subst.one x) = σ i
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using value_inst_lift (σ i) x

/-- Whole lambda-application typing extends a given source interpretation by
its argument. The source body's own actual witnesses can now be transported. -/
theorem ProofShape.ContextSubstitution.lambda_argument {b : ProofShape}
    (W : ContextSubstitution Δ Λ σ)
    (H : TypedSource Λ (.app (.lam (A.subst σ) (b.subst σ.lift)) x)) :
    ContextSubstitution (A::Δ) Λ (σ.cons x) := by
  have V : ContextSubstitution (A::Δ) Λ (σ.lift.comp (ProofShape.Subst.one x)) :=
    ContextSubstitution.comp W.cons H.lambda_argument
  rw [ProofShape.Subst.lift_comp_one] at V
  intro Γ' hΓ' E
  exact V hΓ' E

/-- Collect precisely the demands made of the newly bound variable. Other
variables remain in the surrounding core world. Duplicate uses are retained. -/
def PiInertDemand.headUses : List (Nat × PiInertDemand) → List PiInertDemand
  | [] => []
  | (0, p) :: uses => p :: PiInertDemand.headUses uses
  | (_+1, _) :: uses => PiInertDemand.headUses uses

omit [Params] in
/-- Every demand on index zero appears in the collected binder requirements. -/
theorem PiInertDemand.mem_headUses (H : (0, p) ∈ uses) : p ∈ PiInertDemand.headUses uses := by
  induction uses with
  | nil => cases H
  | cons ip uses ih =>
    obtain ⟨i, r⟩ := ip
    rcases List.mem_cons.1 H with E | tail
    · cases E; exact List.mem_cons_self
    · cases i with
      | zero => exact List.mem_cons_of_mem _ (ih tail)
      | succ => exact ih tail

/-- A paired binder image supplies all its collected demands. The old images
remain variables in a certified core world, so their native neutral evidence
supplies each requested demand after the retained native-type conversion. -/
theorem PiInertDemandImages.cons_world
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (valid : ∀ i p, (i, p) ∈ uses →
      TypedSource (A::Δ) (.bvar i) ∧ TypedSource (A::Δ) (contextOracle (A::Δ) i))
    (W : PiInertCoreWorld D Δ Λ σ)
    (WL : ContextSubstitution (A::Δ) Λ (σ.cons x))
    (HX : PiInertDemandValue (.all (PiInertDemand.headUses uses)) D Λ x y (A.subst σ)) :
    PiInertDemandImages D (A::Δ) Λ (σ.cons x) (σ.cons y) uses := by
  intro i p hi
  cases i with
  | zero =>
    simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons, ProofShape.lift_subst_cons] using
      HX.of_all (PiInertDemand.mem_headUses hi)
  | succ i =>
    obtain ⟨HE, HT⟩ := valid (i+1) p hi
    have HE' := HE.subst WL
    have HT' := HT.subst WL
    simp only [ProofShape.subst, contextOracle, TypeOracle.cons,
      ProofShape.Subst.cons, ProofShape.lift_subst_cons] at HE' HT' ⊢
    obtain ⟨j, Ej, _, HR⟩ := W.lookup i
    have HJ : TypedSource Λ (.bvar j) := Ej ▸ HE'
    have HN : PiInertWorldValue D 0 Λ (.bvar j) (.bvar j) (contextOracle Λ j) :=
      pi_inert_native_variable_world_neutral.value HJ HJ
    have HV := HN.convert HR.world_computation
    have HC : PiInertCarrierValue D 0 Λ (σ i) (σ i) ((contextOracle Δ i).subst σ) := by
      rw [Ej]
      exact .neutral HV
    exact HC.demand heq hs hc hRigid HT'

/-- For every requested result demand, a finite native application body has a
finite sufficient binder demand. Arbitrary repeated uses are collected, and
actual lambda-application typing provides each paired body substitution.
This covers the displayed tree grammar only, not arbitrary strong lambdas. -/
theorem PiInertDemandTree.lambda_value
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertDemandTree D (A::Δ) b B)
    (HD : TypedSource Δ A) (HF : TypedSource Δ (.lam A b))
    (HT : TypedSource Δ (.forallE A B)) (q : PiInertDemand) :
    ∃ p, PiInertDemandValue (.arrow p q) D Δ (.lam A b) (.lam A b) (.forallE A B) := by
  obtain ⟨uses, valid, run⟩ := H.requirements heq hs hc q
  refine ⟨.all (PiInertDemand.headUses uses), PiInertDemandBase.refl hc HF HT, ?_⟩
  intro Λ σ C E x y W HP J HX HL HR HResult
  simp only [ProofShape.subst] at J HL HR
  obtain ⟨JD, JB⟩ := J.level_core_pi_parts
  have HArg := HX.core_join hs hc (HD.subst W.typed) JD.symm
  have WL : ContextSubstitution (A::Δ) Λ (σ.cons x) :=
    ContextSubstitution.lambda_argument W.typed HL
  have WR : ContextSubstitution (A::Δ) Λ (σ.cons y) :=
    ContextSubstitution.lambda_argument W.typed HR
  have images := PiInertDemandImages.cons_world heq hs hc hRigid valid W WL HArg
  have HBody := run WL WR images
  have JE : ComputeJoin (ErasedLevelCore D) (B.subst (σ.cons x)) (E.inst x) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst_subst, ProofShape.Subst.lift_comp_one] using
      JB.subst (fun R => erased_level_core_subst R) (σ := ProofShape.Subst.one x)
  have beta (x : ProofShape) : Compute (ErasedLevelCore D)
      (.app (.lam (A.subst σ) (b.subst σ.lift)) x) (b.subst (σ.cons x)) := by
    have E : (b.subst σ.lift).inst x = b.subst (σ.cons x) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
        ProofShape.subst_subst, ProofShape.Subst.lift_comp_one]
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := A.subst σ))
  exact (HBody.core_join hs hc HResult JE).prefixes hs hc HL HR (beta x) (beta y)

/-- An actual non-proof variable at its literal lookup type constructs a
native application-tree leaf. No assigned/native type equality is erased or
assumed computational in this constructor. -/
theorem PiInertDemandTree.actual_bvar
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i T) (hn : ¬ IsProof Γ (.bvar i)) :
    PiInertDemandTree D (proofEraseCtx Γ) (proofErase Γ (.bvar i)) (proofErase Γ T) := by
  have hv : env.HasType univs Γ (.bvar i) T := .bvar hl
  obtain ⟨u, hT⟩ := hv.isType henv hΓ
  have EO : contextOracle (proofEraseCtx Γ) i = proofErase Γ T := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl]
  have EV : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  rw [EV, ← EO]
  exact .bvar i ⟨Γ, _, _, hΓ, rfl, hv, EV⟩ ⟨Γ, _, _, hΓ, rfl, hT, EO.symm⟩

/-- The actual non-proof application case preserves the tree when its two
original children have tree evidence. Whole source and result typing and the
exact erased dependent codomain are reconstructed from the actual premises. -/
theorem PiInertDemandTree.actual_app
    (p : PiInertDemand) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (F : PiInertDemandTree D (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A B)))
    (X : PiInertDemandTree D (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    PiInertDemandTree D (proofEraseCtx Γ) (proofErase Γ (.app f x)) (proofErase Γ (B.inst x)) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨_, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  have EE : proofErase Γ (.app f x) = .app (proofErase Γ f) (proofErase Γ x) := if_neg hn
  have ET := proofErase_instN hΓA hx Ctx.InstN.zero hB
  rw [EP] at F
  rw [EE, ET]
  exact .app p F X ⟨Γ, _, _, hΓ, rfl, hf.app hx, EE⟩
    ⟨Γ, _, _, hΓ, rfl, hB.instN henv Ctx.InstN.zero hx, ET⟩

/-- Actual lambdas with an application-tree body have a finite sufficient
input demand for every requested result demand. The body certificate is the
remaining fragment hypothesis; this does not claim that arbitrary strong
body equality, general conversion or nested lambdas have such a tree. -/
theorem PiInertDemandTree.actual_lambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A::Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (H : PiInertDemandTree D (proofEraseCtx (A::Γ))
      (proofErase (A::Γ) b) (proofErase (A::Γ) B)) (q : PiInertDemand) :
    ∃ p, PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam A b)) (proofErase Γ (.forallE A B)) := by
  have hf := HasType.lam hA hb
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EF : proofErase Γ (.lam A b) =
      .lam (proofErase Γ A) (proofErase (A::Γ) b) := if_neg hn
  have ET : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  rw [EF, ET]
  exact H.lambda_value heq hs hc hRigid ⟨Γ, _, _, hΓ, rfl, hA, rfl⟩
    ⟨Γ, _, _, hΓ, rfl, hf, EF⟩ ⟨Γ, _, _, hΓ, rfl, hPi, ET⟩ q

/-- A typed repeated higher-order use of the bound function: fun f => f (f x),
with x itself a function Prop -> Prop. The two calls may choose different
argument demands; their inferred binder requirements are retained together.
The result remains a function, so subsequent function demands are meaningful. -/
theorem pi_inert_repeated_function_body_demand
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (first second result : PiInertDemand) :
    let A := VExpr.forallE (.sort .zero) (.sort .zero)
    let F := VExpr.forallE A A
    let f := VExpr.lam F (.app (.bvar 0) (.app (.bvar 0) (.bvar 1)))
    ∃ p, PiInertDemandValue (.arrow p result) D (proofEraseCtx [A])
      (proofErase [A] f) (proofErase [A] f) (proofErase [A] (.forallE F A)) := by
  dsimp only
  let A := VExpr.forallE (.sort .zero) (.sort .zero)
  let F := VExpr.forallE A A
  have hA {Γ} : env.HasType univs Γ A (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hF {Γ} : env.HasType univs Γ F (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (by trivial) (by trivial) VLevel.imax_self).defeq (HasType.forallE hA hA)
  have hΓ : OnCtx [A] (env.IsType univs) := ⟨trivial, _, hA⟩
  have hΓF : OnCtx [F, A] (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hv : env.HasType univs [F, A] (.bvar 0) F := .bvar .zero
  have hx : env.HasType univs [F, A] (.bvar 1) A := .bvar (.succ .zero)
  have hInner : env.HasType univs [F, A] (.app (.bvar 0) (.bvar 1)) A := hv.app hx
  have hBody : env.HasType univs [F, A] (.app (.bvar 0) (.app (.bvar 0) (.bvar 1))) A :=
    hv.app hInner
  have VF : PiInertDemandTree D (proofEraseCtx [F, A])
      (proofErase [F, A] (.bvar 0)) (proofErase [F, A] F) :=
    .actual_bvar hΓF Lookup.zero (not_proof_at_positive_type hΓF hF hv)
  have VX : PiInertDemandTree D (proofEraseCtx [F, A])
      (proofErase [F, A] (.bvar 1)) (proofErase [F, A] A) :=
    .actual_bvar hΓF (Lookup.succ Lookup.zero) (not_proof_at_positive_type hΓF hA hx)
  have VI := PiInertDemandTree.actual_app first hΓF hv hx
    (not_proof_at_positive_type hΓF hA hInner) VF VX
  have VB := PiInertDemandTree.actual_app second hΓF hv hInner
    (not_proof_at_positive_type hΓF hA hBody) VF VI
  have hPi : env.HasType univs [A] (.forallE F A) (.sort (.succ .zero)) :=
    (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (by trivial) (by trivial) VLevel.imax_self).defeq (HasType.forallE hF hA)
  exact VB.actual_lambda heq hs hc hRigid hΓ hF hBody
    (not_proof_at_positive_type hΓ hPi (.lam hF hBody)) result

end Lean4Lean.VEnv.Strengthening
