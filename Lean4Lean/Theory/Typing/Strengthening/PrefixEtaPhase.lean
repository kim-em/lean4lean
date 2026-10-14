import Lean4Lean.Theory.Typing.Strengthening.EtaPrefixExchange
import Lean4Lean.Theory.Typing.Strengthening.PrefixEtaHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.FamilyHeadRepair

/-! # Head repair with a terminal phase containing both eta forms

Computation, finite typed eta expansion, and ordinary normal comparison form a
head-repair interface that includes structure eta. No theorem here claims that
arbitrary interleavings in FullReduction admit this factorization.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- The eta-only phase embeds in the existing syntactic observation model.
Its declaration collection may be empty; no indexed-prefix replay is requested. -/
theorem TypedEtaExpansion.observation (R : TypedEtaExpansion Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ConstructorObservation.EtaCompute D e out := by
  induction R generalizing T with
  | refl => exact .compute (.base .refl)
  | structEta hi hp hx hm hc =>
    exact .structEta hi hx ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc) hp
  | funEta => exact .funEta
  | trans R1 _ ih1 ih2 => exact (ih1 hΓ ht).trans (ih2 hΓ (R1.simAt hΓ _ ht).hasType.2)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ih1 hΓ hf) (ih2 hΓ ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2)

/-- Every original parallel eta step embeds in the phase, including parallel
changes of its displayed domain, structure parameters and projected major. -/
theorem TypedEtaExpansion.of_etaPar (R : EtaPar Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    TypedEtaExpansion Γ e out := by
  induction R generalizing T with
  | bvar | sort | const => exact .refl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ih1 hΓ hf) (ih2 hΓ ha)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ih1 hΓ hA) (ih2 ⟨hΓ, _, hA⟩ hB)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2)
  | funEta _ _ hf ihf ihA =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    exact (TypedEtaExpansion.funEta hf).trans
      (.lam (ihA hΓ hA) (.app ((ihf hΓ ht).weakN .one) .refl))
  | structEta _ hlen _ hi hp hx hm hc ihm ihp =>
    have hparams := VExpr.WF.args_of_mkApps henv hΓ
      ((hm.isType henv hΓ).elim (fun _ h => ⟨_, h⟩))
    have HP : List.Forall₂ (TypedEtaExpansion _) _ _ := List.forall₂_of_getElem hlen (by
      intro i hi hi'
      obtain ⟨_, hP⟩ := hparams _ (List.getElem_mem hi)
      exact ihp i hi hi' hΓ hP)
    have HM := ihm hΓ ht
    refine (TypedEtaExpansion.structEta hi hp hx hm hc).trans
      (typedEtaExpansion_congrRel.mkApps .refl (HP.append' ?_))
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range] using
      (TypedEtaExpansion.proj (s := _) (i := i) HM)


/-- Actual computation followed by finite typed eta and one normal comparison.
FullReduction coverage remains an unproved postponement problem. -/
def PrefixEtaNormal (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ x y, PrefixCompute D Γ a x ∧ TypedEtaExpansion Γ x y ∧ NormalEq Γ y b

/-- The earlier function-eta factorization embeds with an empty eta phase. -/
theorem PrefixNormal.etaPhase (H : PrefixNormal D Γ a b) : PrefixEtaNormal D Γ a b := by
  obtain ⟨x, R, H⟩ := H
  exact ⟨x, x, R, .refl, H⟩

/-- Every finite typed expansion has the phase representation. -/
theorem TypedEtaExpansion.etaPhase (R : TypedEtaExpansion Γ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T) :
    PrefixEtaNormal D Γ a b :=
  ⟨a, b, .refl, R, .refl (R.simAt hΓ _ ht).hasType.2⟩

/-- The three phases give an original typed equality. -/
theorem PrefixEtaNormal.defeq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixEtaNormal D Γ a b) (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T := by
  obtain ⟨x, y, RC, RE, HN⟩ := H
  have hx := RC.simAt hs hΓ _ ht
  have hy := RE.simAt hΓ _ hx.hasType.2
  exact (hx.trans hy).trans ((HN.defeq hΓ).of_l henv hΓ hy.hasType.2)

/-- Both eta forms disappear from a Pi-exposing phase representation. -/
theorem PrefixEtaNormal.pi_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixEtaNormal D Γ e (.forallE A B)) :
    ∃ A' B', PrefixCompute D Γ e (.forallE A' B') := by
  obtain ⟨x, y, RC, RE, HN⟩ := H
  obtain ⟨A0, B0, rfl⟩ := normal_pi_right hΓ HN
  obtain ⟨A', B', rfl⟩ := RE.forallE_source
  exact ⟨A', B', RC⟩

/-- Registered family exposure also repairs through the eta phase. Beta-only
normal exposure is combined with the already checked eta observation theorem;
no arbitrary-prefix claim is made about that model. -/
theorem PrefixEtaNormal.family_exposure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (H : PrefixEtaNormal D Γ e (mkApps (.const family levels) args))
    (ht : env.HasType univs Γ e (.sort u)) :
    ∃ levels' args', PrefixCompute D Γ e (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨x, y, RC, RE, n, HN⟩ := H
  have hx := (RC.simAt hs hΓ _ ht).hasType.2
  have hy := (RE.simAt hΓ _ hx).hasType.2
  rcases normal_spine_expose_beta hΓ .const n HN (bs := []) .nil hy with
    hp | ⟨head, args', hh, RB, HA⟩ | ⟨A, body, m, xs, B, hm, RB, HB, ha, hf⟩ |
      ⟨z, A, B, m, xs, hm, RB, hz, HB, ha, hf⟩
  · exact (HasType.sort_not_proof hΓ hy hp).elim
  · cases hh with
    | const hlevels =>
      simp only [mkApps, List.foldl_nil] at RB
      have RX := (RE.observation (D := Definitions.empty) hΓ hx).trans (.compute (.base (.of_beta RB)))
      obtain ⟨args0, R0, hlen⟩ := RX.family_exposure (fun _ _ _ _ _ h => False.elim h) hi
      have R0' : PatternCompute D x (mkApps (.const family _) args0) := R0.mono (fun h => False.elim h)
      refine ⟨_, args0, RC.trans (.base R0'), hlevels, hlen.trans ?_⟩
      simpa only [List.append_nil] using HA.length_eq
  · have hbody := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hy).hasType.2
    exact (HasType.sort_not_lam hΓ hbody).elim
  · have hsort := (RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hy).hasType.2
    exact ((hsort.uniqU henv hΓ hz).sort_forallE_inv henv hΓ).elim

/-- Pi exposure in the three phases reconstructs a lower inferred function type.
Only exact computational replay uses the witnessed proposition front. -/
theorem PrefixEtaNormal.function_type_below (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hf : env.HasType univs Γ f T)
    (H : PrefixEtaNormal D Γ' (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧ env.IsDefEqU univs Γ T (.forallE A' B') := by
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  obtain ⟨A0, B0, RC⟩ := H.pi_exposure hΓ'
  obtain ⟨out, R0, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' hT
  obtain ⟨A', B', rfl, _, _⟩ := lift'_eq_forallE he.symm
  have HE := R0.simAt hs hΓ _ hT
  exact ⟨A', B', hf.defeqU_r henv hΓ ⟨_, HE⟩, _, HE⟩

/-- The corresponding family-typing repair retains the exposed head and arity.
The phase's eta annotations and parameters need not be scoped below. -/
theorem PrefixEtaNormal.family_type_below (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hi : env.projections family info) (hm : env.HasType univs Γ m T)
    (H : PrefixEtaNormal D Γ' (T.lift' ρ) (mkApps (.const family levels) args)) :
    ∃ levels' args', env.HasType univs Γ m (mkApps (.const family levels') args') ∧
      env.IsDefEqU univs Γ T (mkApps (.const family levels') args') ∧
      List.Forall₂ (· ≈ ·) levels' levels ∧ args'.length = args.length := by
  obtain ⟨u, hT⟩ := hm.isType henv hΓ
  obtain ⟨levels', args0, RC, hlevels, hlen⟩ := H.family_exposure hs hΓ' hi (hT.weak' henv W)
  obtain ⟨out, R0, he⟩ := RC.lift_inv heq hs hfront W hΓ hΓ' hT
  obtain ⟨args', rfl, rfl⟩ := lift'_eq_const_spine he.symm
  have HE := R0.simAt hs hΓ _ hT
  exact ⟨levels', args', hm.defeqU_r henv hΓ ⟨_, HE⟩, ⟨_, HE⟩, hlevels, by
    simpa only [List.length_map] using hlen⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
