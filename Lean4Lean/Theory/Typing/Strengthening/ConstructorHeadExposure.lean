import Lean4Lean.Theory.Typing.Strengthening.ConstructorStructureEta
import Lean4Lean.Theory.Typing.Strengthening.QuotHeadComputation

/-! # Head exposure through ordinary recursor computation and both eta forms

The finite model includes iota rules with non-projection constructor majors.
Recovered paths use PatternCompute and replay below from source typing alone.
Structure-major iota and index-sensitive singleton prefix unfolding remain open.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions ProjectionCompute PatternCompute CheckFromTyping)
variable [Params]

/-- Constructor constants cannot also unfold as declarations. -/
def ConstructorRigid (D : Definitions) : Prop :=
  ∀ s info, env.projections s info → ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs

/-- The environment's actual declaration equations satisfy constructor rigidity. -/
theorem ConstructorRigid.ofEnv : ConstructorRigid (Definitions.ofEnv env univs henv) :=
  fun _ _ hi _ _ => Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hi)

/-- Compatible beta/delta/projection computation and both eta expansions. The eta
rules deliberately require no typings: backwards head exposure is syntactic.
Iota carries the uniform check certificate already supplied by every concrete rule. -/
inductive EtaCompute (D : Definitions) : VExpr → VExpr → Prop where
  | compute : ProjectionCompute D e out → EtaCompute D e out
  | iota {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
        (SimplePattern.iota recursor major ctor fields).toPattern.Check}
      {captures : (SimplePattern.iota recursor major ctor fields).toPattern.Path → VExpr} :
      Pat _ r → CheckFromTyping env univs _ r levels →
      (SimplePattern.iota recursor major ctor fields).toPattern.Matches e levels captures →
      NotProjectionCtor ctor → EtaCompute D e (r.1.apply levels captures)
  | trans : EtaCompute D a b → EtaCompute D b c → EtaCompute D a c
  | funEta : EtaCompute D e (.lam A (.app e.lift (.bvar 0)))
  | structEta : env.projections s info → ps.length = info.nparams →
      EtaCompute D e (structExpand s info ls ps e)
  | app : EtaCompute D f f' → EtaCompute D a a' → EtaCompute D (.app f a) (.app f' a')
  | lam : EtaCompute D A A' → EtaCompute D b b' → EtaCompute D (.lam A b) (.lam A' b')
  | forallE : EtaCompute D A A' → EtaCompute D B B' → EtaCompute D (.forallE A B) (.forallE A' B')
  | proj : EtaCompute D m m' → EtaCompute D (.proj s i m) (.proj s i m')

/-- Every actual parallel eta step in the full confluence presentation embeds in
this relation, including simultaneous changes of domains and structure parameters. -/
theorem EtaCompute.of_etaPar (R : EtaPar Γ e out) : EtaCompute D e out := by
  induction R with
  | bvar | sort | const => exact .compute (.base .refl)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | funEta _ _ _ ih _ => exact ih.trans .funEta
  | structEta _ hl _ hi hp _ _ _ ih _ => exact ih.trans (.structEta hi (by omega))

/-- The earlier beta/delta/function-eta fragment embeds without restriction. -/
theorem EtaCompute.of_computeEta (R : PureObservation.ComputeEta D e out) : EtaCompute D e out := by
  induction R with
  | compute h => exact .compute (.base h)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | eta => exact .funEta
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Compatible computation of captures computes any instantiated pattern RHS. -/
theorem EtaCompute.apply_pat {p : Pattern} (r : p.RHS)
    {levels : List VLevel} {captures captures' : p.Path → VExpr}
    (H : ∀ p, EtaCompute D (captures p) (captures' p)) :
    EtaCompute D (r.apply levels captures) (r.apply levels captures') := by
  induction r with
  | fixed => exact .compute (.base .refl)
  | var => exact H _
  | app _ _ ihf iha => exact .app ihf iha

omit [Params] in
/-- An actual checked non-structure iota rule embeds, including arbitrary mixed
computation/eta paths in its captures. Concrete checks supply the uniform certificate. -/
theorem EtaCompute.of_iota {env : VEnv} (henv : env.WF)
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    {captures captures' : (SimplePattern.iota recursor major ctor fields).toPattern.Path → VExpr}
    (hp : ConcretePattern env _ r)
    (hm : (SimplePattern.iota recursor major ctor fields).toPattern.Matches e levels captures)
    (hc : r.2.OK (env.IsDefEqU U Γ) levels captures)
    (hn : @NotProjectionCtor (henv.params U) ctor)
    (H : ∀ p, @EtaCompute (henv.params U) D (captures p) (captures' p)) :
    @EtaCompute (henv.params U) D e (r.1.apply levels captures') := by
  letI := henv.params U
  exact (EtaCompute.iota hp (PureObservation.ConcretePattern.checkFromTyping henv hp hc) hm hn).trans
    (EtaCompute.apply_pat _ H)

/-- No step of a mixed computational/eta path adds a finite observation. -/
theorem EtaCompute.obs_back (hD : ConstructorRigid D) (R : EtaCompute D e out)
    (H : Obs D S out o) : Obs D S e o := by
  induction R generalizing S o with
  | compute h => exact projection_obs_back h H
  | iota hp hc hm hn => exact H.iota_back hp hc hm hn
  | trans _ _ ih1 ih2 => exact ih1 (ih2 H)
  | funEta => exact H.eta_back
  | structEta hi hp => exact H.struct_eta_back hi (hD _ _ hi) hp
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hl⟩ := H.lam_inv
    exact .sub (.lam (ihb hb)) hl
  | forallE => exact .sub .pi H.pi_inv
  | proj _ ih => exact .proj (ih H.proj_inv)

/-- Eta can be removed from a finite Pi-exposing path. The recovered Pi may have
different annotations, and no normalization of the whole source is asserted. -/
theorem EtaCompute.pi_exposure (hD : ConstructorRigid D) (R : EtaCompute D e (.forallE A B)) :
    ∃ A' B', PatternCompute D e (.forallE A' B') :=
  (R.obs_back hD (S := fun _ _ => False) .pi).pi_exposure

/-- The corresponding sort-head exposure theorem. -/
theorem EtaCompute.sort_exposure (hD : ConstructorRigid D) (R : EtaCompute D e (.sort u)) :
    ∃ v, PatternCompute D e (.sort v) :=
  (R.obs_back hD (S := fun _ _ => False) .sort).sort_exposure

/-- Mixed head exposure of a lifted type yields a genuine computational Pi
exposure below, even if eta annotations in the original path do not lower. -/
theorem EtaCompute.pi_exposure_below (hD : ConstructorRigid D)
    (R : EtaCompute D (e.lift' ρ) (.forallE A B)) :
    ∃ A' B', PatternCompute D e (.forallE A' B') := by
  obtain ⟨A', B', RC⟩ := R.pi_exposure hD
  obtain ⟨out, R0, he⟩ := RC.lift_inv
  obtain ⟨A0, B0, rfl, _, _⟩ := lift'_eq_forallE he.symm
  exact ⟨A0, B0, R0⟩

/-- Reconstruct a function's Pi type below from a lifted type trace, with both
function and structure eta allowed in that trace. Replay uses source typing below. -/
theorem EtaCompute.function_type_below (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : EtaCompute D (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') := by
  obtain ⟨A', B', RC⟩ := R.pi_exposure_below hD
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have HT := RC.simAt hs hΓ (.sort u) hT
  exact ⟨A', B', HT.defeq hf, _, HT⟩

/-- The recovered type licenses a genuine function-eta step below. -/
theorem EtaCompute.function_eta_below (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : EtaCompute D (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧
      FullReduction Γ f (.lam A' (.app f.lift (.bvar 0))) := by
  obtain ⟨A', B', ht, _⟩ := R.function_type_below hD hs hΓ hf
  exact ⟨A', B', ht, .tail .rfl (.funEta ht)⟩

/-- For actual environment equations all semantic side conditions are discharged. -/
theorem EtaCompute.function_type_below_ofEnv
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : EtaCompute (Definitions.ofEnv env univs henv) (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  R.function_type_below ConstructorRigid.ofEnv (Definitions.ofEnv_sound henv) hΓ hf

/-- All checked quotient prefixes remain available through their one derived
closed constant equation in the enlarged model. -/
theorem EtaCompute.of_quotPrefix (hr : QuotRegistered env)
    (H : QuotPrefixUnfold env univs Γ levels args rhs) :
    EtaCompute (ClosedQuot.definitions env univs henv hr)
      (mkApps (.const ``Quot.lift levels) args) rhs :=
  .compute (.base (ClosedQuot.prefix_compute henv hr H))

/-- Reconstruct the Pi type below for mixed recursor, projection, quotient-prefix,
and eta paths, discharging both declaration assumptions for the concrete collection. -/
theorem EtaCompute.function_type_below_quot (hr : QuotRegistered env)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : HasType env univs Γ f T)
    (R : EtaCompute (ClosedQuot.definitions env univs henv hr) (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env univs Γ f (.forallE A' B') ∧ IsDefEqU env univs Γ T (.forallE A' B') :=
  R.function_type_below (ClosedQuot.definitions_rigid hr) (ClosedQuot.definitions_sound henv hr) hΓ hf

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
