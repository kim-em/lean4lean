import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedCastResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation

/-! # Certified cast removal in function position

An arbitrary application suffix does not unblock a proof-major Eq recursor.
Ordinary core computation still acts componentwise on its entire spine. This
allows a certified cast to be removed after computation even when its payload
will subsequently expose beta redexes at the supplied arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private spineCount match_varN_count
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

private theorem eqRec_match_arity
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hp : Pat p r) (hm : Matches p e levels captures)
    (hh : e.constHead = some ``Eq.rec) : spineCount e = 6 := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  have hn := hm.constHead.symm.trans hh
  cases sp with
  | defn c =>
    have hc : c = ``Eq.rec := Option.some.inj hn
    subst c
    rw [(pat_const_not_unfolding hp).1] at hreg
    cases hreg
  | iota c major ctor fields =>
    have hc : c = ``Eq.rec := by
      rw [Pattern.constHead_eq, SimplePattern.iota_headConst] at hn
      exact Option.some.inj hn
    subst c
    have hmj := ConstructorObservation.recursor_major_offset hreg hp
    rw [hoff] at hmj
    cases hm with
    | app hfn _ =>
      have H := match_varN_count hfn
      change spineCount _ + 1 = 6
      omega

omit [Params] in
private theorem spineCount_const (args : List ProofShape) :
    spineCount (ProofShape.mkApps (.const c levels) args) = args.length := by
  induction args using List.snoc_induction with
  | nil => rfl
  | snoc args a ih => simp only [ProofShape.mkApps_snoc, spineCount, ih,
      List.length_append, List.length_cons, List.length_nil, Nat.zero_add]

/-- Ordinary Eq rules have exactly six supplied arguments. In particular an
extra argument cannot introduce a new primitive root above a blocked major. -/
theorem erased_iota_eqRec_overapplied_no_root
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hlen : 6 < args.length) :
    ¬ ErasedIotaPrimitive D (ProofShape.mkApps (.const ``Eq.rec levels) args) out := by
  intro H
  have HC := spineCount_const (c := ``Eq.rec) (levels := levels) args
  have HH := constHead_mkApps (.const ``Eq.rec levels) args
  generalize E : ProofShape.mkApps (.const ``Eq.rec levels) args = e at H HC HH
  rcases H with (H | H) | H
  · cases H with
    | delta _ => change 0 = args.length at HC; omega
    | projIota => cases HH
  · cases H with
    | select hp _ hm | apply hp _ hm =>
      have := eqRec_match_arity hreg hoff hp hm HH
      omega
  · cases H with
    | intro hp _ _ hm =>
      have := eqRec_match_arity hreg hoff hp hm HH
      omega

/-- A proof-major Eq recursor remains blocked with any finite application
suffix. Every argument, including the suffix, retains its own ordinary path. -/
theorem ProofShape.Compute.eqRec_proof_spine_core_inv
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (R : ProofShape.Compute (ErasedIotaPrimitive D)
      (ProofShape.mkApps (ProofShape.eqRec v w α a M m b .proof) args) out) :
    ∃ α' a' M' m' b' args',
      out = ProofShape.mkApps (ProofShape.eqRec v w α' a' M' m' b' .proof) args' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) α α' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) a a' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) M M' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) m m' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) b b' ∧
      List.Forall₂ (ProofShape.Compute (ErasedIotaPrimitive D)) args args' := by
  have RS : ScopedCompute (fun _ => ErasedIotaPrimitive D) []
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) (α :: a :: M :: m :: b :: .proof :: args)) out :=
    R.scoped (fun H => .base H)
  rcases RS.const_spine_or_head with ⟨args', E, HA⟩ | ⟨k, args', target, hk, HA, HS⟩
  · cases HA with | cons Rα HA =>
      cases HA with | cons Ra HA =>
        cases HA with | cons RM HA =>
          cases HA with | cons Rm HA =>
            cases HA with | cons Rb HA =>
              cases HA with | cons Rp HA =>
                cases Rp.proof_fixed (fun H => erased_iota_primitive_head H)
                exact ⟨_, _, _, _, _, _, E, Rα.core_forget, Ra.core_forget,
                  RM.core_forget, Rm.core_forget, Rb.core_forget,
                  HA.imp (fun _ _ H => H.core_forget)⟩
  · by_cases hlong : 6 < args'.length
    · exact (erased_iota_eqRec_overapplied_no_root hreg hoff hlong HS).elim
    apply (erased_iota_eqRec_no_root hreg hoff hD (constHead_mkApps _ _) ?_ HS).elim
    by_cases hshort : args'.length ≤ 5
    · exact .inl ⟨_, _, rfl, hshort⟩
    have HL := HA.length_eq
    simp only [List.length_take, List.length_cons] at HL
    simp only [List.length_cons] at hk
    have hk' : k = 6 := by omega
    subst k
    simp only [List.take_succ_cons, List.take_zero] at HA
    cases HA with | cons _ HA =>
      cases HA with | cons _ HA =>
        cases HA with | cons _ HA =>
          cases HA with | cons _ HA =>
            cases HA with | cons _ HA =>
              cases HA with | cons Rp HA =>
                cases HA
                cases Rp.proof_fixed (fun H => erased_iota_primitive_head H)
                exact .inr ⟨_, rfl⟩

/-- A typed cast in function position can be removed after every full-core
path, leaving an ordinary-core reduct of the entire payload application.
The application suffix is arbitrary and may create beta redexes after removal.
Only the endpoint types require an earlier-stage comparison certificate. -/
theorem staged_cast_spine_level_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hf : env.HasType univs Γ f X)
    (ht : env.HasType univs Γ (VExpr.mkApps (typeCast u X Y q f) args) T)
    (HG : ∀ {a b Δ}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b)
    (R : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args)) out) :
    env.HasType univs Γ (VExpr.mkApps f args) T ∧
    ∃ minor, ProofShape.Compute (ErasedIotaPrimitive D)
        (proofErase Γ (VExpr.mkApps f args)) minor ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ out minor := by
  have HXY := (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY (HG .refl .refl)).1
      ⟨_, HasType.sort hu⟩
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ (HXY.of_l henv hΓ hX) hq hf
  have HE := (HC.toU.mkApps_congr_left henv hΓ ⟨_, ht⟩).of_l henv hΓ ht
  refine ⟨HE.hasType.2, ?_⟩
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ ht R
  by_cases hp : IsProof Γ (VExpr.mkApps (typeCast u X Y q f) args)
  · have EF := proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun H => .base H)).proof_fixed
      (fun H => erased_iota_primitive_head H)
    subst mid
    exact ⟨.proof, EF ▸ .refl, RT.in_static_stage⟩
  · have hpf : ¬ IsProof Γ (VExpr.mkApps f args) := fun H => hp ((isProof_congr hΓ HE).2 H)
    have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
      ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hY⟩
    have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, f, Y, q] ++ args) ht hp
    change proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args) = _ at ES
    simp only [List.map_append, List.map_cons, List.map_nil, Eq] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', args', rfl, _, Ra, _, Rm, Rb, Rargs⟩ :=
      RM.eqRec_proof_spine_core_inv hreg hoff hD
    have H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a' b' :=
      HG (Ra.mono (fun H => .inl H)) (Rb.mono (fun H => .inl H))
    refine ⟨ProofShape.mkApps m' args', ?_, RT.in_static_stage.trans ?_⟩
    · rw [proofErase_mkApps hΓ HE.hasType.2 hpf]
      exact ((Rm.scoped (Δ := []) (fun H => .base H)).mkApps
        (Rargs.imp (fun _ _ H => H.scoped (fun H => .base H)))).core_forget
    · exact H.next_stage_full.mkApps (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))

/-- Independent full-core tails of a cast application and its payload
application join at the next stage. Confluence is used only at the original
typed payload application, so created beta redexes need no new closure axiom. -/
theorem staged_cast_spine_level_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hf : env.HasType univs Γ f X)
    (ht : env.HasType univs Γ (VExpr.mkApps (typeCast u X Y q f) args) T)
    (HG : ∀ {a b Δ}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b)
    (RC : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args)) castOut)
    (RF : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (VExpr.mkApps f args)) payloadOut) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ castOut shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ payloadOut shared := by
  obtain ⟨hfargs, minor, RM, RR⟩ := staged_cast_spine_level_core_residual
    heq hs hl hcon hreg hoff hD hu hΓ hX hY hq hf ht HG RC
  obtain ⟨shared, RA, RB⟩ := hc hΓ hfargs (RM.mono (fun H => .inl H)) RF
  exact ⟨shared, RR.trans RA.in_static_stage, RB.in_static_stage⟩

end Lean4Lean.VEnv.Strengthening
