import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldEtaCut

/-! # Activate a fresh type field through its actual consuming frame

A field can still be a temporary variable before the original type argument
is supplied. Focusing the actual application below a retained telescope maps
that variable to the supplied argument, lifted beneath precisely that telescope.
The earlier guarded computation is not substituted. A component endpoint in
the two-binder eta body therefore enters the existing ambient-field minimum;
a non-component endpoint retains its selected smaller native root.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

omit [Params] in
private theorem fresh_field_image :
    (ProofShape.bvar depth).subst ((ProofShape.Subst.one x).liftN depth) = x.liftN depth := by
  rw [← ProofShape.inst_eq_subst]
  simp [ProofShape.inst]

/-- Execute the actual consuming frame beneath a nonempty retained telescope.
The tracked fresh field becomes the supplied argument at exactly the retained
depth. The new source and minimum belong to the actual suffix; no native
certificate or substitution transport for the preceding body path is assumed.
The application frame is removed while the retained depth is preserved. -/
theorem PiInertRetainedPrefixCount.fresh_field_application_progress
    {plug : ProofShape → ProofShape} {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HP : PiInertRetainedPrefixCount D Ξ (A :: Δ) plug depth) (hd : 0 < depth)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (he : e = ProofShape.mkApps (.const ctor levels) (.bvar depth :: fields))
    (RP : ScopedComputeCount (PiInertStage D n) cb Ξ source e)
    (HT : TypedSource Δ (ProofShape.mkApps ((plug e).subst (ProofShape.Subst.one x)) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs Δ
      (ProofShape.mkApps ((plug e).subst (ProofShape.Subst.one x)) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K' endpoint ck remaining)
    (EK : ∀ body k, K body k ↔
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K' (plug body) k)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j Ξ source body →
      K body k → cb+(cs+ck) ≤ j+k) :
    ∃ telescope smaller, telescope.length = depth ∧
      ContextSubstitution Ξ (telescope ++ Δ) ((ProofShape.Subst.one x).liftN depth) ∧
      smaller ≤ cs+ck ∧ remaining+depth < remaining+depth+1 ∧
      PiInertProjectionFrameMinimum D Ω family index out (telescope ++ Δ)
        (ProofShape.mkApps (.const ctor levels)
          (x.liftN depth :: fields.map (·.subst ((ProofShape.Subst.one x).liftN depth))))
        smaller (remaining+depth) := by
  obtain ⟨telescope, smaller, hlen, WS, hsmall, hframes, Hbody⟩ :=
    HP.projection_application_progress heq hs hd (.inst W) RP HT RT HK EK HM rfl
  refine ⟨telescope, smaller, hlen, WS, hsmall, hframes, ?_⟩
  rw [he] at Hbody
  have EF := fresh_field_image (depth := depth) (x := x)
  change (ProofShape.Subst.one x).liftN depth depth = x.liftN depth at EF
  simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, EF] using Hbody

/-- A selected root below the temporary type and value binders whose exact
remaining continuation retains the value lambda and consumes the type binder
with the recorded argument `x`. Unlike an unrestricted observed root, this
keeps the relation between the fresh type field and its eventual supplied
image available to subsequent recursive readout. All minima still quantify
over arbitrary raw competitors at every finite stage. -/
def PiInertFreshFieldObservedRoot (D : Definitions) (Δ : List ProofShape)
    (family : Name) (out : ProofShape) (bound : Nat) (A C : ProofShape) (v : VLevel)
    (x : ProofShape) (stage : Nat) (source target : ProofShape) : Prop :=
  ∃ pending tailCost e C' domainStage cd suffixArgs suffixStage cs endpoint ck K frames,
    1+tailCost+cs+ck < bound ∧
    TypedSource (C :: A :: Δ) (ProofShape.mkApps source pending) ∧
    PiInertStage D stage (C :: A :: Δ) source target ∧
    ScopedComputeCount (PiInertStage D stage) tailCost (C :: A :: Δ)
      (ProofShape.mkApps target pending) e ∧
    DomainSort (A :: Δ) C v ∧
    ScopedComputeCount (PiInertStage D domainStage) cd (A :: Δ) C C' ∧
    TypedSource (A :: Δ) (.lam C' e) ∧
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) ∧
    TypedSource Δ (ProofShape.mkApps ((ProofShape.lam C' e).subst (ProofShape.Subst.one x)) suffixArgs) ∧
    ScopedComputeCount (PiInertStage D suffixStage) cs Δ
      (ProofShape.mkApps ((ProofShape.lam C' e).subst (ProofShape.Subst.one x)) suffixArgs) endpoint ∧
    PiInertProjectionRunFrames D Δ family 0 out Δ K endpoint ck frames ∧
    ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (C :: A :: Δ)
      (ProofShape.mkApps source pending) body →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) suffixArgs K (.lam C' body) k →
      1+tailCost+cs+ck ≤ j+k

/-- Forget only the specific future type-binder argument. The witness already
contains an ordinary observed-root minimum; its exact retained/application
run is reconstructed from the recorded domain path and actual suffix. -/
theorem PiInertFreshFieldObservedRoot.forget
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertFreshFieldObservedRoot D Δ family out bound A C v x stage source target) :
    PiInertObservedBodyRoot D Δ family 0 out bound stage (C :: A :: Δ) source target := by
  obtain ⟨pending, tailCost, e, C', domainStage, cd, suffixArgs, suffixStage, cs, endpoint,
    ck, K, frames, hsmall, HT, HR, RT, SD, RD, HTlam, W, HTnext, RNext, HK, HM⟩ := H
  have RRoot := ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))).trans RT
  have HTe := HT.pi_inert_compute heq hs RRoot.forget
  refine ⟨pending, tailCost, e, cs+ck,
    (fun body k => PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) suffixArgs K (.lam C' body) k),
    by omega, HT, HR, RT, ?_, ?_⟩
  · exact .retained (args := []) HTe SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD)
      (.application HTlam (.inst W) HTnext RNext HK.forget)
  · intro later j body k RJ RK
    have HH := HM later j body k RJ RK
    omega

/-- Analyze the actual body of the value eta while its type field is still
one binder farther out. Its continuation retains the value lambda and then
consumes the type binder with `x`. In the component branch the fresh field
becomes `x.liftN 1` in a smaller minimum above the observer. Otherwise the SAME
body path has a native function/structure eta root and a smaller observed
execution. The original-field charge is reserved in both alternatives.
Recursive field readout through the native-root alternative remains open. -/
theorem pi_inert_fresh_pair_retained_transfer_or_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort (A :: Δ) C v)
    (RD : ScopedComputeCount (PiInertStage D domainStage) cd (A :: Δ) C C')
    (HT : TypedSource (C :: A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]))
    (RB : ScopedComputeCount (PiInertStage D n) cb (C :: A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) e)
    (HTlam : TypedSource (A :: Δ) (.lam C' e))
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HTnext : TypedSource Δ
      (ProofShape.mkApps ((ProofShape.lam C' e).subst (ProofShape.Subst.one x)) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs Δ
      (ProofShape.mkApps ((ProofShape.lam C' e).subst (ProofShape.Subst.one x)) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K endpoint ck frames)
    (hbudget : charge+cb+cs+ck < budget)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (C :: A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) body →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K (.lam C' body) k →
      cb+cs+ck ≤ j+k) :
    (∃ domain value smaller, smaller ≤ cs+ck ∧ charge+smaller < budget ∧
      PiInertProjectionFrameMinimum D Δ family 0 out (domain :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [x.liftN 1, value]) smaller (frames+1)) ∨
    (∃ pre bodyPending target cp ct ca, cp+1+ct ≤ cb ∧ ca ≤ cp ∧
      ScopedArgumentsCount (PiInertStage D n) (C :: A :: Δ) ca
        [.bvar 1, etaArgument v] (pre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D n) cp (C :: A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v])
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) ∧
      PiInertStage D n (C :: A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ScopedComputeCount (PiInertStage D n) ct (C :: A :: Δ) (ProofShape.mkApps target bodyPending) e ∧
      ConstructorEtaBodyRoot D n (C :: A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      PiInertFreshFieldObservedRoot D Δ family out (budget-charge) A C v x n
        (ProofShape.mkApps (.const info.ctorName []) pre) target) := by
  have WI : ContextSubstitution (C :: A :: Δ) (C' :: A :: Δ) ProofShape.Subst.id :=
    pi_inert_retained_frame_interpretation heq hs SD RD
  let KP : ProofShape → Nat → Prop := fun body k =>
    PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K (.lam C' body) k
  have HKfull : PiInertProjectionRunFrames D Δ family 0 out (C :: A :: Δ) KP e (cs+ck) (frames+2) :=
    .retained (args := []) (HT.pi_inert_compute heq hs RB.forget) SD RD WI
      (.application HTlam (.inst W) HTnext RT HK)
  rcases RB.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, fields, ch, ca, hcounts, rfl, HL, _, HA⟩ |
    ⟨levels, pre, bodyPending, target, cp, ct, ca, hcut, hca, HL, HA, RP, HR, HN, Rtail⟩
  · cases HL
    cases HA with
    | cons RF rest =>
      cases rest with
      | cons RV last =>
        cases last
        rename_i fieldCost field valueCost value
        have EF := RF.forget.pi_inert_bvar_fixed
        have HP : PiInertRetainedPrefixCount D (C :: A :: Δ) (A :: Δ)
            (fun body => .lam C' body) 1 := .retained (args := []) SD RD WI .refl
        obtain ⟨telescope, smaller, hlen, WS, hsmall, _, Hnext⟩ :=
          HP.fresh_field_application_progress (ctor := info.ctorName) (levels := []) (fields := [value])
            heq hs (by omega) W
            (by simp only [EF]) RB HTnext RT HK (K := KP) (fun _ _ => Iff.rfl)
            (by simpa only [KP, Nat.add_assoc] using HM)
        cases telescope with
        | nil => simp at hlen
        | cons domain rest =>
          have ER : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
          subst rest
          exact .inl ⟨domain, _, smaller, hsmall, by omega,
            by simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] using Hnext⟩
  · cases HL
    have HSorted := HKfull.forget.pair_sorted hi hu hp hshape
    have HRoot := pi_inert_sorted_frames_constructor_root heq hs (henv.projectionCtorRigid hi)
      hD HT RP HR HN Rtail HSorted hout hproj (cost := cb+cs+ck) (by omega) HM
    have HTwhole : TypedSource (C :: A :: Δ)
        (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) bodyPending) := by
      simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
    refine .inr ⟨pre, bodyPending, target, cp, ct, ca, hcut, hca, HA, RP, HR, Rtail, HRoot,
      bodyPending, ct, e, C', domainStage, cd, pending, m, cs, endpoint, ck, K, frames,
      by omega, HTwhole, HR, Rtail, SD, RD, HTlam, W, HTnext, RT, HK, ?_⟩
    intro later j tail k RJ RK
    have RAlt := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (by simpa only [ProofShape.mkApps_append] using RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ tail k RAlt RK
    omega

end Lean4Lean.VEnv.Strengthening
