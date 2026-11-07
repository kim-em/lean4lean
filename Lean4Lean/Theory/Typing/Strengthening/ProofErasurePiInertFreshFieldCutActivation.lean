import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldActivation

/-! # Original-field accounting at the supplied fresh-field cut

The actual outer argument paths determine the original field's supplied image.
Read the surviving value eta in its original binder context and retain its
outer consuming continuation. Component readout then activates that image
above the observer; otherwise a selected native root remains below both
binders, with the same field charge reserved in its smaller budget.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : Definitions}

/-- Starting from the actual globally minimal empty-prefix pair eta cut,
either the original field reaches a supplied image with a smaller one-binder
pair minimum, or the nested value body has another native root with a smaller
observed budget after reserving that SAME field history. The actual outer
argument paths provide the field charge; no native certificate is assumed for
that argument and no old body path is transported through its substitution.
The remaining native-root alternative still requires recursive field readout. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_activation_or_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (harity : info.nparams + info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HTfield : TypedSource Δ field)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (ROuter : ScopedArgumentsCount (PiInertStage D n) Δ outerCost [field, value] args)
    (houter : outerCost ≤ cp)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) args))
    (REta : PiInertStage D n Δ (.const info.ctorName [])
      (.lam A (.app (.const info.ctorName []) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName [] [] A u args major ct
      (ConstructorEtaBodyRoot D))
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K major ck frames)
    (hcost : cp+1+ct+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → budget ≤ j+k) :
    ∃ x charge, TypedSource Δ x ∧
      ScopedComputeCount (PiInertStage D n) charge Δ field x ∧
      ((∃ domain value' smaller, charge+smaller < budget ∧
        PiInertProjectionFrameMinimum D Δ family 0 out (domain :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) [x.liftN 1, value']) smaller (frames+1)) ∨
       (∃ C v stage pre pending target ca, DomainSort (A :: Δ) C v ∧
        ScopedArgumentsCount (PiInertStage D stage) (C :: A :: Δ) ca
          [.bvar 1, etaArgument v] (pre ++ pending) ∧
        ConstructorEtaBodyRoot D stage (C :: A :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
        PiInertFreshFieldObservedRoot D Δ family out (budget-charge) A C v x stage
          (ProofShape.mkApps (.const info.ctorName []) pre) target)) := by
  have HS := H.empty_pair_prefix_supplies_fresh_field heq hs hi hu harity hshape SD RN HT RP
    HK.forget.holds hcost HM
  obtain ⟨domain, body, x, xs, cf, ca, cs, cd, cb, m, levels, pre, pending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, HL, HA, RBodyPrefix, HR, HN, RT, HBodyMin, HJointMin,
    HI, HTR, WI, HC, ESource, innerStage, hinner, HE⟩ := HS
  cases HL
  have EPre : pre = [etaArgument u] :=
    (const_spine_inj (ps' := [etaArgument u]) ESource).2.2
  have hlen := HA.1.length_eq
  have EPending : pending = [] := List.eq_nil_of_length_eq_zero (by
    simp only [EPre, List.map_nil, List.nil_append, List.length_append, List.length_cons,
      List.length_nil] at hlen
    omega)
  subst pre pending
  have ESlot := pi_inert_pair_constructor_eta_slot heq hs hi hu hshape SD RN
  rw [ESlot] at HTR HR HE RBodyPrefix
  cases HE with
  | intro RNinner SDinner =>
    rename_i C Binner v
    have HTlong := HTR.pi_inert_compute heq hs (ScopedComputeCount.base HR).forget
    have Rlambda : ScopedComputeCount (PiInertStage D m) tb (A :: Δ)
        (ProofShape.mkApps (.lam C (.app ((ProofShape.app (.const info.ctorName []) (.bvar 0)).liftN 1)
          (etaArgument v))) []) body := RT
    rcases Rlambda.pi_inert_lambda_spine_or_beta with
      ⟨C', e, rest, innerCost, argumentCost, htail, EBody, RInner, REmpty⟩ |
      ⟨C', e, arg, rest, innerCost, argumentCost, suffixCost, htail, RInner, REmpty, RSuffix⟩
    · cases REmpty
      simp only [ProofShape.mkApps] at EBody
      subst body
      obtain ⟨innerDomainCost, innerBodyCost, bodyStage, hsplit, RDomain, RValue⟩ :=
        pi_inert_native_eta_count_body_readout heq hs
          (erased_static_structure_eta_expansion_stage_descent heq hs innerStage)
          HTR (.intro RNinner SDinner) RInner
      have HTvalue : TypedSource (C :: A :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) := by
        simpa only [ProofShape.mkApps, ProofShape.liftN, liftVar, Nat.lt_irrefl, Nat.add_zero,
          ↓reduceIte] using (ScopedHole.lamBody C .hole).typed HTlong
      have RValue' : ScopedComputeCount (PiInertStage D bodyStage) innerBodyCost (C :: A :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) e := by
        simpa only [ProofShape.mkApps, ProofShape.liftN, liftVar, Nat.lt_irrefl, Nat.add_zero,
          ↓reduceIte] using RValue
      have HTlam : TypedSource (A :: Δ) (.lam C' e) := HTlong.pi_inert_compute heq hs RInner.forget
      have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
          (ProofShape.mkApps (.lam domain (.lam C' e)) (x :: xs))
          (ProofShape.mkApps ((ProofShape.lam C' e).inst x) xs) := by
        simpa only [ProofShape.mkApps] using
          (ScopedComputeCount.beta (BetaRed.beta (A := domain) (b := .lam C' e) (a := x))).mkApps
            (ScopedArgumentsCount.refl (args := xs))
      have HTouterlong := HT.pi_inert_compute heq hs
        ((ScopedComputeCount.base REta).mkApps (ScopedArgumentsCount.refl (args := args))).forget
      have HTnext := HTouterlong.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
      have HTnext' : TypedSource Δ
          (ProofShape.mkApps ((ProofShape.lam C' e).subst (ProofShape.Subst.one x)) xs) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
      have RNext : ScopedComputeCount (PiInertStage D n) cs Δ
          (ProofShape.mkApps ((ProofShape.lam C' e).subst (ProofShape.Subst.one x)) xs) major := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
      obtain ⟨charge, hcharge, RField⟩ : ∃ charge, charge ≤ outerCost+ca ∧
          ScopedComputeCount (PiInertStage D n) charge Δ field x := by
        have RAll := ROuter.trans RX
        generalize htotal : outerCost+ca = total at RAll
        cases RAll with
        | cons RFirst RRest => exact ⟨_, by omega, RFirst⟩
      have HValueMin : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (C :: A :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) body →
          PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) xs K (.lam C' body) k →
          innerBodyCost+cs+ck ≤ j+k := by
        rintro later j body k RJ ⟨suffixStage, suffixCount, endpoint, tailCount, hsum, RK, HK'⟩
        have raise : ∀ {Ξ a b}, PiInertStage D m Ξ a b → PiInertStage D (max m later) Ξ a b :=
          pi_inert_stage_mono (Nat.le_max_left m later)
        have RL := ScopedComputeCount.lam (RDomain.mono raise)
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right m later)))
        have RRoot := (ScopedComputeCount.base (raise HR)).trans (by
          simpa only [ProofShape.mkApps, ProofShape.liftN, liftVar, Nat.lt_irrefl, Nat.add_zero,
            ↓reduceIte] using RL)
        have RB := (RBodyPrefix.mono raise).trans (by
          simpa only [ProofShape.mkApps, List.append_nil] using RRoot)
        have liftOuter : ∀ {Ξ a b}, PiInertStage D n Ξ a b →
            PiInertStage D (max n suffixStage) Ξ a b :=
          pi_inert_stage_mono (Nat.le_max_left n suffixStage)
        have RK' : ScopedComputeCount (PiInertStage D (max n suffixStage)) suffixCount Δ
            (ProofShape.mkApps ((ProofShape.lam C' body).inst x) xs) endpoint := by
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
            RK.mono (pi_inert_stage_mono (Nat.le_max_right n suffixStage))
        have RAlt := pi_inert_counted_lambda_body_replace (RP.mono liftOuter) (liftOuter REta)
          (RD.mono liftOuter) (by simpa only [ProofShape.mkApps, ProofShape.liftN, ESlot] using RB)
          (RX.mono liftOuter) RK'
        have HH := HM _ _ endpoint tailCount RAlt HK'
        omega
      have HProgress := pi_inert_fresh_pair_retained_transfer_or_root heq hs hi hu hp hshape hD hout hproj
        SDinner RDomain HTvalue RValue' HTlam WI HTnext' RNext HK
        (charge := charge) (budget := budget) (by omega) HValueMin
      refine ⟨x, charge, HTfield.pi_inert_compute heq hs RField.forget, RField, ?_⟩
      rcases HProgress with ⟨domain', value', smaller, _, hsmall, HMinimum⟩ |
        ⟨pre', pending', target', cp', ct', ca', hcut', hca', HA', RP', HR', RT', HRoot', HObserved'⟩
      · exact .inl ⟨domain', value', smaller, hsmall, HMinimum⟩
      · exact .inr ⟨C, v, bodyStage, pre', pending', target', ca', SDinner, HA', HRoot', HObserved'⟩
    · cases REmpty

end Lean4Lean.VEnv.Strengthening
