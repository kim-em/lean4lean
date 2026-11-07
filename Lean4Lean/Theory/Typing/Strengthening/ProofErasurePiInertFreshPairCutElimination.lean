import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshPairRootProgress
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldCutActivation

/-! # Eliminate function eta in the actual empty-prefix pair cut

Retain the full two-binder pair minimum before selecting another body root.
The cost/frame induction then eliminates all repeated function-eta transitions,
while preserving the original field history and its reserved budget.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- The actual empty-prefix eta cut supplies a marked full-pair minimum before
its next body root is selected. The original field computation and remaining
minimum fit strictly inside the same original budget. Both retained binders
and the distinguished supplying argument are preserved. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_marked_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (harity : info.nparams + info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
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
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K major ck frames)
    (hcost : cp+1+ct+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → budget ≤ j+k) :
    ∃ x charge C v smaller nextFrames, TypedSource Δ x ∧
      ScopedComputeCount (PiInertStage D n) charge Δ field x ∧
      DomainSort (A :: Δ) C v ∧ charge+smaller < budget ∧
      PiInertFreshFieldMinimum D Ω Δ family out A x [C]
        (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) smaller nextFrames := by
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
      have HRun : PiInertFreshFieldRun D Ω Δ family out A x [C]
          (fun body k => PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) xs K (.lam C' body) k)
          e (cs+ck) (frames+2) :=
        .retained (args := []) (HTvalue.pi_inert_compute heq hs RValue'.forget) SDinner RDomain
          (pi_inert_retained_frame_interpretation heq hs SDinner RDomain)
          (.supply HTlam WI HTnext' RNext HK)
      refine ⟨x, charge, C, v, innerBodyCost+cs+ck, frames+2,
        HTfield.pi_inert_compute heq hs RField.forget, RField, SDinner, by omega,
        _, bodyStage, innerBodyCost, cs+ck, e, HTvalue, RValue', HRun, by omega, HValueMin⟩
    · cases REmpty

/-- The actual global empty-prefix pair cut has no residual function-eta case
after cost/frame induction. It either activates its original field below a
retained telescope or reaches a selected saturated structure expansion of a
full fresh pair. Both outcomes preserve the SAME original field charge plus
remaining minimum strictly below the original budget. Reading these two
outcomes is still needed for the complete projection theorem. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_function_eta_eliminate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
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
    (HK : PiInertProjectionRunFrames D Ω family 0 out Δ K major ck frames)
    (hcost : cp+1+ct+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → budget ≤ j+k) :
    ∃ x charge, TypedSource Δ x ∧
      ScopedComputeCount (PiInertStage D n) charge Δ field x ∧
      ((∃ telescope nextValue smaller nextFrames, charge+smaller < budget ∧
        PiInertProjectionFrameMinimum D Ω family 0 out (telescope ++ Δ)
          (ProofShape.mkApps (.const info.ctorName []) [x.liftN telescope.length, nextValue]) smaller nextFrames) ∨
       (∃ controls nextValue smaller nextFrames, charge+smaller < budget ∧
        PiInertFreshPairStructureMinimum D Ω Δ family info out A x controls nextValue smaller nextFrames)) := by
  obtain ⟨x, charge, C, v, smaller, nextFrames, HTx, RField, SDC, hsmall, HMin⟩ :=
    H.empty_pair_prefix_marked_minimum heq hs hi hu (by omega) hshape SD RN HTfield HT
      ROuter houter RP REta HK hcost HM
  have HTlower : TypedSource Δ (.const info.ctorName []) := typed_spine_head HT
  rcases HMin.pair_function_eta_eliminate heq hs hi hu hp hf hz hshape hD hout hproj SD RN HTlower with
    ⟨telescope, nextValue, last, lastFrames, hlast, HLast⟩ |
    ⟨controls, nextValue, last, lastFrames, hlast, HLast⟩
  · exact ⟨x, charge, HTx, RField, .inl ⟨telescope, nextValue, last, lastFrames, by omega, HLast⟩⟩
  · exact ⟨x, charge, HTx, RField, .inr ⟨controls, nextValue, last, lastFrames, by omega, HLast⟩⟩

end Lean4Lean.VEnv.Strengthening
