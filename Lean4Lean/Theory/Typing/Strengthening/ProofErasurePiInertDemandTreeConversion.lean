import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandHigherConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralHead

/-! # Recursive conversion through finite universe and function trees

Input and output conversion recurse on the reference tree. The right call initially has its result assigned at the right argument.
Typed reflection of the argument history constructs the equality needed to
assign it at the left argument too. No equality of raw result carriers and
no ordinary-core join between dependent instances is assumed. Selected Pi
exposure and retained source demand remain required; general strengthening
and full strong demand coverage are not established.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private erase_app_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Assigned raw typing realizes at any fixed actual carrier representative.
The carrier is a type, so its erasure reflects even if the operand is a proof. -/
theorem ProofShape.TypedAt.realize_carrier
    (H : TypedAt (proofEraseCtx Γ) e T) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (EA : proofErase Γ A = T) :
    ∃ a, env.HasType univs Γ a A ∧ proofErase Γ a = e := by
  obtain ⟨a, B, ha, Ea, EB⟩ := H.realize hΓ
  obtain ⟨_, hB⟩ := ha.isType henv hΓ
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hB hA (EB.trans EA.symm)).2
    (not_isProof_of_sort hΓ hB)
  exact ⟨a, ha.defeqU_r henv hΓ (HE.defeq hΓ), Ea⟩

/-- A demand base reflects to equality at supplied actual common typings.
This is original-context soundness of its retained carrier guard; it does not
promote semantic equality to a computation certificate. -/
theorem PiInertDemandBase.actual_defeq
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : PiInertDemandBase D (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)
      (proofErase Γ A)) : env.IsDefEq univs Γ a b A := by
  obtain ⟨n, HN⟩ := H.history
  exact proofErase_computed_joint_carrier_reflect
    (fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht (pi_inert_stage_embed R)) hΓ ha hb (HN.base .refl .refl .refl)

/-- A right application receives its assigned dependent result at the left
argument when a retained argument demand and both actual assignments are
available. The argument equality is constructed from the history. -/
theorem ProofShape.TypedAt.app_result_left
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedAt Δ g (.forallE A B))
    (HX : TypedAt Δ x A) (HXY : PiInertDemandValue p D Δ x y A)
    (HR : TypedSource Δ (.app g y)) : TypedAt Δ (.app g y) (B.inst x) := by
  obtain ⟨Γ, t, T, hΓ, EΓ, ht, Et⟩ := HR
  obtain ⟨g₀, y₀, rfl, hn, Eg, Ey⟩ := erase_app_inv Et
  obtain ⟨C, E, hg, hy⟩ := ht.app_inv henv hΓ
  obtain ⟨f₀, F, hf₀, Ef₀, EF⟩ := (EΓ ▸ H).realize hΓ
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EF
  have hng : ¬ IsProof Γ g₀ := fun hp => hn (IsProof.app_fn hΓ hg hy hp)
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hg hf₀ (Eg.trans Ef₀.symm)).2 hng
  have hg' := ((HE.defeq hΓ).of_r henv hΓ hf₀).hasType.1
  obtain ⟨⟨_, HD⟩, _, _⟩ := (hg.uniqU henv hΓ hg').forallE_inv henv hΓ
  have hy' := hy.defeqU_r henv hΓ HD.toU
  obtain ⟨_, hPi⟩ := hf₀.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨_, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A₀::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨x₀, hx, Ex⟩ := (EΓ ▸ HX).realize_carrier hΓ hA EA
  have hxy : env.IsDefEq univs Γ x₀ y₀ A₀ :=
    PiInertDemandBase.actual_defeq heq hs hΓ hx hy'
      (by simpa only [Ex, Ey, EA, EΓ] using HXY.base)
  have W : Ctx.SubstEq env univs Γ (VExpr.Subst.id.cons y₀) (VExpr.Subst.id.cons x₀) (A₀::Γ) :=
    .cons (.id henv.ordered hΓ) hA (by
      change env.IsDefEq univs Γ y₀ x₀ (A₀.subst .id)
      simpa only [VExpr.subst_id] using hxy.symm)
  have HB : env.IsDefEqU univs Γ (B₀.inst y₀) (B₀.inst x₀) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
      (hB.substDF henv.orderedStrong hΓA hΓ W).toU
  refine ⟨Γ, .app g₀ y₀, B₀.inst x₀, hΓ, EΓ,
    (hg'.app hy').defeqU_r henv hΓ HB, Et, ?_⟩
  simpa only [EA, EB, Ex] using proofErase_instN hΓA hx Ctx.InstN.zero hB

/-- A non-proof endpoint assigned both carriers transfers the second
assignment to any operand at the first. This uses ordinary type uniqueness
and typed erasure reflection, not a computational relation between carriers. -/
theorem ProofShape.TypedAt.transfer
    (HF : TypedAt Δ f A) (HF' : TypedAt Δ f B) (HG : TypedAt Δ g A)
    (hn : f ≠ .proof) : TypedAt Δ g B := by
  obtain ⟨Γ, f₀, A₀, hΓ, rfl, hf, Ef, EA⟩ := HF
  obtain ⟨B₀, hf', EB⟩ := HF'.realize_term hΓ hf Ef hn
  obtain ⟨_, hA⟩ := hf.isType henv hΓ
  obtain ⟨g₀, hg, Eg⟩ := HG.realize_carrier hΓ hA EA
  exact ⟨Γ, g₀, B₀, hΓ, rfl, hg.defeqU_r henv hΓ (hf.uniqU henv hΓ hf'), Eg, EB⟩

/-- Typed calls construct an arrow demand directly at assigned raw Pis.
Typed carrier reflection lets actual representatives share the selected
type. The resulting ground history is constructed by the fresh test. -/
theorem PiInertDemandValue.function_of_assigned_calls
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hf : TypedAt Δ f (.forallE C E)) (hg : TypedAt Δ g (.forallE C E))
    (run : ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
      PiInertDemandValue r D Λ x y (C.subst σ) →
      TypedSource Λ (.app (f.subst σ) x) → TypedSource Λ (.app (g.subst σ) y) →
      PiInertDemandValue s D Λ (.app (f.subst σ) x) (.app (g.subst σ) y)
        ((E.subst σ.lift).inst x)) :
    PiInertDemandValue (.arrow r s) D Δ f g (.forallE C E) := by
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf₀, Ef, EF⟩ := hf
  obtain ⟨C₀, E₀, rfl, _, EC, EE⟩ := erase_forallE_inv EF
  obtain ⟨_, hPi⟩ := hf₀.isType henv hΓ
  obtain ⟨g₀, hg₀, Eg⟩ := hg.realize_carrier hΓ hPi EF
  rw [← Ef, ← Eg, ← EF]
  apply PiInertDemandValue.function_of_typed_calls heq hs hc hRigid hΓ hf₀ hg₀
  intro Λ σ x y W HX HL HR
  simp only [EC, EE, Ef, Eg] at HX HL HR ⊢
  exact run W HX HL HR

/-- General assigned function conversion exposes source, target and reference
input assignments, and gives both outputs the left target result carrier.
The caller still supplies recursive input/output conversion; argument history
constructs the dependent result alignment needed by that recursion. -/
theorem PiInertDemandValue.function_convert_assigned
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hfOld : TypedAt Δ f (.forallE A B))
    (hfNew : TypedAt Δ f (.forallE C E)) (hgNew : TypedAt Δ g (.forallE C E))
    (hfRef : TypedAt Δ f (.forallE K L)) (hgRef : TypedAt Δ g (.forallE K L))
    (hn : f ≠ .proof)
    (H : PiInertDemandValue (.arrow p q) D Δ f g (.forallE A B))
    (input : ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
      TypedAt Λ x (A.subst σ) → TypedAt Λ y (A.subst σ) →
      TypedAt Λ x (K.subst σ) → TypedAt Λ y (K.subst σ) →
      TypedAt Λ x (C.subst σ) → TypedAt Λ y (C.subst σ) →
      PiInertDemandValue r D Λ x y (C.subst σ) →
      PiInertDemandValue p D Λ x y (A.subst σ))
    (output : ∀ {Λ σ x y a b}, PiInertCoreWorld D Δ Λ σ →
      TypedAt Λ a ((B.subst σ.lift).inst x) →
      TypedAt Λ a ((E.subst σ.lift).inst x) → TypedAt Λ b ((E.subst σ.lift).inst x) →
      TypedAt Λ a ((L.subst σ.lift).inst x) → TypedAt Λ b ((L.subst σ.lift).inst y) →
      PiInertDemandValue q D Λ a b ((B.subst σ.lift).inst x) →
      PiInertDemandValue s D Λ a b ((E.subst σ.lift).inst x)) :
    PiInertDemandValue (.arrow r s) D Δ f g (.forallE C E) := by
  apply PiInertDemandValue.function_of_assigned_calls heq hs hc hRigid hfNew hgNew
  intro Λ σ x y W HX HL HR
  have oldLeft := hfOld.subst W.typed
  have oldRight := (hfNew.transfer hfOld hgNew hn).subst W.typed
  have newLeft := hfNew.subst W.typed
  have newRight := hgNew.subst W.typed
  have refLeft := hfRef.subst W.typed
  have refRight := hgRef.subst W.typed
  have value := H.move W
  simp only [ProofShape.subst] at oldLeft oldRight newLeft newRight refLeft refRight value
  obtain ⟨OX, OL⟩ := oldLeft.app_parts HL
  have OY := (oldRight.app_parts HR).1
  obtain ⟨TX, TL⟩ := newLeft.app_parts HL
  have TY := (newRight.app_parts HR).1
  obtain ⟨KX, KL⟩ := refLeft.app_parts HL
  obtain ⟨KY, KR⟩ := refRight.app_parts HR
  have TR := newRight.app_result_left heq hs TX HX HR
  have arg := input W OX OY KX KY TX TY HX
  exact output W OL TL TR KL KR (value.app heq hc arg HL HR OL.sources.2)

/-- Finite universe/Pi interfaces, with arbitrary nesting on both sides
of each function type. The index is the finite demand used for conversion. -/
inductive PiInertTypeInterface : PiInertDemand → ProofShape → Prop where
  | sort : PiInertTypeInterface .ground (.sort u)
  | function : PiInertTypeInterface p A → PiInertTypeInterface q B →
      PiInertTypeInterface (.arrow p q) (.forallE A B)

/-- Selected carriers expose the interface's Pi tree. Leaf annotations may
be arbitrary, including dependent aliases. General outer Pi aliases are not
covered by this syntactic exposure condition. -/
inductive PiInertTypeCarrier : PiInertDemand → ProofShape → Prop where
  | base : PiInertTypeCarrier .ground A
  | function : PiInertTypeCarrier p A → PiInertTypeCarrier q B →
      PiInertTypeCarrier (.arrow p q) (.forallE A B)

omit [Params] in
/-- Universe/Pi reference interfaces contain no term variables. -/
theorem PiInertTypeInterface.closed (H : PiInertTypeInterface p T) (σ : ProofShape.Subst) :
    T.subst σ = T := by
  induction H generalizing σ with
  | sort => rfl
  | function HA HB ihA ihB => simp only [ProofShape.subst, ihA, ihB]

omit [Params] in
/-- Reference result interfaces agree at both arguments of a paired call. -/
theorem PiInertTypeInterface.inst_closed (H : PiInertTypeInterface p T) (x : ProofShape) :
    T.inst x = T := by
  rw [ProofShape.inst_eq_subst]
  exact H.closed _

omit [Params] in
/-- Selected exposure survives every interpreted substitution and dependent
instantiation, even though its arbitrary leaf annotations may change. -/
theorem PiInertTypeCarrier.subst (H : PiInertTypeCarrier p T) (σ : ProofShape.Subst) :
    PiInertTypeCarrier p (T.subst σ) := by
  induction H generalizing σ with
  | base => exact .base
  | function HA HB ihA ihB => exact .function (ihA σ) (ihB σ.lift)

/-- Actual representatives of reference trees have a telescope ending in a
universe. This is erasure shape inversion, not normalization of an alias. -/
theorem PiInertTypeInterface.realize_telescope (H : PiInertTypeInterface p R)
    (ER : proofErase Γ T = R) : ∃ n, DemandProfile.SortTelescope n T := by
  induction H generalizing Γ T with
  | sort => obtain rfl := erase_sort_inv ER; exact ⟨0, .sort⟩
  | function HA HB ihA ihB =>
    obtain ⟨A, B, rfl, _, _, EB⟩ := erase_forallE_inv ER
    obtain ⟨n, HN⟩ := ihB EB
    exact ⟨n+1, .forallE HN⟩

/-- Operands at a universe/Pi reference interface cannot be proof markers. -/
theorem PiInertTypeInterface.not_proof (H : PiInertTypeInterface p R)
    (HF : TypedAt Δ f R) : f ≠ .proof := by
  obtain ⟨Γ, f₀, T, hΓ, _, hf, Ef, ET⟩ := HF
  obtain ⟨n, HN⟩ := H.realize_telescope ET
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  have hn := (DemandProfile.Fits.of_sortTelescope hΓ hT HN).not_isProof
    hΓ (DemandProfile.spineDemand_valid n).visible hf
  intro E
  exact hn (proofErase_eq_proof.1 (Ef.trans E))

/-- Conversion for every finite universe/Pi interface, recursing on both
input and output structure. Argument history supplies common dependent target
result assignments; the reference result is closed. Selected Pi exposure and
source demand remain explicit, so this does not assert full strong coverage. -/
theorem PiInertTypeInterface.convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HR : PiInertTypeInterface p R)
    (HA : PiInertTypeCarrier p A) (HB : PiInertTypeCarrier p B)
    (hfOld : TypedAt Δ f A) (hfNew : TypedAt Δ f B) (hgNew : TypedAt Δ g B)
    (hfRef : TypedAt Δ f R) (hgRef : TypedAt Δ g R)
    (H : PiInertDemandValue p D Δ f g A) : PiInertDemandValue p D Δ f g B := by
  induction HR generalizing Δ f g A B with
  | sort =>
    exact H.sorted_reindex heq hs hfRef.sort_domain hgRef.sort_domain hfOld hfNew.sources.2
  | function HRa HRb ihA ihB =>
    cases HA with
    | function HAd HAb =>
      cases HB with
      | function HBd HBb =>
        apply H.function_convert_assigned heq hs hc hRigid hfOld hfNew hgNew hfRef hgRef
          ((PiInertTypeInterface.function HRa HRb).not_proof hfRef)
        · intro Λ σ x y _ OX OY KX KY TX _ HX
          rw [HRa.closed σ] at KX KY
          exact ihA (HBd.subst σ) (HAd.subst σ) TX OX OY KX KY HX
        · intro Λ σ x y a b _ OL TL TR KL KR result
          rw [HRb.closed σ.lift, HRb.inst_closed] at KL KR
          exact ihB
            (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using (HAb.subst σ.lift).subst (.one x))
            (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using (HBb.subst σ.lift).subst (.one x))
            OL TL TR KL KR result

/-- Original strong conversion children instantiate the full finite tree
rule using ordinary reference typing. Recursive calls follow the reference
tree, not substituted or context-converted strong derivations. -/
theorem StrongBounded.demand_convert_type_tree
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A B (.sort v))
    (termChild : StrongBounded env univs k Γ f g A)
    (hfRef : env.HasType univs Γ f R)
    (HR : PiInertTypeInterface p (proofErase Γ R))
    (HA : PiInertTypeCarrier p (proofErase Γ A))
    (HB : PiInertTypeCarrier p (proofErase Γ B))
    (H : PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A)) :
    PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ B) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  have hgRef := HT.hasType.2.defeqU_r henv hΓ (HT.hasType.1.uniqU henv hΓ hfRef)
  exact HR.convert heq hs hc hRigid HA HB (TypedAt.of_typed hΓ HT.hasType.1)
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.1))
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.2))
    (TypedAt.of_typed hΓ hfRef) (TypedAt.of_typed hΓ hgRef) H

omit [Params] in
/-- Every reference interface itself supplies the selected exposure tree. -/
theorem PiInertTypeInterface.carrier (H : PiInertTypeInterface p R) :
    PiInertTypeCarrier p R := by
  induction H with
  | sort => exact .base
  | function HA HB ihA ihB => exact .function ihA ihB

/-- Native variables construct the source demand at every finite interface
before conversion. The selected target may have dependent aliases at its
leaves, but must expose the interface's Pi tree. No source demand is assumed. -/
theorem pi_inert_native_type_tree_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (lookup : Lookup Γ i R)
    (HR : PiInertTypeInterface p (proofErase Γ R))
    (HU : PiInertTypeCarrier p (proofErase Γ U))
    (HE : env.IsDefEqU univs Γ R U) :
    PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar i)) (proofErase Γ U) := by
  have hf : env.HasType univs Γ (.bvar i) R := .bvar lookup
  have TF := TypedAt.of_typed hΓ hf
  have hn : ¬ IsProof Γ (.bvar i) := fun hp => HR.not_proof TF (proofErase_eq_proof.2 hp)
  have EV : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have EO : contextOracle (proofEraseCtx Γ) i = proofErase Γ R := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ lookup]
  have HV : TypedSource (proofEraseCtx Γ) (.bvar i) := ⟨Γ, .bvar i, R, hΓ, rfl, hf, EV⟩
  have HN : PiInertWorldValue D 0 (proofEraseCtx Γ) (.bvar i) (.bvar i) (proofErase Γ R) := by
    rw [← EO]
    exact pi_inert_native_variable_world_neutral.value HV HV
  have source : PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar i)) (proofErase Γ R) := by
    rw [EV]
    exact (PiInertCarrierValue.neutral HN).demand heq hs hc hRigid TF.sources.2
  have TU := TypedAt.of_typed hΓ (hf.defeqU_r henv hΓ HE)
  exact HR.convert heq hs hc hRigid HR.carrier HU TF TU TU TF TF source

omit [Params] in
/-- Function-valued outputs lie outside the preceding predicate towers.
This interface is in the new tree class at a concrete finite demand, while
no predicate-tower level has its shape. -/
theorem pi_inert_function_result_interface_separation (u v w : VLevel) :
    PiInertTypeInterface (.arrow .ground (.arrow .ground .ground))
      (.forallE (.sort u) (.forallE (.sort v) (.sort w))) ∧
    ∀ n, ¬ PiInertPredicateTower n (.forallE (.sort u) (.forallE (.sort v) (.sort w))) := by
  refine ⟨.function .sort (.function .sort .sort), ?_⟩
  intro n H
  cases H

end Lean4Lean.VEnv.Strengthening
