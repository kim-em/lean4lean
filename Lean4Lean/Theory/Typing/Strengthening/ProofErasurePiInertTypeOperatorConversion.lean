import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertUniverseTransport

/-! # Guarded conversion for universe-valued type operators

The new domain is a universe alias, and the old dependent codomain is a
universe alias in its recorded binder. Actual whole-application typing puts
each argument at the old domain before instantiating that codomain. Universe
transport then constructs the argument and result conversions, and fresh
testing constructs the new function's ground history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tree_inst tree_comp_id
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees
variable [Params] {D : Definitions}

/-- An operand assigned a universe alias is independently sorted. The actual
alias equality converts its realized assignment; no exposure path is needed. -/
theorem ProofShape.UniverseAlias.assigned_sorted (H : UniverseAlias Δ T)
    (HX : TypedAt Δ x T) : ∃ u, DomainSort Δ x u := by
  obtain ⟨Γ, A, u, v, hΓ, EΓ, HE, EA⟩ := H
  obtain ⟨a, ha, Ea⟩ := (EΓ ▸ HX).realize_carrier hΓ HE.hasType.1 EA
  exact ⟨v, Γ, a, hΓ, EΓ, HE.defeq ha, Ea⟩

/-- An actual assigned argument interprets a fresh binder, including a proof
argument. Its carrier witness supplies the actual binder typing. -/
theorem ProofShape.TypedAt.argument_substitution (H : TypedAt Δ x A) :
    ContextSubstitution (A::Δ) Δ (ProofShape.Subst.one x) := by
  obtain ⟨Γ, a, T, hΓ, EΓ, ha, Ea, ET⟩ := H
  obtain ⟨u, hT⟩ := ha.isType henv hΓ
  have hΓT : OnCtx (T::Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W : ContextSubstitution (proofEraseCtx (T::Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ a)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓT ha)
      (erasedSubstAgreement_one hΓT ha)
  intro Γ' hΓ' EΓ'
  have E : proofEraseCtx Γ' = proofEraseCtx (T::Γ) := by
    simpa only [proofEraseCtx, ET, EΓ] using EΓ'
  simpa only [EΓ, Ea] using W hΓ' E

/-- Extend an arbitrary typed substitution by an assigned raw argument at
the substituted domain. This does not assert a core-world condition. -/
theorem ProofShape.ContextSubstitution.cons_assigned
    (W : ContextSubstitution Δ Λ σ) (HX : TypedAt Λ x (A.subst σ)) :
    ContextSubstitution (A::Δ) Λ (σ.cons x) := by
  have V : ContextSubstitution (A::Δ) Λ (σ.lift.comp (ProofShape.Subst.one x)) :=
    ContextSubstitution.comp W.cons HX.argument_substitution
  intro Γ hΓ EΓ
  simpa only [ProofShape.Subst.lift_comp_one] using V hΓ EΓ

omit [Params] in
/-- Changing annotations preserves the absence of explicit guarded calls. -/
theorem PiInertGuardedTree.Ordinary.subst {p : PiInertGuardedTree} {σ : ProofShape.Subst}
    (H : p.Ordinary) : (p.subst σ).Ordinary := by
  induction p with
  | plain => trivial
  | both p q ihp ihq => exact ⟨ihp H.1, ihq H.2⟩
  | call => exact H.elim

/-- Ordinary trees require no type-only guarded exposure supply. -/
theorem PiInertGuardedTreeSupply.of_ordinary (H : p.Ordinary) :
    PiInertGuardedTreeSupply p ρ D Δ T := by
  induction p with
  | plain => trivial
  | both p q ihp ihq => exact ⟨ihp H.1, ihq H.2⟩
  | call => exact H.elim

/-- Change a guarded function's interface when the new argument carrier and
old dependent result carrier are universe aliases. The old input tree must
be ordinary, so its action is not merely vacuous at an impossible call input.
Argument/result transports and the new ground history are constructed, not
assumed. The old selected carrier may itself be a guarded alias. -/
theorem PiInertGuardedTreeValue.type_operator_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertGuardedTreeValue (.call A B p q) ProofShape.Subst.id D Δ f g T)
    (HF : TypedAt Δ f (.forallE C E)) (HG : TypedAt Δ g (.forallE C E))
    (HC : UniverseAlias Δ C) (HB : UniverseAlias (A::Δ) B)
    (HP : p.Ordinary) (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedTreeValue (.call C E r s) ProofShape.Subst.id D Δ f g (.forallE C E) := by
  obtain ⟨n, RT⟩ := H.2.1
  have oldF := H.1.left.world_computation heq hs RT
  have oldG := H.1.right.world_computation heq hs RT
  simp only [ProofShape.subst_id, ProofShape.Subst.id_lift] at oldF oldG
  apply PiInertGuardedTreeValue.of_calls heq hs hc hRigid HF HG (.of_ordinary HR)
  intro Λ σ x y W HX HL HRight
  have FL := HF.subst W.typed
  have FR := HG.subst W.typed
  have OL := oldF.subst W.typed
  have OR := oldG.subst W.typed
  simp only [ProofShape.subst] at FL FR OL OR
  obtain ⟨TX, TL⟩ := FL.app_parts HL
  have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HRight
  have OX := (OL.app_parts HL).1
  have OY := (OR.app_parts HRight).1
  have CU := HC.substitute W.typed
  obtain ⟨u, SX⟩ := CU.assigned_sorted TX
  have inputBase : PiInertAssignedBase D Λ x y (A.subst σ) :=
    ⟨OX, OY, OX.sources.1, OY.sources.1, OX.sources.2, by
      obtain ⟨k, HK⟩ := HX.base.ground.history
      exact ⟨k, HK.universe_alias_reindex heq hs CU⟩⟩
  have input : PiInertGuardedTreeValue p σ D Λ x y (A.subst σ) :=
    inputBase.sorted_tree SX HP
  have body := H.2.2 W input HL HRight
  have BU := HB.substitute (ContextSubstitution.cons_assigned W.typed OX)
  obtain ⟨v, SBody⟩ := BU.assigned_sorted body.base.left
  rw [tree_inst] at TL TR
  have outputBase : PiInertAssignedBase D Λ (.app (f.subst σ) x) (.app (g.subst σ) y)
      (E.subst (σ.cons x)) :=
    ⟨TL, TR, TL.sources.1, TR.sources.1, TL.sources.2, by
      obtain ⟨k, HK⟩ := body.base.ground.history
      exact ⟨k, HK.universe_alias_reindex heq hs BU⟩⟩
  exact outputBase.sorted_tree SBody HS

/-- The interface conversion theorem works at a substituted annotation map.
The old codomain alias moves beneath the old written binder before the
argument is supplied; no history is moved across unequal binder contexts. -/
theorem PiInertGuardedTreeValue.type_operator_convert_substituted
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (W : ContextSubstitution Δ Λ σ)
    (H : PiInertGuardedTreeValue (.call A B p q) σ D Λ f g T)
    (HF : TypedAt Λ f (.forallE (C.subst σ) (E.subst σ.lift)))
    (HG : TypedAt Λ g (.forallE (C.subst σ) (E.subst σ.lift)))
    (HC : UniverseAlias Δ C) (HB : UniverseAlias (A::Δ) B)
    (HP : p.Ordinary) (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedTreeValue (.call C E r s) σ D Λ f g
      (.forallE (C.subst σ) (E.subst σ.lift)) := by
  have old : PiInertGuardedTreeValue ((PiInertGuardedTree.call A B p q).subst σ)
      ProofShape.Subst.id D Λ f g T := by
    simpa only [PiInertGuardedTreeValue.subst_iff, tree_comp_id] using H
  have result := old.type_operator_convert heq hs hc hRigid HF HG
    (HC.substitute W) (HB.substitute W.cons) HP.subst (HR.subst (σ := σ)) (HS.subst (σ := σ.lift))
  change PiInertGuardedTreeValue ((PiInertGuardedTree.call C E r s).subst σ)
    ProofShape.Subst.id D Λ f g (.forallE (C.subst σ) (E.subst σ.lift)) at result
  simpa only [PiInertGuardedTreeValue.subst_iff, tree_comp_id] using result

/-- Paired type-operator interpretation converts both function interfaces
under arbitrary paired typed substitutions. Cross assignments come from the
old assigned comparison; each old codomain is instantiated in its own source
environment. No argument/output semantic transport premise is introduced. -/
theorem PiInertGuardedPairInterpretation.convert_type_operator
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertGuardedPairInterpretation D Δ uses f g T U (.call A B p q) (.call A B p q))
    (HF : TypedAt Δ f (.forallE C E)) (HG : TypedAt Δ g (.forallE C E))
    (HC : UniverseAlias Δ C) (HB : UniverseAlias (A::Δ) B)
    (HP : p.Ordinary) (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedPairInterpretation D Δ uses f g (.forallE C E) (.forallE C E)
      (.call C E r s) (.call C E r s) := by
  refine ⟨HF, HG, ?_⟩
  intro Λ σ τ WL WR images
  have old := H.run WL WR images
  have FL := HF.subst WL
  have GR := HG.subst WR
  have GL := old.forward.base.transfer heq hs FL
  have FR := old.backward.base.transfer heq hs GR
  simp only [ProofShape.subst] at FL GR GL FR ⊢
  exact ⟨old.forward.type_operator_convert_substituted heq hs hc hRigid WL FL GL HC HB HP HR HS,
    old.backward.type_operator_convert_substituted heq hs hc hRigid WR GR FR HC HB HP HR HS⟩

/-- Original strong conversion for a type operator whose source domain and
dependent codomain are arbitrary actual universe aliases. The type child
transfers the domain alias to the new interface. The old codomain alias stays
in its recorded context until a typed argument instantiates it. Only ordinary
alias equalities are required; no semantic transport certificates are added. -/
theorem StrongBounded.paired_convert_type_operator_aliases
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ (.forallE A B) (.forallE C E) (.sort w))
    (termChild : StrongBounded env univs k Γ f g (.forallE A B))
    (HA : env.IsDefEq univs Γ A (.sort u) (.sort a))
    (HB : env.IsDefEq univs (A::Γ) B (.sort v) (.sort b))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B))
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p q)
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p q))
    (HP : p.Ordinary) (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE C E)) (proofErase Γ (.forallE C E))
      (.call (proofErase Γ C) (proofErase (C::Γ) E) r s)
      (.call (proofErase Γ C) (proofErase (C::Γ) E) r s) := by
  have HE := typeChild.strong.defeq
  have HF := termChild.strong.defeq
  obtain ⟨⟨z, HD⟩, _⟩ := HE.toU.forallE_inv henv hΓ
  have HC : UniverseAlias (proofEraseCtx Γ) (proofErase Γ C) :=
    .of_typed hΓ (HD.symm.trans (HA.toU.of_l henv hΓ HD.hasType.1))
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, a, HA.hasType.1⟩
  have HU : UniverseAlias (proofErase Γ A :: proofEraseCtx Γ) (proofErase (A::Γ) B) :=
    .of_typed hΓA HB
  have EP : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) :=
    if_neg (not_isProof_of_sort hΓ HE.hasType.2)
  rw [EP]
  exact H.convert_type_operator heq hs hc hRigid
    (EP ▸ TypedAt.of_typed hΓ (HE.defeq HF.hasType.1))
    (EP ▸ TypedAt.of_typed hΓ (HE.defeq HF.hasType.2)) HC HU HP HR HS

/-- Original strong conversion of a universe-to-universe type operator
constructs both guarded target interfaces. Injectivity of the original type
child supplies the new domain alias, while the source codomain is a literal
universe. No separate semantic type-child, input transport, output transport,
or target ground history is assumed. The term-child interpreter still carries
its recursive source action, and general function conversion remains open. -/
theorem StrongBounded.paired_convert_type_operator
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ (.forallE (.sort u) (.sort v))
      (.forallE C E) (.sort w))
    (termChild : StrongBounded env univs k Γ f g (.forallE (.sort u) (.sort v)))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE (.sort u) (.sort v)))
      (proofErase Γ (.forallE (.sort u) (.sort v)))
      (.call (.sort u) (.sort v) p q) (.call (.sort u) (.sort v) p q))
    (HP : p.Ordinary) (HR : r.Ordinary) (HS : s.Ordinary) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE C E)) (proofErase Γ (.forallE C E))
      (.call (proofErase Γ C) (proofErase (C::Γ) E) r s)
      (.call (proofErase Γ C) (proofErase (C::Γ) E) r s) := by
  have HE := typeChild.strong.defeq
  have HF := termChild.strong.defeq
  obtain ⟨⟨z, HD⟩, _⟩ := HE.toU.forallE_inv henv hΓ
  have HC : UniverseAlias (proofEraseCtx Γ) (proofErase Γ C) := .of_typed hΓ HD.symm
  obtain ⟨⟨a, hA⟩, b, hB⟩ := HE.hasType.1.forallE_inv henv
  have hΓA : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, a, hA⟩
  have EA : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hA)
  have EB : proofErase (.sort u :: Γ) (.sort v) = .sort v :=
    if_neg (not_isProof_of_sort hΓA hB)
  have HB : UniverseAlias (.sort u :: proofEraseCtx Γ) (.sort v) := by
    simpa only [proofEraseCtx, EA, EB] using UniverseAlias.of_typed hΓA hB
  have EP : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) :=
    if_neg (not_isProof_of_sort hΓ HE.hasType.2)
  rw [EP]
  apply H.convert_type_operator heq hs hc hRigid
    (EP ▸ TypedAt.of_typed hΓ (HE.defeq HF.hasType.1))
    (EP ▸ TypedAt.of_typed hΓ (HE.defeq HF.hasType.2)) HC HB HP HR HS

end Lean4Lean.VEnv.Strengthening
