import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTypeOperatorConversion

/-! # Recursive conversion of guarded interfaces

Input transport is contravariant. Output transport lives in the old binder
and is instantiated by an actually typed argument. These certificates retain
whole recursive trees, so the call constructor supports higher-order inputs
and results. Fresh testing constructs each new function ground history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tree_inst tree_comp_id tree_lift_cons tree_comp_assoc
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees
variable [Params] {D : Definitions}

/-- Directed transport of a complete guarded tree under every typed
substitution. New actual assignments are explicit: this certificate is not
actual type equality. Missing for general strong conversion is construction
for every original type child with the profiles its term child requires. -/
def PiInertTreeTransport (D : Definitions) (Δ : List ProofShape)
    (p : PiInertGuardedTree) (T : ProofShape) (q : PiInertGuardedTree) (U : ProofShape) : Prop :=
  ∀ {Λ σ}, ContextSubstitution Δ Λ σ → ∀ {a b},
    PiInertGuardedTreeValue p σ D Λ a b (T.subst σ) →
    TypedAt Λ a (U.subst σ) → TypedAt Λ b (U.subst σ) →
    PiInertGuardedTreeValue q σ D Λ a b (U.subst σ)

/-- Exposure supply for every typed substitution, independently of endpoint
comparisons or variable image requirements. It ensures the chosen input tree
can be used in fresh testing; transport alone need not ensure this. -/
def PiInertTreeSupply (D : Definitions) (Δ : List ProofShape)
    (p : PiInertGuardedTree) (T : ProofShape) : Prop :=
  ∀ {Λ σ}, ContextSubstitution Δ Λ σ → PiInertGuardedTreeSupply p σ D Λ (T.subst σ)

/-- Reifying annotation substitution also preserves recursive exposure
supply, including each dependent result and future world. -/
theorem PiInertGuardedTreeSupply.subst_iff :
    PiInertGuardedTreeSupply (p.subst σ) ρ D Δ T ↔
      PiInertGuardedTreeSupply p (σ.comp ρ) D Δ T := by
  induction p generalizing σ ρ Δ T with
  | plain => rfl
  | both p q ihp ihq =>
    simp only [PiInertGuardedTree.subst, PiInertGuardedTreeSupply, ihp, ihq]
  | call A B p q _ ihq =>
    simp only [PiInertGuardedTree.subst, PiInertGuardedTreeSupply, ihq,
      ProofShape.subst_subst, ← ProofShape.Subst.comp_lift, tree_lift_cons, tree_comp_assoc]

/-- Transport with an unchanged type and profile needs no conversion. -/
theorem PiInertTreeTransport.refl : PiInertTreeTransport D Δ p T p T := by
  intro Λ σ W a b H _ _
  exact H

/-- Transport retains its full quantification after any typed substitution. -/
theorem PiInertTreeTransport.substitute (H : PiInertTreeTransport D Δ p T q U)
    (W : ContextSubstitution Δ Λ σ) :
    PiInertTreeTransport D Λ (p.subst σ) (T.subst σ) (q.subst σ) (U.subst σ) := by
  intro Ξ τ V a b K HA HB
  simp only [PiInertGuardedTreeValue.subst_iff, ProofShape.subst_subst] at K HA HB ⊢
  exact H (W.comp V) K HA HB

/-- A carrier transport constructs the ground-tree case, retaining actual
new assignments. This is not transitivity of comparisons between terms. -/
theorem PiInertTreeTransport.ground (H : PiInertCarrierTransport D Δ T U) :
    PiInertTreeTransport D Δ (.plain .ground) T (.plain .ground) U := by
  intro Λ σ W a b K HA HB
  exact ⟨HA, HB, HA.sources.1, HB.sources.1, HA.sources.2,
    (H W a b).1 K.base.ground.history⟩

/-- An original actual type equality supplies intermediate assignments for
arbitrary target endpoints after a typed substitution. The endpoints need
not themselves be images of terms in the original context. No history or
recursive action is transported by this typing lemma. -/
theorem ProofShape.TypedAt.actual_type_eq_substituted
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ A B (.sort u))
    (W : ContextSubstitution (proofEraseCtx Γ) Λ σ)
    (H : TypedAt Λ a ((proofErase Γ A).subst σ)) :
    TypedAt Λ a ((proofErase Γ B).subst σ) := by
  obtain ⟨Γ', τ, hΓ', EΓ', WT, ES⟩ := W hΓ rfl
  have EA := proofErase_subst_with hΓ' WT HE.hasType.1 ES
  have EB := proofErase_subst_with hΓ' WT HE.hasType.2 ES
  rw [← EΓ', ← EA] at H
  rw [← EΓ', ← EB]
  apply H.actual_type_eq hΓ'
  simpa only [VExpr.subst] using HE.subst henv.orderedStrong WT hΓ'

/-- Recursive type transports compose when the original first type equality
supplies the intermediate actual assignments. Endpoints and their recursive
action are transported twice; no transitivity of term comparisons is used.
The ordinary equality premise cannot simply be dropped from this contract. -/
theorem PiInertTreeTransport.trans_typed
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ A B (.sort u))
    (H : PiInertTreeTransport D (proofEraseCtx Γ) p (proofErase Γ A) q (proofErase Γ B))
    (K : PiInertTreeTransport D (proofEraseCtx Γ) q (proofErase Γ B) r V) :
    PiInertTreeTransport D (proofEraseCtx Γ) p (proofErase Γ A) r V := by
  intro Λ σ W a b X HA HB
  have MA := X.base.left.actual_type_eq_substituted hΓ HE W
  have MB := X.base.right.actual_type_eq_substituted hΓ HE W
  exact K W (H W X MA MB) HA HB

/-- A source universe alias constructs transport from any source tree to
any ordinary target tree. Actual target assignments remain explicit. -/
theorem PiInertTreeTransport.universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : UniverseAlias Δ T) (HQ : q.Ordinary) : PiInertTreeTransport D Δ p T q U := by
  intro Λ σ W a b K HA HB
  have HU := HT.substitute W
  obtain ⟨u, SA⟩ := HU.assigned_sorted K.base.left
  have base : PiInertAssignedBase D Λ a b (U.subst σ) :=
    ⟨HA, HB, HA.sources.1, HB.sources.1, HA.sources.2, by
      obtain ⟨n, H⟩ := K.base.ground.history
      exact ⟨n, H.universe_alias_reindex heq hs HU⟩⟩
  exact base.sorted_tree SA HQ

/-- A finite intersection of target requirements is constructed componentwise. -/
theorem PiInertTreeTransport.both (H : PiInertTreeTransport D Δ p T q U)
    (K : PiInertTreeTransport D Δ p T r U) :
    PiInertTreeTransport D Δ p T (.both q r) U := by
  intro Λ σ W a b V HA HB
  exact ⟨H W V HA HB, K W V HA HB⟩

/-- Ordinary profiles require no exposure, even under arbitrary substitutions. -/
theorem PiInertTreeSupply.ordinary (H : p.Ordinary) : PiInertTreeSupply D Δ p T :=
  fun _ => PiInertGuardedTreeSupply.of_ordinary H

/-- Full computation evidence and recursive result supply construct a call's
type-only supply. The dependent result is instantiated in the old binder. -/
theorem PiInertTreeSupply.call (R : PiInertEvidence D n .compute Δ T (.forallE A B))
    (S : PiInertTreeSupply D (A::Δ) q B) : PiInertTreeSupply D Δ (.call A B p q) T := by
  intro Λ σ W
  refine ⟨⟨n, (R.substitute W).world_computation⟩, ?_⟩
  intro Ξ τ x V HX
  exact S (ContextSubstitution.cons_assigned (W.comp V.typed) HX)

/-- A typed literal Pi supplies its own exposure; only the result tree's
recursive type supply remains. No function action is a premise. -/
theorem PiInertTreeSupply.literal_call
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HT : TypedSource Δ (.forallE A B)) (S : PiInertTreeSupply D (A::Δ) q B) :
    PiInertTreeSupply D Δ (.call A B p q) (.forallE A B) :=
  PiInertTreeSupply.call (PiInertEvidence.core_source (n := 0) hs hc HT .refl) S

/-- Recursive argument/result transports rebuild the whole new function
interface. Result transport is recorded under the old domain, not moved
across a changed binder. Its typed argument instantiation is constructed from
whole-application typing. Fresh testing supplies the new ground history. -/
theorem PiInertGuardedTreeValue.interface_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertGuardedTreeValue (.call A B p q) ProofShape.Subst.id D Δ f g T)
    (HF : TypedAt Δ f (.forallE C E)) (HG : TypedAt Δ g (.forallE C E))
    (input : PiInertTreeTransport D Δ r C p A)
    (output : PiInertTreeTransport D (A::Δ) q B s E)
    (supply : PiInertGuardedTreeSupply r ProofShape.Subst.id D Δ C) :
    PiInertGuardedTreeValue (.call C E r s) ProofShape.Subst.id D Δ f g (.forallE C E) := by
  obtain ⟨n, RT⟩ := H.2.1
  have oldF := H.1.left.world_computation heq hs RT
  have oldG := H.1.right.world_computation heq hs RT
  simp only [ProofShape.subst_id, ProofShape.Subst.id_lift] at oldF oldG
  apply PiInertGuardedTreeValue.of_calls heq hs hc hRigid HF HG supply
  intro Λ σ x y W HX HL HR
  have FL := HF.subst W.typed
  have FR := HG.subst W.typed
  have OL := oldF.subst W.typed
  have OR := oldG.subst W.typed
  simp only [ProofShape.subst] at FL FR OL OR
  obtain ⟨TX, TL⟩ := FL.app_parts HL
  have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HR
  have OX := (OL.app_parts HL).1
  have OY := (OR.app_parts HR).1
  have body := H.2.2 W (input W.typed HX OX OY) HL HR
  rw [tree_inst] at TL TR
  exact output (ContextSubstitution.cons_assigned W.typed OX) body TL TR

/-- The recursive Pi constructor for directed tree transport. Input
conversion reverses direction, result conversion stays under the old binder,
and independent supply makes the new input usable for fresh testing. This
supports nested calls in either argument or result profiles. The source's
selected carrier is unrestricted: its call already retains the old exposure. -/
theorem PiInertTreeTransport.call
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (input : PiInertTreeTransport D Δ r C p A)
    (output : PiInertTreeTransport D (A::Δ) q B s E)
    (supply : PiInertTreeSupply D Δ r C) :
    PiInertTreeTransport D Δ (.call A B p q) T
      (.call C E r s) (.forallE C E) := by
  intro Λ σ W f g H HF HG
  have old : PiInertGuardedTreeValue ((PiInertGuardedTree.call A B p q).subst σ)
      ProofShape.Subst.id D Λ f g (T.subst σ) := by
    simpa only [PiInertGuardedTreeValue.subst_iff, tree_comp_id] using H
  have S : PiInertGuardedTreeSupply (r.subst σ) ProofShape.Subst.id D Λ (C.subst σ) := by
    simpa only [PiInertGuardedTreeSupply.subst_iff, tree_comp_id] using supply W
  have result := old.interface_convert heq hs hc hRigid HF HG
    (PiInertTreeTransport.substitute input W)
    (PiInertTreeTransport.substitute output W.cons) S
  change PiInertGuardedTreeValue ((PiInertGuardedTree.call C E r s).subst σ)
    ProofShape.Subst.id D Λ f g ((ProofShape.forallE C E).subst σ) at result
  simpa only [PiInertGuardedTreeValue.subst_iff, tree_comp_id] using result

/-- A retained full computation from a new selected alias to the converted
carrier preserves the complete resulting call. The target need not itself
be a literal Pi, and the prefix does not erase its recursive action. -/
theorem PiInertTreeTransport.target_call_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertTreeTransport D Δ p T (.call A B r s) U)
    (R : PiInertEvidence D n .compute Δ V U) :
    PiInertTreeTransport D Δ p T (.call A B r s) V := by
  intro Λ σ W a b X HA HB
  have path := (R.substitute W).world_computation
  have result := H W X (HA.world_computation heq hs path) (HB.world_computation heq hs path)
  exact result.call_prefix HA HB path

/-- Paired interpretation consumes independently retained recursive
transports in its two environments. Cross assignments come from actual
reflection of the original assigned ground comparison. -/
theorem PiInertGuardedPairInterpretation.convert_trees
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertGuardedPairInterpretation D Δ uses f g T U p q)
    (LT : PiInertTreeTransport D Δ p T r V) (RT : PiInertTreeTransport D Δ q U s E)
    (HF : TypedAt Δ f V) (HG : TypedAt Δ g E) :
    PiInertGuardedPairInterpretation D Δ uses f g V E r s := by
  refine ⟨HF, HG, ?_⟩
  intro Λ σ τ WL WR images
  have old := H.run WL WR images
  have FL := HF.subst WL
  have GR := HG.subst WR
  have GL := old.forward.base.transfer heq hs FL
  have FR := old.backward.base.transfer heq hs GR
  exact ⟨LT WL old.forward FL GL, RT WR old.backward GR FR⟩

/-- Original strong conversion consumes full recursive interface transport
instead of dropping the term child to ground. The original children derive
the target assignments. General construction of both transports from an
arbitrary type child is the remaining coverage obligation. -/
theorem StrongBounded.paired_convert_interfaces
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A B (.sort u))
    (termChild : StrongBounded env univs k Γ f g A)
    (LT : PiInertTreeTransport D (proofEraseCtx Γ) p (proofErase Γ A) r (proofErase Γ B))
    (RT : PiInertTreeTransport D (proofEraseCtx Γ) q (proofErase Γ A) s (proofErase Γ B))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A) (proofErase Γ A) p q) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ B) (proofErase Γ B) r s := by
  have HE := typeChild.strong.defeq
  have HF := termChild.strong.defeq
  exact H.convert_trees heq hs LT RT
    (.of_typed hΓ (HE.defeq HF.hasType.1)) (.of_typed hΓ (HE.defeq HF.hasType.2))

/-- The original Pi-congruence children construct recursive interface
transport from their domain and codomain certificates. Ordinary context
conversion identifies the target codomain's erasure in the two binders; the
history transport itself stays under the source binder. This discharges the
dependent binder mismatch without assuming history context conversion. -/
theorem StrongBounded.forall_interface_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (domainChild : StrongBounded env univs k Γ A C (.sort u))
    (bodyChild : StrongBounded env univs k (A::Γ) B E (.sort v))
    (input : PiInertTreeTransport D (proofEraseCtx Γ) r (proofErase Γ C) p (proofErase Γ A))
    (output : PiInertTreeTransport D (proofEraseCtx (A::Γ))
      q (proofErase (A::Γ) B) s (proofErase (A::Γ) E))
    (supply : PiInertTreeSupply D (proofEraseCtx Γ) r (proofErase Γ C)) :
    PiInertTreeTransport D (proofEraseCtx Γ)
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p q) (proofErase Γ (.forallE A B))
      (.call (proofErase Γ C) (proofErase (C::Γ) E) r s) (proofErase Γ (.forallE C E)) := by
  have HD := domainChild.strong.defeq
  have HB := bodyChild.strong.defeq
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, HD.hasType.1⟩
  have W : IsDefEqCtx env univs Γ (A::Γ) (C::Γ) := .succ .zero HD
  have EE := proofErase_defeqCtx hΓA W HB.hasType.2
  have hOld := HasType.forallE HD.hasType.1 HB.hasType.1
  have hNew := HasType.forallE HD.hasType.2 (HB.hasType.2.defeqDFC henv W)
  have EOld : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hOld)
  have ENew : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) :=
    if_neg (not_isProof_of_sort hΓ hNew)
  rw [EOld, ENew, ← EE]
  intro Λ σ V f g H HF HG
  exact PiInertTreeTransport.call heq hs hc hRigid input output supply V H HF HG

/-- A higher-order operator converts its function-valued input recursively.
All transports and fresh-input supply are constructed from actual universe
aliases and the target input type's source witness. No function-transport
certificate is an assumption; target operand assignments remain part of the
transport contract. The source and target inner interfaces may differ. -/
theorem PiInertTreeTransport.higher_order_type_operator
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HA : UniverseAlias Δ A) (HE : UniverseAlias (C::Δ) E)
    (HF : UniverseAlias (ProofShape.forallE A B :: Δ) F)
    (HT : TypedSource Δ (.forallE C E)) :
    PiInertTreeTransport D Δ
      (.call (.forallE A B) F (.call A B (.plain .ground) (.plain .ground)) (.plain .ground))
      (.forallE (.forallE A B) F)
      (.call (.forallE C E) G (.call C E (.plain .ground) (.plain .ground)) (.plain .ground))
      (.forallE (.forallE C E) G) := by
  have input : PiInertTreeTransport D Δ
      (.call C E (.plain .ground) (.plain .ground)) (.forallE C E)
      (.call A B (.plain .ground) (.plain .ground)) (.forallE A B) := by
    apply PiInertTreeTransport.call heq hs hc hRigid
    · exact PiInertTreeTransport.universe (q := .plain .ground) heq hs HA trivial
    · exact PiInertTreeTransport.universe (q := .plain .ground) heq hs HE trivial
    · exact PiInertTreeSupply.ordinary (p := .plain .ground) trivial
  apply PiInertTreeTransport.call heq hs hc hRigid input
  · exact PiInertTreeTransport.universe (q := .plain .ground) heq hs HF trivial
  · exact PiInertTreeSupply.literal_call hs hc HT (PiInertTreeSupply.ordinary (p := .plain .ground) trivial)

/-- Recursive conversion also rebuilds a function-valued result. Each
codomain certificate is kept under its own old binder. This tests covariance
through two dependent binders rather than flattening the result to ground. -/
theorem PiInertTreeTransport.curried_type_operator
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HC : UniverseAlias Δ C) (HE : UniverseAlias (A::Δ) E)
    (HF : UniverseAlias (B::A::Δ) F) :
    PiInertTreeTransport D Δ
      (.call A (.forallE B F) (.plain .ground) (.call B F (.plain .ground) (.plain .ground)))
      (.forallE A (.forallE B F))
      (.call C (.forallE E G) (.plain .ground) (.call E G (.plain .ground) (.plain .ground)))
      (.forallE C (.forallE E G)) := by
  apply PiInertTreeTransport.call heq hs hc hRigid
  · exact PiInertTreeTransport.universe (q := .plain .ground) heq hs HC trivial
  · apply PiInertTreeTransport.call heq hs hc hRigid
    · exact PiInertTreeTransport.universe (q := .plain .ground) heq hs HE trivial
    · exact PiInertTreeTransport.universe (q := .plain .ground) heq hs HF trivial
    · exact PiInertTreeSupply.ordinary (p := .plain .ground) trivial
  · exact PiInertTreeSupply.ordinary (p := .plain .ground) trivial

end Lean4Lean.VEnv.Strengthening
