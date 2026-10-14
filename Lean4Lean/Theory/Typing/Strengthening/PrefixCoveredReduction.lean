import Lean4Lean.Theory.Typing.Strengthening.ProofIndexHeadComputation
import Lean4Lean.Theory.Typing.Strengthening.FullHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.FamilyHeadRepair

/-! # Full paths with explicit singleton-prefix coverage

The relation retains every ordinary full-step rule and requires a declaration
certificate only at singleton-prefix nodes. Coverage is a property of a finite
derivation, not a global restriction on the environment. In particular, canonical
Eq may retain data-index instances outside the covered path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
variable [Params]

/-- A local registry instance whose indices form a dependent proposition
telescope. No occurrence-specific equality check is part of this certificate. -/
def ProofIndexPrefix (name : Name) (levels : List VLevel) : Prop :=
  ∃ data S, recursorData name = some data ∧
    data.singletonLayout env levels = some S ∧
    PropTelescope env univs (data.propParams levels).reverse S.indices

/-- Full reduction with an explicit prefix-coverage certificate at each delta
node. Its other constructors are the ordinary full reduction rules. -/
inductive PrefixCoveredStep (P : Name → List VLevel → Prop) :
    List VExpr → VExpr → VExpr → Prop where
  | core : ParRed Γ e out → PrefixCoveredStep P Γ e out
  | delta : P name levels → PrefixUnfold env univs recursorData Γ name levels args rhs →
      PrefixCoveredStep P Γ (mkApps (.const name levels) args) rhs
  | quotDelta : QuotPrefixUnfold env univs Γ levels args rhs →
      PrefixCoveredStep P Γ (mkApps (.const ``Quot.lift levels) args) rhs
  | projIota : env.projections s info →
      HasType env univs Γ (.proj s i (mkApps (.const info.ctorName ls) args)) T →
      args[info.nparams + i]? = some field → HasType env univs Γ field T →
      PrefixCoveredStep P Γ (.proj s i (mkApps (.const info.ctorName ls) args)) field
  | structEta : env.projections s info → ps.length = info.nparams → info.nindices = 0 →
      HasType env univs Γ e (mkApps (.const s ls) ps) →
      HasType env univs Γ (structExpand s info ls ps e) (mkApps (.const s ls) ps) →
      PrefixCoveredStep P Γ e (structExpand s info ls ps e)
  | funEta : HasType env univs Γ e (.forallE A B) →
      PrefixCoveredStep P Γ e (.lam A (.app e.lift (.bvar 0)))
  | app : PrefixCoveredStep P Γ f f' → PrefixCoveredStep P Γ a a' →
      PrefixCoveredStep P Γ (.app f a) (.app f' a')
  | proj : PrefixCoveredStep P Γ m m' → PrefixCoveredStep P Γ (.proj s i m) (.proj s i m')
  | lam : PrefixCoveredStep P Γ A A' → PrefixCoveredStep P (A :: Γ) b b' →
      PrefixCoveredStep P Γ (.lam A b) (.lam A' b')
  | forallE : PrefixCoveredStep P Γ A A' → PrefixCoveredStep P (A :: Γ) B B' →
      PrefixCoveredStep P Γ (.forallE A B) (.forallE A' B')

/-- Finite paths retain their local singleton-prefix evidence. -/
abbrev PrefixCoveredReduction (P : Name → List VLevel → Prop) (Γ : List VExpr) :=
  ReflTransGen (PrefixCoveredStep P Γ)

/-- Forgetting coverage yields an actual full step, not a new equality rule. -/
theorem PrefixCoveredStep.full (R : PrefixCoveredStep P Γ e out) : FullStep Γ e out := by
  induction R with
  | core R => exact .core R
  | delta _ R => exact .delta R
  | quotDelta R => exact .quotDelta R
  | projIota hi ht hg hf => exact .projIota hi ht hg hf
  | structEta hi hp hz hm he => exact .structEta hi hp hz hm he
  | funEta ht => exact .funEta ht
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

/-- Forgetting all local certificates yields the original full path. -/
theorem PrefixCoveredReduction.full (R : PrefixCoveredReduction P Γ e out) :
    FullReduction Γ e out := by
  induction R with
  | rfl => exact .rfl
  | tail _ R ih => exact ih.tail R.full

end Lean4Lean.VEnv.Strengthening

namespace Lean4Lean.VEnv.Strengthening.ProofIndexFullHead
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions PatternCompute)
open ConstructorObservation (EtaCompute ConstructorRigid)
variable {env : VEnv}

/-- Add proof-index equations to the previous complete closed collection. -/
noncomputable def definitions (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) : Definitions :=
  @ProofIndexedSingleton.definitions (henv.params U) heq (FullHead.definitions henv heq U)

/-- Closed equation soundness is inherited from the two checked collections. -/
theorem sound (henv : env.WF) (heq : env.HasCanonicalEq) :
    (definitions henv heq U).Sound env U :=
  @ProofIndexedSingleton.definitions_sound (henv.params U) _ heq (FullHead.sound henv heq)

/-- Family and constructor observations stay valid after adjoining the equations. -/
theorem rigid (henv : env.WF) (heq : env.HasCanonicalEq) :
    @ConstructorRigid (henv.params U) (definitions henv heq U) :=
  @ProofIndexedSingleton.definitions_rigid (henv.params U) _ heq (FullHead.rigid henv heq)

/-- Every covered step embeds, including prefix nodes under arbitrary syntax
and both eta forms. Only source well-formedness is used for intermediate typing. -/
theorem step (henv : env.WF) (heq : env.HasCanonicalEq)
    (R : @PrefixCoveredStep (henv.params U) (@ProofIndexPrefix (henv.params U)) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : VExpr.WF env U Γ e) :
    @EtaCompute (henv.params U) (definitions henv heq U) e out := by
  letI := henv.params U
  induction R with
  | core R => exact (FullHead.core henv heq R hΓ ht).of_inclusion (fun _ _ _ h => .inl h)
  | delta hP R =>
    obtain ⟨data, S, hl, hS, hidx⟩ := hP
    exact .compute (.base (ProofIndexedSingleton.prefix_compute heq hl hS hidx R))
  | quotDelta R => exact (FullHead.quotient henv heq R).of_inclusion (fun _ _ _ h => .inl h)
  | projIota hi hs hg _ =>
    obtain ⟨info', _, _, _, _, _, _, hi', _, _, _, _, _, _, hm, _, _⟩ := HasType.proj_inv henv hΓ hs
    obtain rfl := henv.ordered.projections_unique hi hi'
    have ha := (projection_major_family henv hΓ hi (henv.projectionRigid hi) hm.hasType.2).2
    exact .compute (.projIota hi ha hg)
  | structEta hi hp hz hm he =>
    exact .structEta hi hz ((StructureReplay.expansion_typed_iff henv hΓ hi hp hz hm).1 he) hp
  | funEta => exact .funEta
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ ⟨_, hf⟩) (iha hΓ ⟨_, ha⟩)
  | proj _ ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := HasType.proj_inv henv hΓ ht
    exact .proj (ih hΓ ⟨_, hm.hasType.2⟩)
  | lam _ _ ihA ihb =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩)) (ihb ⟨hΓ, hA⟩ hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨hA, hB⟩ := HasType.forallE_inv henv.ordered ht
    exact .forallE (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩))
      (ihB ⟨hΓ, hA⟩ (hB.elim fun _ h => ⟨_, h⟩))

/-- Whole covered paths embed with no assumptions on eta annotation scope. -/
theorem reduction (henv : env.WF) (heq : env.HasCanonicalEq)
    (R : @PrefixCoveredReduction (henv.params U) (@ProofIndexPrefix (henv.params U)) Γ e out)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : env.HasType U Γ e T) :
    @EtaCompute (henv.params U) (definitions henv heq U) e out := by
  letI := henv.params U
  induction R with
  | rfl => exact .compute (.base .refl)
  | tail R S ih =>
    exact ih.trans (step henv heq S hΓ ⟨_,
      FullReduction.hasType hΓ (PrefixCoveredReduction.full R) ht⟩)

/-- Pi exposure along a covered full path can be repaired by eta-free pattern
computation. The new domain and body need not equal the original annotations. -/
theorem pi_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : env.HasType U Γ e T)
    (R : @PrefixCoveredReduction (henv.params U) (@ProofIndexPrefix (henv.params U))
      Γ e (.forallE A B)) :
    ∃ A' B', @PatternCompute (henv.params U) (definitions henv heq U) e (.forallE A' B') := by
  letI := henv.params U
  exact (reduction henv heq R hΓ ht).pi_exposure (rigid henv heq)

/-- A registered family exposed by a covered full path can be recovered with
the same levels and arity, while replacing arguments containing eta annotations. -/
theorem family_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hi : env.projections s info)
    (hΓ : OnCtx Γ (env.IsType U)) (ht : env.HasType U Γ e T)
    (R : @PrefixCoveredReduction (henv.params U) (@ProofIndexPrefix (henv.params U))
      Γ e (mkApps (.const s ls) args)) :
    ∃ args', @PatternCompute (henv.params U) (definitions henv heq U) e (mkApps (.const s ls) args') ∧
      args'.length = args.length := by
  letI := henv.params U
  exact (reduction henv heq R hΓ ht).family_exposure (rigid henv heq) hi

/-- Covered exposure of a lifted inferred type reconstructs a Pi typing below
the inserted context, even when the full path itself does not descend. -/
theorem function_type_below (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hf : env.HasType U Γ f T)
    (R : @PrefixCoveredReduction (henv.params U) (@ProofIndexPrefix (henv.params U))
      Γ' (T.liftN n k) (.forallE A B)) :
    ∃ A' B', env.HasType U Γ f (.forallE A' B') ∧
      env.IsDefEqU U Γ T (.forallE A' B') := by
  letI := henv.params U
  obtain ⟨_, hT⟩ := hf.isType henv.ordered hΓ
  have H := reduction henv heq R hΓ' (hT.weakN henv.ordered W)
  rw [← lift'_consN_skipN] at H
  exact H.function_type_below (rigid henv heq) (sound henv heq) hΓ hf

/-- Covered family exposure of a lifted inferred major type reconstructs a
usable field below. Successful field selection follows from source typing. -/
theorem projection_type_below (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : Ctx.LiftN n k Γ Γ') (hi : env.projections s info)
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (ht : VExpr.WF env U Γ (.proj s i m)) (hm : env.HasType U Γ m T)
    (R : @PrefixCoveredReduction (henv.params U) (@ProofIndexPrefix (henv.params U))
      Γ' (T.liftN n k) (mkApps (.const s ls) args)) :
    ∃ args' F, @PatternCompute (henv.params U) (definitions henv heq U) T
      (mkApps (.const s ls) args') ∧
      info.fieldType s ls (args'.take info.nparams) i m = some F ∧
      env.HasType U Γ (.proj s i m) F := by
  letI := henv.params U
  obtain ⟨_, hT⟩ := hm.isType henv.ordered hΓ
  have H := reduction henv heq R hΓ' (hT.weakN henv.ordered W)
  rw [← lift'_consN_skipN] at H
  exact H.projection_type_below (rigid henv heq) (sound henv heq) hi hΓ ht hm

end Lean4Lean.VEnv.Strengthening.ProofIndexFullHead
