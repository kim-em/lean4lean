import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidDemandTransport
import Lean4Lean.Theory.Typing.Strengthening.StructureFamilyArity

/-! # Rigid family readout after arbitrary enriched computation

Finite dependent observations preserve the family name and number of arguments.
Universe instances and arguments may change. Beta cleanup exposes the resulting
literal constant spine without any argument recovery assumption.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open DemandProfile
open PureObservation (Ob)
variable [Params] {c : Name} {arity : Nat} {P : ProofShape → Prop}

/-- Dependent typing decorations do not constrain operational substitution:
supplying the free demands suffices for every raw realizing substitution. -/
theorem Obs.realizes (H : Obs c arity Δ S e t o)
    (hP : ∀ {e e'}, ProofShape.BetaRed e e' → P e' → P e)
    (hconst : ∀ ls, Realizes P (.const c ls) (spineDemand arity))
    (hσ : ∀ i t key, S i t key → Realizes P (σ i) key) :
    Realizes P (e.subst σ) o := by
  induction H generalizing σ with
  | const => exact hconst _
  | var _ _ h => exact hσ _ _ _ h
  | app _ _ _ ihf ihx =>
    have HF := ihf hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => ihx key hk hσ)
  | @lam Δ D b A B keys S o HT HK HB ih =>
    simp only [Realizes]
    intro a ha
    have H := ih (σ := σ.cons a) (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one,
          ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Realizes.beta_back hP (E ▸ (ProofShape.BetaRed.beta (A := D.subst σ))) H

/-- The operational result retains the constant head and exact spine length,
while permitting arbitrary argument expressions at the exposed endpoint. -/
def HeadResult (c : Name) (n : Nat) (e : ProofShape) : Prop :=
  ∃ ls args, args.length = n ∧ ProofShape.BetaRed e (ProofShape.mkApps (.const c ls) args)

omit [Params] in
/-- Completing the remaining applications realizes a head demand. -/
theorem head_spine_realizes (h : args.length + k = n) :
    Realizes (HeadResult c n) (ProofShape.mkApps (.const c ls) args) (spineDemand k) := by
  induction k generalizing args with
  | zero =>
    simp only [spineDemand, Realizes, HeadResult]
    exact ⟨ls, args, by simpa using h, .refl⟩
  | succ k ih =>
    simp only [spineDemand, Realizes]
    intro a _
    have R := ih (args := args ++ [a]) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    simpa only [ProofShape.mkApps_snoc] using R

/-- With no free demanded variables, the designated constant is the only
possible exposed head. Universe instances and argument syntax stay unrestricted. -/
theorem Obs.head_readout (H : Obs c arity Δ (fun _ _ _ => False) e t .pi) :
    HeadResult c arity e := by
  have HR := H.realizes (P := HeadResult c arity) (σ := ProofShape.Subst.id)
    (fun R H => by obtain ⟨ls, args, hn, RB⟩ := H; exact ⟨ls, args, hn, R.trans RB⟩)
    (fun ls => head_spine_realizes (args := []) (by simp))
    (fun _ _ _ h => h.elim)
  simpa only [ProofShape.subst_id, Realizes] using HR

/-- Applying a typed telescope discharges the ignored demands one by one.
Only ordinary argument typing is used, including at proof and data parameters. -/
theorem Obs.telescope (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f T)
    (HP : Fits Γ T (spineProfile args.length))
    (HW : InstForallsC env univs Γ T args result)
    (H : Obs c arity (proofEraseCtx Γ) S (proofErase Γ f)
      (spineProfile args.length) (spineDemand args.length)) :
    Obs c arity (proofEraseCtx Γ) S (proofErase Γ (VExpr.mkApps f args)) .sort .pi := by
  induction HW generalizing f with
  | nil => exact H
  | @cons a A args result B ha HW ih =>
    obtain ⟨HA, HB⟩ := HP.forallE_inv hΓ
    obtain ⟨u, hA⟩ := HA.isType
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA ha
    have HPI : Fits Γ (B.inst a) (spineProfile args.length) := by
      simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
    have hfa := HasType.app hf ha
    have E : proofErase Γ (.app f a) = .app (proofErase Γ f) (proofErase Γ a) :=
      if_neg (HPI.not_isProof hΓ (spineDemand_valid args.length).visible hfa)
    have HT : Typing (proofEraseCtx Γ) (.app (proofErase Γ f) (proofErase Γ a))
        (spineProfile args.length) := ⟨Γ, _, _, hΓ, rfl, hfa, HPI, E⟩
    have HO : Obs c arity (proofEraseCtx Γ) S (proofErase Γ (.app f a))
        (spineProfile args.length) (spineDemand args.length) := by
      rw [E]
      exact .app (keys := []) HT H (by simp)
    exact ih hfa HPI HO

/-- A saturated rigid type family retains its name and exact arity through
full structure/function-eta computation. The explicit non-unfolding condition
excludes selecting an arbitrary sound delta equation for the rigid head. -/
theorem static_structure_rigid_telescope_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.const c ls) T)
    (HT : SortTelescope args.length T)
    (HW : InstForallsC env univs Γ T args result)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const c ls) args)) out) :
    ∃ ls' args', args'.length = args.length ∧ BetaRed out (ProofShape.mkApps (.const c ls') args') := by
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  have HP := Fits.of_sortTelescope hΓ hT HT
  have E : proofErase Γ (.const c ls) = .const c ls :=
    if_neg (HP.not_isProof hΓ (spineDemand_valid args.length).visible hf)
  have H : Obs c args.length (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ (.const c ls))
      (spineProfile args.length) (spineDemand args.length) := by
    rw [E]
    exact .const ⟨Γ, _, _, hΓ, rfl, hf, HP, E⟩
  exact ((H.telescope hΓ hf HP HW).static_structure_union heq hs hc hD R
    (fun _ _ _ h => h.elim)).head_readout

omit [Params] in
/-- A normalized telescope ending in a universe has the required head profile. -/
theorem sortTelescope_wrapForalls (doms : List VExpr) (u : VLevel) :
    SortTelescope doms.length (VExpr.wrapForalls doms (.sort u)) := by
  induction doms with
  | nil => exact .sort
  | cons A doms ih => exact .forallE ih

/-- A registered structure family supplies its normalized telescope from the
environment. Full computation exposes the same family and its exact parameter
and index count, without assuming a literal normalized stored declaration. -/
theorem static_structure_registered_family_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) args) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const family ls) args)) out) :
    ∃ ls' args', args'.length = info.nparams + info.nindices ∧
      BetaRed out (ProofShape.mkApps (.const family ls') args') := by
  obtain ⟨doms, w, hlen, hf⟩ := StructureReplay.family_head_telescope henv hΓ hi ⟨u, hS⟩
  have hargs := StructureReplay.family_arity henv hΓ hi ⟨u, hS⟩
  have EL : args.length = doms.length := hargs.trans hlen.symm
  obtain ⟨result, HW, _⟩ := HasType.mkApps_telescope henv hΓ (hf hΓ) ⟨_, hS⟩
    (EL ▸ VExpr.takeForalls_wrapForalls doms (.sort w))
  obtain ⟨ls', args', hn, RB⟩ := static_structure_rigid_telescope_head_readout heq hs
    (henv.projectionRigid hi) hD hΓ (hf hΓ) (EL.symm ▸ sortTelescope_wrapForalls doms w) HW R
  exact ⟨ls', args', hn.trans hargs, RB⟩

end Lean4Lean.VEnv.Strengthening.RigidDemandProfile
