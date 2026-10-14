import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefixDescent

/-! # Weakening of raw guarded singleton computation

The guard renames even without occurrence typing. This permits the new rule
inside type recovery and compatible eta under arbitrary inserted binders.
-/
namespace Lean4Lean.PropElim
open VExpr VEnv SingletonLayout
variable {S : SingletonLayout} {P ps idx : List VExpr} {E : PropElim}

/-- The transported field program has its declared length for raw providers. -/
theorem transportedFields_length_raw (H : S.Scoped P.length)
    (hps : ps.length = P.length) (hidx : idx.length = S.indices.length) :
    (transportedFields S P E ps idx m i).length = i := by
  have hw : ∀ j, (transportedWitnesses S P E ps idx m j).length = j := by
    intro j; induction j with
    | zero => rfl
    | succ j ih => simp [transportedWitnesses, ih]
  unfold transportedFields
  rw [← tel_instOuter (H.mono_pa hps) hidx i _ (hw i)]
  simp only [List.length_map, (S.tel_length ps idx i).2]

/-- Family naturality needs only provider lengths, not an occurrence typing. -/
theorem transportedFamily_subst_raw (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S P env U) (hps : ps.length = P.length)
    (hidx : idx.length = S.indices.length) (τ : Subst) :
    (transportedFamily S P E ps idx m).subst τ =
      transportedFamily S P E (ps.map (·.subst τ)) (idx.map (·.subst τ)) (m.subst τ) := by
  have hctx : OnCtx (P ++ S.fields).reverse (env.IsType U) := by
    simpa using W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  have hc := (branchFamily_prop henv W).closedN henv.ordered (CtxWF.closed henv.ordered hctx)
  have hl := transportedFields_length_raw (E := E) (m := m) (i := S.fields.length) W.typed.scope hps hidx
  unfold transportedFamily
  rw [instOuter_subst_closed _ _ (by simpa only [List.length_reverse, List.length_append, hps, hl] using hc),
    List.map_append, transportedFields_subst henv heq W hps hidx (Nat.le_refl _) τ]

/-- Raw family providers commute with any binder insertion. -/
theorem transportedFamily_lift_raw (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S P env U) (hps : ps.length = P.length)
    (hidx : idx.length = S.indices.length) (ρ : Lift) :
    (transportedFamily S P E ps idx m).lift' ρ =
      transportedFamily S P E (ps.map (·.lift' ρ)) (idx.map (·.lift' ρ)) (m.lift' ρ) := by
  simpa only [← InductiveSignature.RecursorData.lift'_eq_subst] using
    transportedFamily_subst_raw henv heq W hps hidx (Subst.lift_r .id ρ)

end Lean4Lean.PropElim

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

omit [Params] in
/-- Finite insertion closure extends to every context-lift map. -/
theorem ComputeWeakening.lift' (hw : ComputeWeakening C)
    (W : Ctx.Lift' ρ Γ Γ') (R : C Γ e out) : C Γ' (e.lift' ρ) (out.lift' ρ) := by
  generalize he : ρ.depth = n
  induction n generalizing ρ Γ' with
  | zero => simpa [lift'_depth_zero he, W.depth_zero he] using R
  | succ n ih =>
    obtain ⟨ρ, k, rfl, rfl⟩ := Lift.depth_succ he
    obtain ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, lift'_comp, lift'_comp, ← Lift.skipN_one,
      lift'_consN_skipN, lift'_consN_skipN]
    exact hw W2 (ih W1 Lift.depth_consN)

namespace GuardedSingleton
open InductiveSignature PropElim
variable {S : SingletonLayout} {E : PropElim}

/-- A generated family guard weakens without requiring source typing. -/
theorem FamilyGuard.weak' (heq : env.HasCanonicalEq) (hcmp : ComputeWeakening Cmp)
    (hW : Ctx.Lift' ρ Γ Γ') (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HG : FamilyGuard Cmp Γ data levels args program S E) :
    FamilyGuard Cmp Γ' data levels (args.map (·.lift' ρ)) (program.rename ρ) S E := by
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hio, _, _⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  have hp := (RecursorData.singletonLayout_lengths hS).2
  have hi := (RecursorData.singletonLayout_lengths hS).1
  obtain ⟨_, hps, _, hidx⟩ := openedArguments_split (by simpa only [hp] using hio)
    (RecursorData.singletonUnfolding_spec hg).1
  have hps := hps.trans hp.symm
  have hidx := hidx.trans hi.symm
  have hlenD : program.domains.length = data.majorOffset + 1 - args.length := by
    obtain ⟨_, _, _, _, hh, _⟩ := RecursorData.singletonUnfolding_layout hg
    exact hh
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr
    (RecursorData.singletonUnfolding_spec hg).2.1
  have hmajor : (VExpr.bvar 0).lift' (ρ.consN program.domains.length) = .bvar 0 := by
    cases hn : program.domains.length with
    | zero => omega
    | succ n => rfl
  have hf := transportedFamily_lift_raw (m := .bvar 0) henv heq W hps hidx (ρ.consN program.domains.length)
  rw [hmajor] at hf
  have HG' := hcmp.lift' (RecursorData.renameDomains_context program.domains hW) HG
  unfold FamilyGuard at HG' ⊢
  simp only [openedArguments_lift', ← hlenD, ← List.map_take, ← List.map_drop]
  simpa only [hf, lift'_mkApps, W.family_closed.lift'_eq .zero, List.map_append,
    RecursorData.PrefixUnfolding.rename] using HG'

/-- The complete raw indexed prefix rule preserves arbitrary context lifting. -/
theorem PrefixStep.weak' (heq : env.HasCanonicalEq) (hcmp : ComputeWeakening Cmp)
    (hW : Ctx.Lift' ρ Γ Γ') (R : PrefixStep Cmp Γ e out) :
    PrefixStep Cmp Γ' (e.lift' ρ) (out.lift' ρ) := by
  cases R with
  | intro H hl hz hw hn ho hS hE hg HG =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrt, _⟩ :=
      RecursorData.singleton_equation_syntax H hl hz hn ho hS hE
    have hg' := RecursorData.singletonUnfolding_lift' henv H hl hz hrt
      (H.recursorType_closed henv hrt) hg (ρ := ρ)
    have HG' := HG.weak' heq hcmp hW H hl hz hw hn ho hS hE hg
    have R' := PrefixStep.intro H hl hz hw hn ho hS hE hg' HG'
    rw [RecursorData.PrefixUnfolding.rename_rhs
      (ClosedSingleton.generated_template_closed henv H hl hz hg)] at R'
    simpa only [lift'_mkApps, lift'] using R'

/-- Indexed prefix computation can occur beneath arbitrary fresh binders. -/
theorem PrefixStep.computeWeakening (heq : env.HasCanonicalEq) (hcmp : ComputeWeakening Cmp) :
    ComputeWeakening (PrefixStep Cmp) := by
  intro n k Γ Γ' e out W R
  simpa only [lift'_consN_skipN] using R.weak' heq hcmp (Ctx.liftN_iff_lift'.1 W)

/-- Enlarging the endpoint certificate relation preserves the exact program. -/
theorem PrefixStep.map_guards (hcmp : ∀ {Γ a b}, Cmp Γ a b → Cmp' Γ a b)
    (R : PrefixStep Cmp Γ e out) : PrefixStep Cmp' Γ e out := by
  cases R with
  | intro H hl hz hw hn ho hS hE hg HG => exact .intro H hl hz hw hn ho hS hE hg (hcmp HG)

end GuardedSingleton
end Lean4Lean.VEnv.Strengthening
