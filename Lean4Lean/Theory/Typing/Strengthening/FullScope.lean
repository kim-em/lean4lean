import Lean4Lean.Theory.Typing.Strengthening.GeneratedScope
import Lean4Lean.Theory.Typing.Strengthening.DescentSupport

/-! # Exact scope conditions on full-reduction eta annotations

Core computation and generated prefix syntax preserve unused binders. Function eta
can add a domain and structure eta can add parameters; these are the only new
scope conditions in a full step. This file concerns syntax only: scoped targets
and annotations do not supply smaller-context typings or replay checks.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

omit [Params] in
private theorem skips_proj_iff {e : VExpr} {S : Name} :
    (VExpr.proj S i e).Skips n k ↔ e.Skips n k := by
  simp only [skips_iff, Skips']

omit [Params] in
/-- Scope of a constant/application spine is exactly scope of all its components. -/
theorem skips_mkApps_iff : (mkApps f args).Skips n k ↔
    f.Skips n k ∧ ∀ a ∈ args, a.Skips n k := by
  induction args generalizing f with
  | nil => simp [mkApps]
  | cons a args ih =>
    change (mkApps (.app f a) args).Skips n k ↔ _
    rw [ih]
    simp only [skips_iff, Skips', List.mem_cons, forall_eq_or_imp, and_assoc]

/-- Core parallel reduction preserves scope without lowering the rule's checks or
requiring a typing for the source below. -/
theorem parRed_scope (H : ParRed Γ e out) (hs : e.Skips n k) : out.Skips n k := by
  induction H generalizing k with
  | bvar | sort | const => exact hs
  | app _ _ ihf iha =>
    simp only [skips_iff, Skips'] at hs ⊢
    exact ⟨(skips_iff.1 (ihf (skips_iff.2 hs.1))), (skips_iff.1 (iha (skips_iff.2 hs.2)))⟩
  | proj _ ih =>
    exact skips_proj_iff.2 (ih (skips_proj_iff.1 hs))
  | lam _ _ ihd ihb | forallE _ _ ihd ihb =>
    simp only [skips_iff, Skips'] at hs ⊢
    exact ⟨skips_iff.1 (ihd (skips_iff.2 hs.1)), skips_iff.1 (ihb (skips_iff.2 hs.2))⟩
  | beta _ _ ihb iha =>
    simp only [skips_iff, Skips'] at hs
    obtain ⟨b, hb⟩ := skips_iff_exists.1 (ihb (skips_iff.2 hs.1.2))
    obtain ⟨a, ha⟩ := skips_iff_exists.1 (iha (skips_iff.2 hs.2))
    rw [hb, ha, ← liftN_inst_hi]
    exact .liftN
  | @extra Γ p r e m1 m2 m2' hp hm hcheck hargs ih =>
    obtain ⟨source, hsource⟩ := skips_iff_exists.1 hs
    rw [hsource, ← lift'_consN_skipN] at hm
    obtain ⟨captures, _, hcaptures⟩ := Pattern.matches_lift'.1 hm
    have hcap : ∀ a, (m2' a).Skips n k := by
      intro a
      apply ih a
      rw [hcaptures a, lift'_consN_skipN]
      exact .liftN
    have heq : m2' = fun a => ((m2' a).unliftN n k).lift' ((Lift.refl.skipN n).consN k) := by
      funext a
      simpa only [lift'_consN_skipN] using (hcap a).symm
    rw [heq, ← Pattern.RHS.lift'_apply, lift'_consN_skipN]
    exact .liftN

/-- The full presentation with explicit scope checks on the annotations introduced
by eta. All declaration and typing premises remain in the ambient context. -/
inductive ScopedFullStep (n : Nat) : Nat → List VExpr → VExpr → VExpr → Prop where
  | core : ParRed Γ a b → ScopedFullStep n k Γ a b
  | delta : PrefixUnfold env univs recursorData Γ name levels args rhs →
      ScopedFullStep n k Γ (mkApps (.const name levels) args) rhs
  | quotDelta : QuotPrefixUnfold env univs Γ levels args rhs →
      ScopedFullStep n k Γ (mkApps (.const ``Quot.lift levels) args) rhs
  | projIota : env.projections family info →
      HasType env univs Γ (.proj family index (mkApps (.const info.ctorName levels) args)) T →
      args[info.nparams + index]? = some field → HasType env univs Γ field T →
      ScopedFullStep n k Γ (.proj family index (mkApps (.const info.ctorName levels) args)) field
  | structEta : env.projections family info → params.length = info.nparams → info.nindices = 0 →
      HasType env univs Γ e (mkApps (.const family levels) params) →
      HasType env univs Γ
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index e))
        (mkApps (.const family levels) params) →
      (∀ p ∈ params, p.Skips n k) →
      ScopedFullStep n k Γ e
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index e))
  | funEta : HasType env univs Γ e (.forallE A B) → A.Skips n k →
      ScopedFullStep n k Γ e (.lam A (.app e.lift (.bvar 0)))
  | app : ScopedFullStep n k Γ f f' → ScopedFullStep n k Γ a a' →
      ScopedFullStep n k Γ (.app f a) (.app f' a')
  | proj : ScopedFullStep n k Γ m m' → ScopedFullStep n k Γ (.proj S i m) (.proj S i m')
  | lam : ScopedFullStep n k Γ A A' → ScopedFullStep n (k+1) (A :: Γ) b b' →
      ScopedFullStep n k Γ (.lam A b) (.lam A' b')
  | forallE : ScopedFullStep n k Γ A A' → ScopedFullStep n (k+1) (A :: Γ) B B' →
      ScopedFullStep n k Γ (.forallE A B) (.forallE A' B')

/-- Forgetting annotation scope gives an ordinary full step. -/
theorem ScopedFullStep.full (H : ScopedFullStep n k Γ a b) : FullStep Γ a b := by
  induction H with
  | core H => exact .core H
  | delta H => exact .delta H
  | quotDelta H => exact .quotDelta H
  | projIota h1 h2 h3 h4 => exact .projIota h1 h2 h3 h4
  | structEta h1 h2 h3 h4 h5 _ => exact .structEta h1 h2 h3 h4 h5
  | funEta h _ => exact .funEta h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

omit [Params] in
private theorem list_lift_witness (H : ∀ a ∈ args, a.Skips n k) :
    ∃ lower : List VExpr, args = lower.map (·.liftN n k) := by
  refine ⟨args.map (·.unliftN n k), ?_⟩
  rw [List.map_map]
  symm
  calc
    _ = args.map id := List.map_congr_left H
    _ = args := List.map_id _

/-- No computation case requires a new scope premise. Only eta's added domain or
parameters must omit the removed binders. -/
theorem ScopedFullStep.scope (H : ScopedFullStep n k Γ e out) (hs : e.Skips n k) :
    out.Skips n k := by
  induction H with
  | core H => exact parRed_scope H hs
  | delta H =>
    obtain ⟨args, heq⟩ := list_lift_witness (skips_mkApps_iff.1 hs).2
    rw [heq] at H
    exact skips_iff_exists.2 (prefixUnfold_liftN_scope henv H)
  | quotDelta H =>
    obtain ⟨args, heq⟩ := list_lift_witness (skips_mkApps_iff.1 hs).2
    rw [heq] at H
    exact skips_iff_exists.2 (quotPrefixUnfold_liftN_scope henv H)
  | projIota _ _ hfield _ =>
    have hs' := skips_proj_iff.1 hs
    exact (skips_mkApps_iff.1 hs').2 _ (List.mem_of_getElem? hfield)
  | structEta _ _ _ _ _ hparams =>
    apply skips_mkApps_iff.2
    refine ⟨by simp [skips_iff, Skips'], ?_⟩
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hparams p hp
    · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
      exact skips_proj_iff.2 hs
  | funEta _ hA =>
    obtain ⟨e, rfl⟩ := skips_iff_exists.1 hs
    obtain ⟨A, rfl⟩ := skips_iff_exists.1 hA
    apply skips_iff_exists.2
    refine ⟨.lam A (.app e.lift (.bvar 0)), ?_⟩
    simp [liftN, lift_liftN', liftVar]
  | app _ _ ihf iha =>
    simp only [skips_iff, Skips'] at hs ⊢
    exact ⟨skips_iff.1 (ihf (skips_iff.2 hs.1)), skips_iff.1 (iha (skips_iff.2 hs.2))⟩
  | proj _ ih => exact skips_proj_iff.2 (ih (skips_proj_iff.1 hs))
  | lam _ _ ihd ihb | forallE _ _ ihd ihb =>
    simp only [skips_iff, Skips'] at hs ⊢
    exact ⟨skips_iff.1 (ihd (skips_iff.2 hs.1)), skips_iff.1 (ihb (skips_iff.2 hs.2))⟩

/-- Every genuine full step below weakens to a scope-certified full step above.
The additional checks hold automatically for the lifted eta annotations. -/
theorem _root_.Lean4Lean.VEnv.FullStep.weakN_scoped (W : Ctx.LiftN n k Γ Γ') (H : FullStep Γ a b) :
    ScopedFullStep n k Γ' (a.liftN n k) (b.liftN n k) := by
  induction H generalizing k Γ' with
  | core H => exact .core (H.weakN W)
  | delta H =>
    simp only [liftN_mkApps, VExpr.liftN]
    exact .delta (H.weakN henv W)
  | quotDelta H =>
    simp only [liftN_mkApps, VExpr.liftN]
    exact .quotDelta (H.weakN henv W)
  | projIota hl ht hi hf =>
    have ht' := ht.weakN henv W
    simp only [VExpr.liftN, liftN_mkApps] at ht' ⊢
    exact .projIota hl ht' (by simp [hi]) (hf.weakN henv W)
  | structEta hl hp hi hs ht =>
    have hs' := hs.weakN henv W
    have ht' := ht.weakN henv W
    simp only [liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    refine .structEta hl (by simpa using hp) hi hs' ht' ?_
    intro p hp
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hp
    exact .liftN
  | funEta ht =>
    simpa only [VExpr.liftN, ← lift_liftN', liftVar_zero] using
      ScopedFullStep.funEta (ht.weakN henv W) (Skips.liftN (n := n) (k := k))
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)

/-- Finite full reduction with scope-certified eta annotations throughout. -/
def ScopedFullReduction (n k : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop :=
  ReflTransGen (ScopedFullStep n k Γ)

/-- The scoped presentation retains the full reduction's computational meaning. -/
theorem ScopedFullReduction.full (H : ScopedFullReduction n k Γ a b) : FullReduction Γ a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ H ih => exact .tail ih H.full

/-- Weakening an entire full path gives scoped eta annotations at every step. -/
theorem _root_.Lean4Lean.VEnv.FullReduction.weakN_scoped (W : Ctx.LiftN n k Γ Γ') (H : FullReduction Γ a b) :
    ScopedFullReduction n k Γ' (a.liftN n k) (b.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ H ih => exact .tail ih (H.weakN_scoped W)

/-- Every intermediate and final term of such a path remains syntactically scoped. -/
theorem ScopedFullReduction.scope (H : ScopedFullReduction n k Γ a b) (hs : a.Skips n k) :
    b.Skips n k := by
  induction H with
  | rfl => exact hs
  | tail _ H ih => exact H.scope ih

/-- A scoped full path from a lifted source has a lowered target syntax. Its
ambient path is not asserted to be a full path in the smaller context. -/
theorem ScopedFullReduction.liftN_target
    {a : VExpr} (H : ScopedFullReduction n k Γ (a.liftN n k) out) : ∃ b : VExpr, out = b.liftN n k :=
  skips_iff_exists.1 (H.scope .liftN)

end Lean4Lean.VEnv.Strengthening
