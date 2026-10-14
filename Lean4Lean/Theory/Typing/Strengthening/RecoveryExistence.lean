import Lean4Lean.Theory.Typing.Strengthening.TypeRecoveryCore

/-! # Exact obligations for recovery at some type

Recovery at an arbitrary preselected type is false. Existence of a recoverable
output has a different boundary: recover Pi types at well-formed applications,
and usable family types at well-formed projections. These two obligations are
both necessary and sufficient. Neither is assumed proved for the staged model.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {C : List VExpr → VExpr → VExpr → Prop}

/-- A recovery of an application contains a Pi recovery for its function,
regardless of trailing conversions of the application's resulting type. -/
theorem TypeRecoveryWith.app_inv (R : TypeRecoveryWith C Γ (.app f a) T) :
    ∃ A B, TypeRecoveryWith C Γ f (.forallE A B) := by
  generalize h : VExpr.app f a = e at R
  induction R with
  | app R _ => cases h; exact ⟨_, _, R⟩
  | convert _ _ ih => exact ih h
  | sort | const | bvar | lam | forallE | proj => cases h

/-- A recovered projection contains a selected field in a recovered major
family. Trailing output conversions do not hide this premise. -/
theorem TypeRecoveryWith.proj_inv (R : TypeRecoveryWith C Γ (.proj s i m) T) :
    ∃ info ls args F, env.projections s info ∧
      TypeRecoveryWith C Γ m (mkApps (.const s ls) args) ∧
      info.fieldType s ls (args.take info.nparams) i m = some F := by
  generalize h : VExpr.proj s i m = e at R
  induction R with
  | proj hi R hF _ => cases h; exact ⟨_, _, _, _, hi, R, hF⟩
  | convert _ _ ih => exact ih h
  | sort | const | bvar | lam | app | forallE => cases h

/-- Every well-formed expression has some recoverable output. The output is not
required to be an arbitrary type at which that expression was originally typed. -/
def RecoveryExists (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ e}, OnCtx Γ (env.IsType univs) → VExpr.WF env univs Γ e →
    ∃ T, TypeRecoveryWith C Γ e T

/-- The remaining local synthesis obligations. An application must recover a
Pi from its already recoverable function; a projection must recover a usable
family from its already recoverable major. These obligations are unproved for
the concrete staged computation and are not asserted sufficient for strengthening. -/
structure RecoveryHeads (C : List VExpr → VExpr → VExpr → Prop) : Prop where
  app : ∀ {Γ f a T}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.app f a) → TypeRecoveryWith C Γ f T →
    ∃ A B, TypeRecoveryWith C Γ f (.forallE A B)
  proj : ∀ {Γ s i m T}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.proj s i m) → TypeRecoveryWith C Γ m T →
    ∃ info ls args F, env.projections s info ∧
      TypeRecoveryWith C Γ m (mkApps (.const s ls) args) ∧
      info.fieldType s ls (args.take info.nparams) i m = some F

/-- All other expression constructors synthesize directly. No computation
normalization or prescribed output type is used in this structural induction. -/
theorem RecoveryHeads.exists (H : RecoveryHeads C) : RecoveryExists C := by
  intro Γ e hΓ ht
  induction e generalizing Γ with
  | bvar i =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨T, hT⟩ := HasType.bvar_inv henv hΓ ht
    exact ⟨T, .bvar hT⟩
  | sort u =>
    obtain ⟨_, ht⟩ := ht
    exact ⟨_, .sort (HasType.sort_inv henv.ordered ht)⟩
  | const c ls =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨ci, hc, hls, hn⟩ := HasType.const_inv henv hΓ ht
    exact ⟨_, .const hc hls hn⟩
  | app f a ihf _ =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨T, R⟩ := ihf hΓ ⟨_, hf⟩
    obtain ⟨A, B, R⟩ := H.app hΓ ht R
    exact ⟨_, .app R⟩
  | lam A b _ ihb =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨B, R⟩ := ihb (Γ := A :: Γ) ⟨hΓ, hA⟩ hb
    exact ⟨_, .lam R⟩
  | forallE A B _ _ =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := HasType.forallE_inv henv.ordered ht
    exact ⟨_, .forallE hA hB⟩
  | proj s i m ihm =>
    obtain ⟨_, ht'⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht'
    obtain ⟨T, R⟩ := ihm hΓ ⟨_, hm.hasType.2⟩
    obtain ⟨info, ls, args, F, hi, R, hF⟩ := H.proj hΓ ⟨_, ht'⟩ R
    exact ⟨F, .proj hi R hF⟩

/-- Conversely, existence on the complete application or projection supplies
exactly the corresponding head clause by certificate inversion. -/
theorem RecoveryExists.heads (H : RecoveryExists C) : RecoveryHeads C where
  app hΓ ht _ := by
    obtain ⟨_, R⟩ := H hΓ ht
    exact R.app_inv
  proj hΓ ht _ := by
    obtain ⟨_, R⟩ := H hΓ ht
    exact R.proj_inv

/-- The local clauses characterize recovery existence exactly, rather than
being a stronger arbitrary-typing completeness premise. -/
theorem recoveryExists_iff_heads : RecoveryExists C ↔ RecoveryHeads C :=
  ⟨RecoveryExists.heads, RecoveryHeads.exists⟩

/-- Under the two explicit head obligations, ordinary typed substitution can
re-synthesize a different output type. Uniqueness aligns it with the old
substituted output; no recovery certificate for the argument is required. -/
theorem TypeRecoveryWith.resynthesize_instN (R : TypeRecoveryWith C Γ₁ e T)
    (hc : ComputeDescent C) (H : RecoveryHeads C)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    ∃ T', TypeRecoveryWith C Γ (e.inst x k) T' ∧
      env.IsDefEqU univs Γ (T.inst x k) T' := by
  have he := R.hasType hc hΓ₁ ht
  have hΓ := (W.wf henv hx hΓ₁).2
  have he' := he.instN henv W hx
  obtain ⟨T', R'⟩ := H.exists hΓ ⟨_, he'⟩
  exact ⟨T', R', he'.uniqU henv hΓ (R'.hasType hc hΓ ⟨_, he'⟩)⟩


/-- A local computational completeness obligation for inferred function types.
Only Pi exposure is requested; the exposed domain and codomain may differ from
the originally supplied Pi. This is unproved for the staged model. -/
def RecoveryPiExposure (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ T A B u}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ T (.sort u) →
    env.IsDefEqU univs Γ T (.forallE A B) →
    ∃ A' B', C Γ T (.forallE A' B')

/-- The analogous local obligation for projections. The recovered family may
use different parameters and levels; its selected field must exist. No exact
agreement with the projection's original field type is requested. -/
def RecoveryProjectionExposure (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ s i m T}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.proj s i m) → env.HasType univs Γ m T →
    ∃ info ls args F, env.projections s info ∧ C Γ T (mkApps (.const s ls) args) ∧
      info.fieldType s ls (args.take info.nparams) i m = some F

/-- Computational exposure of already recovered types supplies both necessary
synthesis clauses. Type uniqueness supplies the Pi equation at an application;
there is no assumption that its originally chosen Pi was recoverable. -/
theorem RecoveryHeads.of_type_exposure (hc : ComputeDescent C)
    (hPi : RecoveryPiExposure C) (hProj : RecoveryProjectionExposure C) :
    RecoveryHeads C where
  app hΓ ht R := by
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    have hf' := R.hasType hc hΓ ⟨_, hf⟩
    obtain ⟨_, hT⟩ := hf'.isType henv hΓ
    obtain ⟨A', B', RT⟩ := hPi hΓ hT (hf'.uniqU henv hΓ hf)
    exact ⟨A', B', .convert R RT⟩
  proj hΓ ht R := by
    obtain ⟨_, ht'⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht'
    have hm' := R.hasType hc hΓ ⟨_, hm.hasType.2⟩
    obtain ⟨info, ls, args, F, hi, RT, hF⟩ := hProj hΓ ⟨_, ht'⟩ hm'
    exact ⟨info, ls, args, F, hi, .convert R RT, hF⟩

end Lean4Lean.VEnv.Strengthening
