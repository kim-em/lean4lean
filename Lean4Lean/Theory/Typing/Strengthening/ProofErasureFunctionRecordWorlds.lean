import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeterogeneousControlWorlds

/-! # Computational interpretation of joint function-parameter demands

Functions quantify over exact future context worlds and ordinary typed inputs.
Ground record values and their native types have independent common targets;
other type keys retain annotation information only in the syntactic observer.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets)
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- World-indexed realizability of joint keys. No native certificate is required
for an argument passed at its ordinary closed control type. -/
def WorldComputes (unit record : AtomicControl.Atom)
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (target : Key → ProofShape) (Δ : List ProofShape) (e : ProofShape) : Key → Prop
  | .unit => ScopedCompute Step Δ e (target .unit)
  | .record => ScopedCompute Step Δ e (target .record)
  | .fn domain keys result => ∀ {Δ' τ}, ContextRenaming Δ Δ' τ → ∀ a,
      HeterogeneousControl.ControlTyping Δ' a domain →
      (∀ key ∈ keys, WorldComputes unit record Step target Δ' a key) →
      WorldComputes unit record Step target Δ' (.app (e.subst τ) a) result
  | .type .record => ScopedCompute Step Δ e (target (.type .record))
  | .type _ => True
termination_by key => sizeOf key

/-- Exact renamings preserve every demand when primitives rename and all
chosen targets are closed. Arbitrary native substitution is not assumed. -/
theorem WorldComputes.rename
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hclosed : ∀ key τ, (target key).subst τ = target key)
    (H : WorldComputes unit record Step target Δ e key) (W : ContextRenaming Δ Δ' σ) :
    WorldComputes unit record Step target Δ' (e.subst σ) key := by
  cases key with
  | unit | record =>
    simp only [WorldComputes] at H ⊢
    simpa only [hclosed] using ScopedCompute.rename hstep H W
  | fn domain keys result =>
    simp only [WorldComputes] at H ⊢
    intro Δ'' τ W' a HA ha
    simpa only [ProofShape.subst_subst] using H (W.compose W') a HA ha
  | type key =>
    cases key with
    | unit | fn | type => simp only [WorldComputes]
    | record =>
      simp only [WorldComputes] at H ⊢
      simpa only [hclosed] using ScopedCompute.rename hstep H W

/-- Beta predecessors preserve the interpretation at all higher-order keys. -/
theorem WorldComputes.beta_back (R : BetaRed e e')
    (H : WorldComputes unit record Step target Δ e' key) :
    WorldComputes unit record Step target Δ e key := by
  cases key with
  | unit | record =>
    simp only [WorldComputes] at H ⊢
    exact (ScopedCompute.beta R).trans H
  | fn domain keys result =>
    simp only [WorldComputes] at H ⊢
    intro Δ' τ W a HA ha
    exact WorldComputes.beta_back (.app R.subst .refl) (H W a HA ha)
  | type key =>
    cases key with
    | unit | fn | type => simp only [WorldComputes]
    | record =>
      simp only [WorldComputes] at H ⊢
      exact (ScopedCompute.beta R).trans H
termination_by sizeOf key

/-- The joint observer has a computational interpretation once the actual
constructor and family realize their retained function demands. Annotation
certificates never create arbitrary record-family value leaves. -/
theorem Obs.world_computes
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hclosed : ∀ key τ, (target key).subst τ = target key)
    (HU : target .unit = .const uc [])
    (HC : ∀ {Δ}, HeterogeneousControl.ControlTyping Δ (.const ctor [])
      (.arrow (.arrow (.atom unit) (.atom unit)) (.atom record)) →
      WorldComputes unit record Step target Δ (.const ctor [])
        (.fn (.arrow (.atom unit) (.atom unit)) [.fn (.atom unit) [] .unit] .record))
    (HF : ∀ {Δ}, HeterogeneousControl.ControlTyping Δ (.const family [])
      (.arrow (.arrow (.atom unit) (.atom unit)) (.sort (HeterogeneousControl.ControlType.atom record).level)) →
      WorldComputes unit record Step target Δ (.const family [])
        (.fn (.arrow (.atom unit) (.atom unit)) [.fn (.atom unit) [] .unit] (.type .record)))
    (H : Obs unit record uc ctor family Ω S e key) (W : ContextSubstitution Ω Δ σ)
    (hσ : ∀ i key, S i key → WorldComputes unit record Step target Δ (σ i) key) :
    WorldComputes unit record Step target Δ (e.subst σ) key := by
  induction H generalizing Δ σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [ProofShape.subst, WorldComputes, HU]; exact .refl
  | record_ctor HT => exact HC (HT.subst W)
  | family HT => exact HF (HT.subst W)
  | unit_type | function_type | family_type | univ | pi => simp only [WorldComputes]
  | app HT HF HA ihf iha =>
    have HR := ihf W hσ
    simp only [WorldComputes] at HR
    have R := HR ContextRenaming.identity _ ((HT.argument HF.typing).subst W) (fun key hk => iha key hk W hσ)
    simpa only [ProofShape.subst_id, ProofShape.subst] using R
  | @lam Ω L b domain keys result S HT HE HK HA HB _ ih =>
    simp only [WorldComputes]
    intro Δ' τ W' a HX hx
    have WW : ContextSubstitution Ω Δ' (σ.comp τ) := ContextSubstitution.compose_world W W'.interpretation
    have WB : ContextSubstitution (L :: Ω) Δ' ((σ.comp τ).cons a) := HT.lambda_substitution WW HX
    have HR := ih WB (fun i key hi => by
      cases i with
      | zero => exact hx key hi
      | succ i => exact (hσ i key hi).rename hstep hclosed W')
    have E : (b.subst (σ.comp τ).lift).inst a = b.subst ((σ.comp τ).cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons,
          ProofShape.lift_subst_cons, ProofShape.subst_id]
    have R := WorldComputes.beta_back (E ▸ (BetaRed.beta (A := L.subst (σ.comp τ)))) HR
    simpa only [ProofShape.subst_subst, ProofShape.subst, Subst.comp_lift] using R

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
