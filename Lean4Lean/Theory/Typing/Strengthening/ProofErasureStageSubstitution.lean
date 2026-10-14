import Lean4Lean.Theory.Typing.Strengthening.ProofShapeSubstitution

/-! # Substitution through finite erased computation stages

Visible matches, closed RHS templates and endpoint computation guards survive
arbitrary raw substitution on proof shapes. This gives same-stage substitution
of computations, then specializes to typed original substitutions via erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Erased beta paths survive simultaneous substitution. -/
theorem BetaRed.subst (H : BetaRed e out) : BetaRed (e.subst σ) (out.subst σ) := by
  induction H generalizing σ with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta => rw [subst_inst]; exact .beta

/-- Primitive substitution stability extends through finite compatible paths. -/
theorem Compute.subst
    (hstep : ∀ {a b} {σ : Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : Compute Step e out) : Compute Step (e.subst σ) (out.subst σ) := by
  induction H generalizing σ with
  | base h => exact .base (hstep h)
  | beta h => exact .beta h.subst
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

/-- Substitution acts pointwise on erased application spines. -/
theorem subst_mkApps (f : ProofShape) (args : List ProofShape) :
    (mkApps f args).subst σ = mkApps (f.subst σ) (args.map (·.subst σ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

/-- A visible match retains its shape and substitutes each capture. -/
theorem Matches.subst (H : Matches p e ls captures) :
    Matches p (e.subst σ) ls (fun i => (captures i).subst σ) := by
  induction H with
  | @const c ls =>
    have congr_captures {p : Pattern} {e : ProofShape} {ls : List VLevel} {c d : p.Path → ProofShape}
        (H : Matches p e ls c) (hc : ∀ i, c i = d i) : Matches p e ls d := by
      cases funext hc
      exact H
    apply congr_captures (Matches.const (c := c) (ls := ls))
    intro i
    exact nomatch i
  | @var f f' levels captures a H ih =>
    have hh : (fun i => (Option.elim i a captures).subst σ) =
        (fun i => Option.elim i (a.subst σ) (fun j => (captures j).subst σ)) := by
      funext i
      cases i <;> rfl
    exact hh.symm ▸ Matches.var (a := a.subst σ) ih
  | @app f f' levels captures a a' levels' captures' Hf Ha ihf iha =>
    have hh : (fun i => (Sum.elim captures captures' i).subst σ) =
        Sum.elim (fun j => (captures j).subst σ) (fun j => (captures' j).subst σ) := by
      funext i
      cases i <;> rfl
    exact hh.symm ▸ Matches.app ihf iha

/-- Pointwise computation of substitution images computes the substituted term.
Under a binder, image computations weaken once and the fresh variable is fixed. -/
theorem Compute.subst_images
    (hstep : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (e : ProofShape) {σ τ : Subst} (H : ∀ i, Compute Step (σ i) (τ i)) :
    Compute Step (e.subst σ) (e.subst τ) := by
  induction e generalizing σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app f a ihf iha => exact .app (ihf H) (iha H)
  | proj s i m ih => exact .proj (ih H)
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, Compute Step (σ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .refl
      | succ i => exact (H i).liftN hstep
    first | exact .lam (ihA H) (ihb HB) | exact .forallE (ihA H) (ihb HB)
end ProofShape

variable [Params]

/-- A substitution fixing all in-scope variables fixes an erased scoped term.
Proof detection is unchanged because the original term is not being substituted. -/
theorem proofErase_subst_fixed (hc : e.ClosedN k) {σ : ProofShape.Subst}
    (H : ∀ i, i < k → σ i = .bvar i) : (proofErase Γ e).subst σ = proofErase Γ e := by
  induction e generalizing Γ k σ with
  | bvar i =>
    simp only [proofErase]
    split
    · rfl
    · exact H i hc
  | sort | const => simp only [proofErase]; split <;> rfl
  | app f a ihf iha =>
    simp only [proofErase]
    split
    · rfl
    · simp only [ProofShape.subst, ihf hc.1 H, iha hc.2 H]
  | proj s i m ih =>
    simp only [proofErase]
    split
    · rfl
    · simp only [ProofShape.subst, ih hc H]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, i < k+1 → σ.lift i = .bvar i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [ProofShape.Subst.lift, H i (by omega), ProofShape.liftN, liftVar, Nat.add_comm]
    simp only [proofErase]
    split
    · rfl
    · simp only [ProofShape.subst, ihA hc.1 H, ihb hc.2 HB]

/-- Closed erased declaration bodies are fixed by every raw substitution. -/
theorem proofErase_closed_subst (hc : e.Closed) {σ : ProofShape.Subst} :
    (proofErase Γ e).subst σ = proofErase Γ e :=
  proofErase_subst_fixed hc (fun _ h => (Nat.not_lt_zero _ h).elim)

/-- Declaration and projection primitives survive raw simultaneous substitution. -/
theorem ProofShape.Primitive.subst (H : ProofShape.Primitive D e out) :
    ProofShape.Primitive D (e.subst σ) (out.subst σ) := by
  cases H with
  | delta hd =>
    rw [proofErase_closed_subst (D.closed hd)]
    exact .delta hd
  | projIota hi hl hg =>
    simp only [ProofShape.subst, ProofShape.subst_mkApps]
    apply ProofShape.Primitive.projIota hi (by simpa only [List.length_map] using hl)
    simp only [List.getElem?_map, hg, Option.map_some]

/-- Selector and capture-application primitives substitute their visible matches. -/
theorem ProofShape.CapturePrimitive.subst (H : ProofShape.CapturePrimitive e out) :
    ProofShape.CapturePrimitive (e.subst σ) (out.subst σ) := by
  cases H with
  | select hp hc hm => exact .select hp hc hm.subst
  | apply hp hc hm => exact .apply hp hc hm.subst

/-- Template heads stay closed while substitution changes their captures. -/
theorem ProofShape.TemplatePrimitive.subst (H : ProofShape.TemplatePrimitive e out) :
    ProofShape.TemplatePrimitive (e.subst σ) (out.subst σ) := by
  cases H with
  | intro hp hc ht hm =>
    rw [ProofShape.subst_mkApps, proofErase_closed_subst (ht.closedN' henv.ordered.closed (by trivial)).1]
    simp only [List.map_map, Function.comp_def]
    exact .intro hp hc ht hm.subst

/-- Every visible primitive is closed under raw substitution. -/
theorem erased_iota_primitive_subst (H : ErasedIotaPrimitive D a b) :
    ErasedIotaPrimitive D (a.subst σ) (b.subst σ) := by
  rcases H with (H | H) | H
  · exact .inl (.inl H.subst)
  · exact .inl (.inr H.subst)
  · exact .inr H.subst

omit [Params] in
/-- Substitution stability of predecessor paths preserves a K guard. -/
theorem ProofShape.KPrimitive.subst
    (hstep : ∀ {a b} {σ : ProofShape.Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : ProofShape.KPrimitive Step e out) :
    ProofShape.KPrimitive Step (e.subst σ) (out.subst σ) := by
  cases H with
  | intro Ha Hb =>
    simpa only [ProofShape.eqRec, ProofShape.subst] using
      (ProofShape.KPrimitive.intro (v := _) (w := _) (α := _) (M := _) (m := _) (p := _)
        (Ha.subst hstep (σ := σ)) (Hb.subst hstep (σ := σ)))

/-- All finite erased K primitive stages survive arbitrary substitution. -/
theorem erased_K_stage_subst : ∀ stage {a b} {σ : ProofShape.Subst}, ErasedKStage D stage a b →
    ErasedKStage D stage (a.subst σ) (b.subst σ) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_subst H
  | succ stage ih =>
    intro a b σ H
    exact H.elim (fun h => .inl (ih h)) (fun h => .inr (h.subst ih))

/-- Finite erased computations substitute without increasing their stage. -/
theorem erased_K_compute_subst (H : ProofShape.Compute (ErasedKStage D stage) a b) :
    ProofShape.Compute (ErasedKStage D stage) (a.subst σ) (b.subst σ) :=
  H.subst (erased_K_stage_subst stage)

/-- Both the body computation and pointwise argument computations may be
performed in one stage; no additional recovery premise is needed on raw shapes. -/
theorem erased_K_compute_subst_images (H : ProofShape.Compute (ErasedKStage D stage) a b)
    {σ τ : ProofShape.Subst} (Himages : ∀ i, ProofShape.Compute (ErasedKStage D stage) (σ i) (τ i)) :
    ProofShape.Compute (ErasedKStage D stage) (a.subst σ) (b.subst τ) :=
  (erased_K_compute_subst H).trans (ProofShape.Compute.subst_images (erased_K_stage_liftN stage) b Himages)

/-- The raw closure theorem applies to actual typed substitutions using the
already proved commutation of typed erasure and simultaneous substitution. -/
theorem proofErase_K_subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (he : env.HasType univs Γ e T)
    (H : ProofShape.Compute (ErasedKStage D stage) (proofErase Γ e) out) :
    ProofShape.Compute (ErasedKStage D stage) (proofErase Γ₀ (e.subst σ))
      (out.subst (fun i => proofErase Γ₀ (σ i))) := by
  rw [proofErase_subst hΓ₀ W he]
  exact erased_K_compute_subst H

end Lean4Lean.VEnv.Strengthening
