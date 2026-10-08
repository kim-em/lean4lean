import Lean4Lean.Theory.Typing.ShapeModel.RuleValidCtor

/-!
# Transfer of approximations along the types of spines

For a well-typed spine `h pre M` whose head type is syntactically a telescope with the domain `D`
at the position of `M`, and a spine `c margs` whose head type is a telescope ending in a body
`bodyc`, the type `A` of `M` in the record of the spine is related to `D` (under keys typed along
the head's telescope that approximate `pre`) and to `bodyc` (under keys approximating `margs`):

* `head_dom_of_type` / `head_type_of_dom`: approximations of `A` (that are types) approximate `D`
  under suitable keys, and conversely;
* `ctor_body_of_type` / `ctor_type_of_body`: approximations of the type of `c margs` approximate
  `bodyc` under suitable keys, and conversely.

These are the semantic forms of "the type of the major is the major domain of the eliminator" and
"the type of a constructor application is its codomain", used by the alignment and the field reads
of rules with a constructor major.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- The record of the type of the head of a spine. -/
theorem Spine.headInfo {h : Head} {rev : List VExpr}
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) rev.reverse) T) :
    ∃ Th u, HeadType env h ls Th ∧ StrongSound env Γ Th (.sort u) := by
  induction rev generalizing T with
  | nil =>
    obtain ⟨_, hcore, -⟩ := hTy
    cases h with
    | const c =>
      obtain ⟨ci, u, h1, -, h3, rfl⟩ := hcore.const_inv
      exact ⟨_, u, ⟨ci, h1, rfl⟩, h3⟩
    | elim b o =>
      cases hcore with | elim h1 _ h3 => exact ⟨_, _, ⟨_, h1, rfl⟩, h3⟩
  | cons a rev ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at hTy
    obtain ⟨_, hcore, -⟩ := hTy
    obtain ⟨_, _, hf, -⟩ := hcore.app_inv
    exact ih hf

theorem HeadType.unique {h : Head} (h₁ : HeadType env h ls Th) (h₂ : HeadType env h ls Th') :
    Th = Th' := by
  cases h with
  | const c =>
    obtain ⟨ci, e1, rfl⟩ := h₁; obtain ⟨ci', e2, rfl⟩ := h₂
    cases e1.symm.trans e2; rfl
  | elim b o =>
    obtain ⟨T, e1, rfl⟩ := h₁; obtain ⟨T', e2, rfl⟩ := h₂
    cases e1.symm.trans e2; rfl

theorem StrongSound.app_last {f : VExpr} {pre : List VExpr} {M : VExpr}
    (hTy : StrongSound env Γ (VExpr.mkApps f (pre ++ [M])) B) :
    ∃ A Bf, StrongSound env Γ (VExpr.mkApps f pre) (.forallE A Bf) ∧ StrongSound env Γ M A := by
  rw [VExpr.mkApps_append_singleton] at hTy
  obtain ⟨_, hcore, -⟩ := hTy
  obtain ⟨A, Bf, hf, hM, -⟩ := hcore.app_inv
  exact ⟨A, Bf, hf, hM⟩

theorem nestPi_reverse_cons {ps : List (TShape × TShape)} {q : TShape × TShape} {R : TShape} :
    nestPi (q :: ps).reverse R = nestPi ps.reverse (TShape.pi q.1 q.2 R) := by
  rw [List.reverse_cons, nestPi_append_singleton]

/-- Approximations of the type of the major (that are types) approximate the major domain of the
head's telescope, under typed keys above given approximations of the earlier arguments. -/
theorem head_dom_of_type {h : Head} (W : Valuation.Fits env Γ₀ Γ σ)
    (hf : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) pre) (.forallE A Bf))
    (hTh : HeadType env h ls Th) {doms₀ : List VExpr} {D TbH : VExpr}
    (hThs : Th = VExpr.wrapForalls (doms₀ ++ [D]) TbH) (hlen : doms₀.length = pre.length)
    (hxs : List.Forall₂ (fun x A => Interp env σ x A) xs pre)
    (ht : Interp env σ t A) (htt : t.HasType .type) :
    ∃ ps : List (TShape × TShape), List.Forall₂ (fun x p => x ≤ p.2) xs ps ∧
      List.Forall₂ (fun p A => Interp env σ p.2 A) ps pre ∧ TelTyped ps ∧
      TelInterp env σ doms₀ ps ∧ Interp env (σ.pushes (ps.map (·.2))) t D := by
  have hf' : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) pre.reverse.reverse) (.forallE A Bf) := by
    rwa [List.reverse_reverse]
  have hpi : Interp env σ (TShape.pi t TShape.bot TShape.bot) (.forallE A Bf) :=
    Interp.pi_intro ht (TShape.HasType.bot' htt) .bot
  obtain ⟨qs, hq1, hq2, hq3, hq4⟩ := Spine.typed_head W hf' hTh (List.Forall₂.reverse.2 hxs) hpi
  rw [hThs] at hq4
  have h4 : Interp env σ (nestPi qs.reverse (TShape.pi t TShape.bot TShape.bot))
      (doms₀.foldr .forallE (.forallE D TbH)) := by
    simpa only [VExpr.wrapForalls, List.foldr_append, List.foldr_cons, List.foldr_nil] using hq4
  obtain ⟨htel, hP⟩ := Interp.nest_inv (by rw [List.length_reverse, hq2.length_eq]; simp [hlen]) h4
  refine ⟨qs.reverse, ?_, ?_, fun p hp => hq3 p (List.mem_reverse.1 hp), htel, (Interp.pi_inv hP).1⟩
  · have := List.Forall₂.reverse.2 hq1; rwa [List.reverse_reverse] at this
  · have := List.Forall₂.reverse.2 hq2; rwa [List.reverse_reverse] at this

/-- Conversely, a type approximating the major domain of the head's telescope under typed keys
approximating the earlier arguments approximates the type of the major. -/
theorem head_type_of_dom {h : Head} (W : Valuation.Fits env Γ₀ Γ σ)
    (hf : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) pre) (.forallE A Bf))
    (hTh : HeadType env h ls Th) {doms₀ : List VExpr} {D TbH : VExpr}
    (hThs : Th = VExpr.wrapForalls (doms₀ ++ [D]) TbH)
    {ps : List (TShape × TShape)} (hps : List.Forall₂ (fun p A => Interp env σ p.2 A) ps pre)
    (hpt : TelTyped ps) (htel : TelInterp env σ doms₀ ps)
    (ht : Interp env (σ.pushes (ps.map (·.2))) t D) (htt : t.HasType .type) :
    Interp env σ t A := by
  have hf' : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) pre.reverse.reverse) (.forallE A Bf) := by
    rwa [List.reverse_reverse]
  have hpi : Interp env (σ.pushes (ps.map (·.2))) (TShape.pi t TShape.bot TShape.bot)
      (.forallE D TbH) := Interp.pi_intro ht (TShape.HasType.bot' htt) .bot
  have hN := Interp.nest_intro htel hpt hpi
  have hN' : Interp env σ (nestPi ps.reverse.reverse (TShape.pi t TShape.bot TShape.bot)) Th := by
    rw [List.reverse_reverse, hThs]
    simpa only [VExpr.wrapForalls, List.foldr_append, List.foldr_cons, List.foldr_nil] using hN
  have hps' : List.Forall₂ (fun p A => Interp env σ p.2 A) ps.reverse pre.reverse :=
    List.Forall₂.reverse.2 hps
  exact (Interp.pi_inv (Spine.ofPi_head W hf' hTh hps' hN')).1

/-- Approximations of the type of a constructor application approximate the codomain of the
constructor's telescope, under typed keys above given approximations of the arguments. -/
theorem ctor_body_of_type (W : Valuation.Fits env Γ₀ Γ σ)
    (hM : StrongSound env Γ (VExpr.mkApps (.const c ls) margs) A)
    (hcv : env.constants c = some cv) {domsc : List VExpr} {bodyc : VExpr}
    (hct : cv.type.instL ls = VExpr.wrapForalls domsc bodyc) (hlen : domsc.length = margs.length)
    (hxs : List.Forall₂ (fun x A => Interp env σ x A) xs margs) (ht : Interp env σ t A) :
    ∃ ps : List (TShape × TShape), List.Forall₂ (fun x p => x ≤ p.2) xs ps ∧
      List.Forall₂ (fun p A => Interp env σ p.2 A) ps margs ∧ TelTyped ps ∧
      TelInterp env σ domsc ps ∧ Interp env (σ.pushes (ps.map (·.2))) t bodyc := by
  have hM' : StrongSound env Γ (VExpr.mkApps (.const c ls) margs.reverse.reverse) A := by
    rwa [List.reverse_reverse]
  obtain ⟨qs, hq1, hq2, hq3, hq4⟩ := Spine.typed W hM' hcv (List.Forall₂.reverse.2 hxs) ht
  rw [hct] at hq4
  obtain ⟨htel, hb⟩ := Interp.nest_inv (by rw [List.length_reverse, hq2.length_eq]; simp [hlen]) hq4
  refine ⟨qs.reverse, ?_, ?_, fun p hp => hq3 p (List.mem_reverse.1 hp), htel, hb⟩
  · have := List.Forall₂.reverse.2 hq1; rwa [List.reverse_reverse] at this
  · have := List.Forall₂.reverse.2 hq2; rwa [List.reverse_reverse] at this

/-- Conversely, an approximation of the codomain of a constructor's telescope under typed keys
approximating the arguments approximates the type of the application. -/
theorem ctor_type_of_body (W : Valuation.Fits env Γ₀ Γ σ)
    (hM : StrongSound env Γ (VExpr.mkApps (.const c ls) margs) A)
    (hcv : env.constants c = some cv) {domsc : List VExpr} {bodyc : VExpr}
    (hct : cv.type.instL ls = VExpr.wrapForalls domsc bodyc)
    {ps : List (TShape × TShape)} (hps : List.Forall₂ (fun p A => Interp env σ p.2 A) ps margs)
    (hpt : TelTyped ps) (htel : TelInterp env σ domsc ps)
    (ht : Interp env (σ.pushes (ps.map (·.2))) t bodyc) : Interp env σ t A := by
  have hM' : StrongSound env Γ (VExpr.mkApps (.const c ls) margs.reverse.reverse) A := by
    rwa [List.reverse_reverse]
  have hN := Interp.nest_intro htel hpt ht
  have hN' : Interp env σ (nestPi ps.reverse.reverse t) (cv.type.instL ls) := by
    rw [List.reverse_reverse, hct]; exact hN
  exact Spine.ofPi W hM' hcv (List.Forall₂.reverse.2 hps) hN'

end

end Lean4Lean.ShapeModel
