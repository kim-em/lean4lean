import Lean4Lean.Verify.Inductive.Recursor.RecursiveShapeRow
import Lean4Lean.Verify.Inductive.Recursor.CanonicalRecursorTelescope
import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldDefEq

/-! Induction-hypothesis binder groups of the checked recursor type, read off
the per-field semantic row.

`CompletedRecursorConstruction.recursorTelescope_hypothesisDomains` identifies
the `j`-th hypothesis of a minor premise of the checked recursor type as a
telescope `A` whose domains translate the first-pass origin's argument domains
in the full generator context (parameters, motives, earlier minors, all fields
and the earlier hypotheses).  The per-field semantic row
(`RecInfoHypothesisCallSemanticOriginsAt`) records that the generated recursive
call is scoped by the field's own prefix: its argument telescope mentions only
the parameters and the fields before the recursive field.  Since the
first-pass origin and the semantic call have the same replay trace, the
origin's argument domains and closed exposed indices inherit that scope.

Abstracting variables that do not occur is a de Bruijn lift, so the generator
sources are lifts of sources closed only over the field prefix and the
parameters.  Inverting bound-variable weakening (`TrExprS.weakBV_inv_lift`, a
generalisation of `TrExprS.weakBV_inv` to lifted sources) twice per binder then
exhibits every domain of `A`, and every index of the motive application, as
`InductiveSignature.Instance.underFields` of a translation in the small context
`parameters ++ fields.take pos`.  This is
`CompletedRecursorConstruction.recursorTelescope_hypothesisUnlift`. -/

namespace Lean4Lean
open VEnv Lean

/-- Lookups in a lifted context at a lifted variable come from lookups in
the original context. -/
theorem VLCtx.BVLift.find?_exists_liftVar (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (h : ∃ x, Δ'.find? (VLCtx.liftVar dn dk v) = some x) : ∃ x, Δ.find? v = some x := by
  induction W generalizing v with
  | refl => simpa [VLCtx.liftVar_zero] using h
  | skip d _ ih =>
    obtain i | fv := v
    · have ⟨_, h⟩ := h
      simp only [VLCtx.liftVar, Nat.not_lt_zero, if_false, ← Nat.add_assoc] at h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      exact ih (v := .inl i) ⟨_, by simpa [VLCtx.liftVar] using h⟩
    · have ⟨_, h⟩ := h
      simp [VLCtx.liftVar, VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      exact ih (v := .inr fv) ⟨_, h⟩
  | @cons Δ₀ Δ₀' dn' dk' n' k' d _ ih =>
    obtain (_ | i) | fv := v
    · exact ⟨_, rfl⟩
    · have ⟨_, h⟩ := h
      have hv : VLCtx.liftVar dn' (dk' + 1) (.inl (i + 1)) =
          .inl ((if i < dk' then i else i + dn') + 1) := by
        simp only [VLCtx.liftVar]; split <;> split <;> (try congr 1) <;> omega
      rw [hv] at h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      have ⟨⟨e, A⟩, h'⟩ := ih (v := .inl i) ⟨_, by simpa [VLCtx.liftVar] using h⟩
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, bind, h']⟩
    · have ⟨_, h⟩ := h
      simp [VLCtx.liftVar, VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      have ⟨⟨e, A⟩, h'⟩ := ih (v := .inr fv) ⟨_, by simpa [VLCtx.liftVar] using h⟩
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, bind, h']⟩

variable! (henv : VEnv.WF env) in
/-- Inverse of `TrExprS.weakBV` for an arbitrary source: a translation of a
lifted source in a lifted context is the lift of a translation in the
original context. -/
theorem TrExprS.weakBV_inv_lift (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ' e' t) (he : e' = e.liftLooseBVars' dk dn) :
    ∃ t₀, TrExprS env Us Δ e t₀ ∧ t = t₀.liftN n k := by
  induction H generalizing e Δ dk k with
  | bvar h1 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    rename_i i₀
    subst he
    rw [show (Sum.inl (if i₀ < dk then i₀ else i₀ + dn) : Nat ⊕ FVarId) =
      VLCtx.liftVar dn dk (.inl i₀) from rfl] at h1
    have ⟨⟨e₀, A₀⟩, h2⟩ := W.find?_exists_liftVar ⟨_, h1⟩
    have h3 := W.find? h2
    cases h1.symm.trans h3
    exact ⟨_, .bvar h2, rfl⟩
  | fvar h1 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    subst he
    have ⟨⟨e₀, A₀⟩, h2⟩ := W.find?_exists_liftVar (v := .inr _) ⟨_, h1⟩
    have h3 := W.find? h2
    cases h1.symm.trans h3
    exact ⟨_, .fvar h2, rfl⟩
  | sort h1 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    subst he
    exact ⟨_, .sort h1, rfl⟩
  | const h1 h2 h3 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, .const h1 h2 h3, rfl⟩
  | app h1 h2 _ _ ih1 ih2 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f₀, hf₀, rfl⟩ := ih1 W hΔ' rfl
    obtain ⟨a₀, ha₀, rfl⟩ := ih2 W hΔ' rfl
    have := (VExpr.WF.weakN_iff henv hΔ'.toCtx W.toCtx (e := .app f₀ a₀)).1 ⟨_, h1.app h2⟩
    have ⟨_, _, h3, h4⟩ := this.app_inv henv.ordered (W.wf henv hΔ').toCtx
    exact ⟨_, .app h3 h4 hf₀ ha₀, rfl⟩
  | lam h1 _ _ ih1 ih2 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hΔ' rfl
    have h1' := (IsType.weakN_iff henv hΔ'.toCtx W.toCtx).1 h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlam (ty₀.liftN n k)) :: _) := ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih2 (W.cons (.vlam ty₀)) hΔ'' rfl
    exact ⟨_, .lam h1' hty₀ hbody₀, rfl⟩
  | forallE h1 h2 _ _ ih1 ih2 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hΔ' rfl
    have h1' := (IsType.weakN_iff henv hΔ'.toCtx W.toCtx).1 h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlam (ty₀.liftN n k)) :: _) := ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih2 (W.cons (.vlam ty₀)) hΔ'' rfl
    have hΓ'' : OnCtx (ty₀.liftN n k :: _) (env.IsType Us.length) := ⟨hΔ'.toCtx, h1⟩
    have h2' := (IsType.weakN_iff henv hΓ'' (W.cons (.vlam ty₀)).toCtx).1 h2
    exact ⟨_, .forallE h1' h2' hty₀ hbody₀, rfl⟩
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨ty₀, hty₀, rfl⟩ := ih1 W hΔ' rfl
    obtain ⟨val₀, hval₀, rfl⟩ := ih2 W hΔ' rfl
    have h1' := (HasType.weakN_iff henv hΔ'.toCtx W.toCtx).1 h1
    have hΔ'' : VLCtx.WF env Us.length ((none, .vlet (ty₀.liftN n k) (val₀.liftN n k)) :: _) :=
      ⟨hΔ', nofun, h1⟩
    obtain ⟨body₀, hbody₀, rfl⟩ := ih3 (W.cons (.vlet ty₀ val₀)) hΔ'' rfl
    exact ⟨_, .letE h1' hty₀ hval₀ hbody₀, rfl⟩
  | lit h1 _ ih =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    subst he
    obtain ⟨_, h, rfl⟩ := ih W hΔ' (Expr.liftLooseBVars_eq_self
      Closed.toConstructor.looseBVarRange_le).symm
    exact ⟨_, .lit h1 h, rfl⟩
  | mdata _ ih =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨_, h, rfl⟩ := ih W hΔ' rfl
    exact ⟨_, .mdata h, rfl⟩
  | proj _ hp ih =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨s₀, hs₀, rfl⟩ := ih W hΔ' rfl
    cases hp with | direct m t
    have m' := (VExpr.WF.weakN_iff henv hΔ'.toCtx W.toCtx).1 m
    have t' := (VExpr.WF.weakN_iff henv hΔ'.toCtx W.toCtx (e := .proj _ _ s₀)).1 t
    exact ⟨_, .proj hs₀ (.direct m' t'), rfl⟩

/-- Forward replacement for `TrExprS.weakBV_inv_lift`: when the source already
has a translation `t₀` in the smaller context, every translation of its lift
in the lifted context is the lift of `t₀`.  Unlike the inverse direction this
needs no typing strengthening, only `weakBV` and syntactic uniqueness. -/
theorem TrExprS.weakBV_lift_eq (henv : VEnv.Ordered env)
    (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H₀ : TrExprS env Us Δ e t₀)
    (H : TrExprS env Us Δ' (e.liftLooseBVars' dk dn) T) :
    T = t₀.liftN n k :=
  H.uniqueS (H₀.weakBV henv W)

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- `abstract1` is injective: loose bound variables below the cutoff are
fixed, those at or above it are shifted by one, and the cutoff itself is hit
only by the abstracted variable. -/
theorem Expr.abstract1_injective {v : FVarId} :
    ∀ {e e' : Expr} {k : Nat}, e.abstract1 v k = e'.abstract1 v k → e = e' := by
  intro e
  induction e with
  | bvar i =>
    intro e' k h
    cases e' with
    | bvar i' =>
      simp only [Expr.abstract1, Expr.bvar.injEq] at h
      congr 1; split at h <;> split at h <;> omega
    | fvar w =>
      simp only [Expr.abstract1] at h
      by_cases hw : v = w
      · subst hw; simp at h; split at h <;> omega
      · simp [hw] at h
    | _ => simp [Expr.abstract1] at h
  | fvar u =>
    intro e' k h
    cases e' with
    | bvar i' =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u
      · subst hu; simp at h; split at h <;> omega
      · simp [hu] at h
    | fvar w =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u <;> by_cases hw : v = w <;> simp_all
    | _ =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u <;> simp [hu] at h
  | app f a ihf iha =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [ihf h.1, iha h.2]
  | lam n t b bi iht ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2]
  | forallE n t b bi iht ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2]
  | letE n t val b nd iht ihv ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihv h.2.2.1, ihb h.2.2.2.1, h.2.2.2.2]
  | mdata m b ih =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, ih h.2]
  | proj s i b ih =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, h.2.1, ih h.2.2]
  | _ =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try split at h) <;> simp_all

theorem Expr.abstractList_injective :
    ∀ {xs : List FVarId} {e e' : Expr} {k : Nat},
      e.abstractList xs k = e'.abstractList xs k → e = e'
  | [], _, _, _, h => by simpa using h
  | _ :: _, _, _, _, h => Expr.abstract1_injective (Expr.abstractList_injective h)


/-- An anonymous forall context is well formed when its domains are. -/
theorem abstractForallContext_wf_of_onCtx'
    {env : VEnv} {U : Nat} {domains : List VExpr}
    (H : OnCtx domains.reverse (env.IsType U)) :
    (abstractForallContext domains []).WF env U := by
  have go : ∀ domains : List VExpr, OnCtx domains (env.IsType U) →
      VLCtx.WF env U (domains.map fun type =>
        ((none, .vlam type) : Option (FVarId × List FVarId) × VLocalDecl)) := by
    intro domains Hdomains
    induction domains with
    | nil => trivial
    | cons domain domains ih =>
      refine ⟨ih Hdomains.1, nofun, ?_⟩
      show env.IsType U (VLCtx.toCtx _) domain
      rw [VLCtx.toCtx_map_anonymousLams]
      exact Hdomains.2
  simpa [abstractForallContext] using go domains.reverse H

theorem insertBinders_append' (Fs B : List VExpr) (m : Nat) :
    InductiveSignature.insertBinders (Fs ++ B) m =
      InductiveSignature.insertBinders Fs m ++
        (B.zipIdx Fs.length).map fun (e, k) => e.liftN m k := by
  simp [InductiveSignature.insertBinders, List.zipIdx_append]

theorem liftContextPrefix_reverse_reverse (l : List VExpr) (n : Nat) :
    (liftContextPrefix n l.reverse).reverse = InductiveSignature.insertBinders l n := by
  rw [insertBinders_eq_prefix]; rfl

/-- Translation-level inverse of `TrExprS.insertBeforeInner`. -/
theorem TrExprS.removeBeforeInner {env : VEnv} {Us : List Name} (henv : env.WF)
    {outer inserted inner : List VExpr} {source : Expr} {T : VExpr}
    (hwf : (abstractForallContext (outer ++ inserted ++
      InductiveSignature.insertBinders inner inserted.length) []).WF env Us.length)
    (H : TrExprS env Us (abstractForallContext (outer ++ inserted ++
      InductiveSignature.insertBinders inner inserted.length) [])
      (source.liftLooseBVars' inner.length inserted.length) T) :
    ∃ t, TrExprS env Us (abstractForallContext (outer ++ inner) []) source t ∧
      T = t.liftN inserted.length inner.length ∧
      (abstractForallContext (outer ++ inner) []).WF env Us.length := by
  have W := abstractForallContext.bvInsertBeforeInner outer inserted inner
  simp only [liftContextPrefix_reverse_reverse] at W
  obtain ⟨t, Ht, rfl⟩ := TrExprS.weakBV_inv_lift henv W hwf H rfl
  exact ⟨t, Ht, rfl, W.wf henv hwf⟩

/-- Remove two inserted groups: `G` directly below the current inner
telescope and `M` directly above the retained field prefix `Fs`. -/
theorem TrExprS.unliftStep {env : VEnv} {Us : List Name} (henv : env.WF)
    {PP M Fs G B0 : List VExpr} {source : Expr} {T : VExpr}
    (hwf : (abstractForallContext (PP ++ M ++ InductiveSignature.insertBinders Fs M.length ++ G ++
      InductiveSignature.insertBinders
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) G.length) []).WF
        env Us.length)
    (H : TrExprS env Us (abstractForallContext (PP ++ M ++
      InductiveSignature.insertBinders Fs M.length ++ G ++
      InductiveSignature.insertBinders
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) G.length) [])
      ((source.liftLooseBVars' (Fs.length + B0.length) M.length).liftLooseBVars'
        B0.length G.length) T) :
    ∃ t, TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0) []) source t ∧
      T = (t.liftN M.length (Fs.length + B0.length)).liftN G.length B0.length ∧
      (abstractForallContext (PP ++ Fs ++ B0) []).WF env Us.length := by
  have hlen : ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k).length = B0.length := by
    simp
  obtain ⟨t₁, H₁, rfl, hwf₁⟩ := TrExprS.removeBeforeInner (outer :=
    PP ++ M ++ InductiveSignature.insertBinders Fs M.length) (inserted := G) henv hwf
    (by rw [hlen]; exact H)
  have hins : InductiveSignature.insertBinders (Fs ++ B0) M.length =
      InductiveSignature.insertBinders Fs M.length ++
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) :=
    insertBinders_append' Fs B0 M.length
  have hctx : PP ++ M ++ InductiveSignature.insertBinders Fs M.length ++
      ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) =
      PP ++ M ++ InductiveSignature.insertBinders (Fs ++ B0) M.length := by
    rw [hins, List.append_assoc]
  rw [hctx] at H₁ hwf₁
  obtain ⟨t, Ht, rfl, hwf₀⟩ := TrExprS.removeBeforeInner (outer := PP) (inserted := M)
    (inner := Fs ++ B0) henv hwf₁ (by simpa using H₁)
  refine ⟨t, by simpa using Ht, by simp [hlen], by simpa using hwf₀⟩


theorem zipIdx_twoLift_eq (B0 : List VExpr) (pos m g : Nat) :
    B0.zipIdx.map (fun (e, k) => (e.liftN m (pos + k)).liftN g k) =
      InductiveSignature.insertBinders ((B0.zipIdx pos).map fun (e, k) => e.liftN m k) g := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i h₁ h₂
    simp [InductiveSignature.insertBinders, List.getElem_zipIdx]

/-- Remove both inserted groups from every binder of a telescope sitting
below them, one binder at a time. -/
theorem TrExprS.unliftTelescope {env : VEnv} {Us : List Name} (henv : env.WF)
    {PP M Fs G : List VExpr} (A : List VExpr) (src : Nat → Expr)
    (hwf : ∀ i, i ≤ A.length → (abstractForallContext
      (PP ++ M ++ InductiveSignature.insertBinders Fs M.length ++ G ++ A.take i) []).WF
        env Us.length)
    (H : ∀ i (hi : i < A.length), TrExprS env Us (abstractForallContext
      (PP ++ M ++ InductiveSignature.insertBinders Fs M.length ++ G ++ A.take i) [])
      (((src i).liftLooseBVars' (Fs.length + i) M.length).liftLooseBVars' i G.length) A[i]) :
    ∃ B0 : List VExpr, B0.length = A.length ∧
      A = B0.zipIdx.map (fun (e, k) => (e.liftN M.length (Fs.length + k)).liftN G.length k) ∧
      ∀ i (hi : i < B0.length),
        TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0.take i) []) (src i) B0[i] := by
  suffices h : ∀ i, i ≤ A.length → ∃ B0 : List VExpr, B0.length = i ∧
      A.take i = B0.zipIdx.map (fun (e, k) =>
        (e.liftN M.length (Fs.length + k)).liftN G.length k) ∧
      ∀ k (hk : k < B0.length),
        TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0.take k) []) (src k) B0[k] by
    obtain ⟨B0, hlen, htake, htr⟩ := h A.length (Nat.le_refl _)
    exact ⟨B0, hlen, by rw [← htake, List.take_length], htr⟩
  intro i
  induction i with
  | zero => intro _; exact ⟨[], rfl, by simp, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨B0, hlen, htake, htr⟩ := ih (by omega)
    subst hlen
    have hiA : B0.length < A.length := by omega
    have Hi := H B0.length hiA
    have hwfi := hwf B0.length (by omega)
    rw [htake, zipIdx_twoLift_eq] at Hi hwfi
    obtain ⟨t, Ht, hAt, -⟩ := TrExprS.unliftStep henv hwfi Hi
    refine ⟨B0 ++ [t], by simp, ?_, ?_⟩
    · rw [List.take_succ_eq_append_getElem hiA, htake, hAt]
      simp [List.zipIdx_append]
    · intro k hk
      by_cases hki : k < B0.length
      · rw [List.getElem_append_left hki, List.take_append_of_le_length (Nat.le_of_lt hki)]
        exact htr k hki
      · have hk' : k = B0.length := by simp at hk; omega
        subst hk'
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero, List.take_left']
        exact Ht

/-- Pointwise removal of both inserted groups from a list of translations in
the context extended by the whole telescope. -/
theorem TrExprS.unliftForall₂ {env : VEnv} {Us : List Name} (henv : env.WF)
    {PP M Fs G B0 : List VExpr}
    (hwf : (abstractForallContext (PP ++ M ++ InductiveSignature.insertBinders Fs M.length ++ G ++
      InductiveSignature.insertBinders
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) G.length) []).WF
        env Us.length) :
    ∀ (srcs : List Expr) (I : List VExpr),
    List.Forall₂ (TrExprS env Us (abstractForallContext (PP ++ M ++
      InductiveSignature.insertBinders Fs M.length ++ G ++
      InductiveSignature.insertBinders
        ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN M.length k) G.length) []))
      (srcs.map fun s => (s.liftLooseBVars' (Fs.length + B0.length) M.length).liftLooseBVars'
        B0.length G.length) I →
    ∃ indices : List VExpr,
      I = indices.map (fun e => (e.liftN M.length (Fs.length + B0.length)).liftN G.length
        B0.length) ∧
      List.Forall₂ (TrExprS env Us (abstractForallContext (PP ++ Fs ++ B0) [])) srcs indices
  | [], I, h => by cases h; exact ⟨[], rfl, .nil⟩
  | s :: srcs, I, h => by
    cases h with
    | cons hhead htail =>
      obtain ⟨t, Ht, rfl, -⟩ := TrExprS.unliftStep henv hwf hhead
      obtain ⟨rest, rfl, Hrest⟩ := TrExprS.unliftForall₂ henv hwf srcs _ htail
      exact ⟨t :: rest, rfl, .cons Ht Hrest⟩


/-- Closing a term that mentions only parameters and a field prefix over the
generator's hypothesis prefix, all fields and the outer binders is closing it
over the field prefix and the parameters, followed by two lifts: by the outer
non-parameter binders above the field prefix, and by the remaining fields and
hypotheses below it. -/
theorem Expr.closeShapeSource (X : Expr) (hyps F1 F2 P M : List FVarId) (d : Nat)
    (hscope : X.FVarsIn fun fv => fv ∈ F1 ∨ fv ∈ P)
    (hhyps : ∀ fv ∈ hyps, fv ∉ F1 ∧ fv ∉ P)
    (hF2 : ∀ fv ∈ F2, fv ∉ F1 ∧ fv ∉ P)
    (hfb : (F1 ++ F2).Nodup) (hPM : (P ++ M).Nodup) :
    ((X.abstractList hyps d).abstractList (F1 ++ F2) (hyps.length + d)).abstractList (P ++ M)
        (F1.length + F2.length + hyps.length + d) =
      (((X.abstractList F1 d).abstractList P (F1.length + d)).liftLooseBVars'
        (F1.length + d) M.length).liftLooseBVars' d (F2.length + hyps.length) := by
  have h1 : X.abstractList hyps d = X.liftLooseBVars' d hyps.length := by
    apply Lean4Lean.FVarsIn.abstractList_eq_liftLooseBVars
    apply hscope.mono
    intro fv hfv hmem
    rcases hfv with h | h
    · exact (hhyps fv hmem).1 h
    · exact (hhyps fv hmem).2 h
  have h2 := Expr.liftLooseBVars'_abstractList_add X (F1 ++ F2) d d hyps.length
    (Nat.le_refl _) hfb
  have hY := Lean4Lean.FVarsIn.abstractList_not (xs := F1) (k := d) hscope
  have h3 : X.abstractList (F1 ++ F2) d =
      (X.abstractList F1 d).liftLooseBVars' d F2.length := by
    rw [Expr.abstractList_append]
    apply Lean4Lean.FVarsIn.abstractList_eq_liftLooseBVars
    apply hY.mono
    intro fv hfv hmem
    rcases hfv with ⟨h | h, hn⟩
    · exact hn h
    · exact (hF2 fv hmem).2 h
  have h4 := Expr.liftLooseBVars'_abstractList_add (X.abstractList F1 d) (P ++ M) d
    (F1.length + d) (F2.length + hyps.length) (by omega) hPM
  have hZ := Lean4Lean.FVarsIn.abstractList_not (xs := P) (k := F1.length + d) hY
  have h5 : (X.abstractList F1 d).abstractList (P ++ M) (F1.length + d) =
      ((X.abstractList F1 d).abstractList P (F1.length + d)).liftLooseBVars'
        (F1.length + d) M.length := by
    rw [Expr.abstractList_append]
    apply Lean4Lean.FVarsIn.abstractList_eq_liftLooseBVars
    apply hZ.mono
    intro fv hfv _
    rcases hfv with ⟨⟨h | h, hn⟩, hp⟩
    · exact hn h
    · exact hp h
  rw [h1, Nat.add_comm hyps.length d, h2, h3, Lean.Expr.liftLooseBVars'_liftLooseBVars',
    show F1.length + F2.length + hyps.length + d = F1.length + d + (F2.length + hyps.length) by
      omega, h4, h5]


theorem Expr.forallDomainList_forallDomainsOnly :
    ∀ (n : Nat) (e : Expr), Expr.forallDomainList n (Expr.forallDomainsOnly n e) =
      Expr.forallDomainList n e
  | 0, _ => rfl
  | n + 1, e => by
    cases e <;> simp [Expr.forallDomainsOnly, Expr.forallDomainList,
      Expr.forallDomainList_forallDomainsOnly n]

theorem Expr.forallDomainList_fvarsIn {P : FVarId → Prop} :
    ∀ (n : Nat) {e : Expr}, FVarsIn P e → ∀ d ∈ Expr.forallDomainList n e, FVarsIn P d
  | 0, _, _ => by simp [Expr.forallDomainList]
  | n + 1, e, h => by
    cases e with
    | forallE name dom body bi =>
      intro d hd
      simp only [Expr.forallDomainList, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact Expr.forallDomainList_fvarsIn n h.2 d hd
    | _ => simp [Expr.forallDomainList]

theorem InductiveSignature.insertBinders_take (l : List VExpr) (n k : Nat) :
    (InductiveSignature.insertBinders l n).take k =
      InductiveSignature.insertBinders (l.take k) n := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i _ _
    simp [InductiveSignature.insertBinders]

@[simp] theorem InductiveSignature.insertBinders_zero (l : List VExpr) :
    InductiveSignature.insertBinders l 0 = l := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i _ _
    simp [InductiveSignature.insertBinders]

/-- A selected recursive field is one of the opened field variables. -/
theorem RecInfoMinorTypeShape.recursiveField_pos (S : RecInfoMinorTypeShape)
    {env : VEnv} {decl : VInductDecl} {uvars : Nat}
    {sel : List (RecursorRecursiveDomainAt env decl uvars)}
    (Hsel : RecursorFieldSelectionsAt env decl uvars S.fields S.recursiveFields sel)
    (j : Nat) (hj : j < S.recursiveFields.size) :
    ∃ pos, ∃ hpos : pos < S.fields_bound.fvars.length,
      S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) := by
  have hF := Hsel.arguments_at_positions
  have hlen := Lean4Lean.List.Forall₂.length_eq hF
  have hjSel : j < sel.length := by rw [hlen]; simpa using hj
  obtain ⟨hp, hget⟩ := List.Forall₂.getElem hF j hjSel (by simpa using hj)
  have hsize := S.fields_bound.length_fvars
  refine ⟨sel[j].fieldIndex, by omega, ?_⟩
  rw [getElem!_pos S.recursiveFields j hj]
  have h1 : S.recursiveFields[j] = S.fields[sel[j].fieldIndex] := by simpa using hget
  rw [h1]
  have h2 : ∀ (xs : Array Expr) (h : sel[j].fieldIndex < xs.size),
      xs = (S.fields_bound.fvars.map Expr.fvar).toArray →
      xs[sel[j].fieldIndex] = .fvar (S.fields_bound.fvars[sel[j].fieldIndex]'(by omega)) := by
    intro xs h hxs; subst hxs; simp
  exact h2 _ hp S.fields_bound.expressions


theorem OnCtx.reverse_append_take {P : List VExpr → VExpr → Prop} {l₁ l₂ : List VExpr}
    (h : OnCtx (l₁ ++ l₂).reverse P) (i : Nat) : OnCtx (l₁ ++ l₂.take i).reverse P := by
  have : (l₁ ++ l₂).reverse = (l₂.drop i).reverse ++ (l₁ ++ l₂.take i).reverse := by
    rw [← List.reverse_append, List.append_assoc, List.take_append_drop]
  rw [this] at h
  exact OnCtx.append_right h

theorem OnCtx.reverse_append_getElem {P : List VExpr → VExpr → Prop} {l₁ l₂ : List VExpr}
    (h : OnCtx (l₁ ++ l₂).reverse P) (i : Nat) (hi : i < l₂.length) :
    P (l₁ ++ l₂.take i).reverse l₂[i] := by
  have h' := OnCtx.reverse_append_take h (i + 1)
  rw [List.take_succ_eq_append_getElem hi, ← List.append_assoc, List.reverse_append] at h'
  exact h'.2

/-- The `j`-th induction hypothesis of a minor premise of the checked recursor
type, unlifted to the small context of its recursive field.

For the origin `O` retained by the rule rows and the recursive field at
position `pos`, the hypothesis is the generator's `underFields` embedding of a
binder telescope `binders` and of an index list `indices`, applied to the
owner's motive variable and the recursive field variable.  Each `binders[i]`
translates, in `parameters ++ sourceFields.take pos ++ binders.take i`, the
`i`-th literal argument domain `O.argDomains[i]!` closed over the fields before
`pos` (at depth `i`) and the parameters (at depth `pos + i`); the indices are
the closed exposed indices of `O`, closed the same way at depth `O.args.size`.
The generator-context sources of `recursorTelescope_hypothesisDomains` are
exactly the lifts of these sources (`Expr.closeShapeSource`). -/
theorem CompletedRecursorConstruction.recursorTelescope_hypothesisUnlift
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : GeneratedRecursorTelescopeTranslation R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : BoundFVarDeclarationAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let sourceFields := (H.sourceFields mowner hmowner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
    let nmot := (H.recInfos.map (·.motive)).size
    let fields := InductiveSignature.insertBinders sourceFields (nmot + minorIdx)
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat) (hj : j < S.hypotheses.size),
      ∃ (origins : RecInfoMinorHypothesisTypeOrigins S.sourceFullContext S.recursiveFields
          S.hypotheses)
        (root : AddInductive.Context) (sourceType : Expr)
        (O : RecInfoMinorHypothesisTypeOrigin origins.stats origins.recInfos root
          (S.recursiveFields[j]!) sourceType)
        (pos : Nat) (hpos : pos < S.fields_bound.fvars.length) (binders indices : List VExpr),
        S.hypothesis_type_origins = some origins ∧ origins.stats = stats ∧
        origins.recInfos.map (·.motive) = H.recInfos.map (·.motive) ∧
        S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) ∧
        binders.length = O.args.size ∧ O.ownerIdx < H.recInfos.size ∧
        hyps[j]'(by rw [hhyps]; exact hj) =
          VExpr.wrapForalls
            (binders.zipIdx.map fun (e, i) =>
              InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx) i)
            (.app
              (VExpr.mkApps (.bvar (S.fields.size + j + O.args.size + minorIdx +
                  (nmot - 1 - O.ownerIdx)))
                (indices.map fun e =>
                  InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx)
                    O.args.size))
              (VExpr.mkApps (.bvar (j + O.args.size + (S.fields.size - 1 - pos)))
                (InductiveSignature.vars O.args.size 0))) ∧
        (∀ (i : Nat) (hi : i < binders.length),
          TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ binders.take i) [])
            ((O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
              H.params.fvars (pos + i))
            (binders[i]'hi)) ∧
        List.Forall₂
          (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
              sourceFields.take pos ++ binders) []))
          ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map fun e =>
            ((e.abstractN O.arguments_bound.fvars).abstractList
              (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
                (pos + O.args.size))
          indices ∧
        (H.recInfos[mowner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).args = O.args ∧
        (H.recInfos[mowner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).lctx =
          O.current.lctx ∧
        (H.recInfos[mowner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).targetIndices =
          O.exposedType.getAppArgs[origins.stats.params.size:] ∧
        (H.recInfos[mowner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).targetTypeIdx =
          O.ownerIdx ∧
        (H.recInfos[mowner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).major =
          S.recursiveFields[j]! ∧
        (H.recInfos[mowner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).template =
          O.current.lctx.mkLambda O.args
            ((mkAppN (.bvar O.args.size) O.exposedType.getAppArgs[origins.stats.params.size:]).app
              (mkAppN S.recursiveFields[j]! O.args)) ∧
        O.argDomains =
          Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)) ∧
        ExprArrayFVarIds O.args = O.arguments_bound.fvars := by
  intro S sourceFields nmot fields hyps res hhyps hminorEq j hj
  -- The retained rows for this minor.
  obtain ⟨-, -, -, -, -, origins₁, -, horig₁, -, -, Hcalls⟩ :=
    H.blueprints.entry mowner hmowner localIndex hlocal
  obtain ⟨⟨origins, horig, hstats, hmotives, F, hparams, depth', -, _, Hsel, -, -, -, -, -, -, -,
    -, -, ⟨HcallAt⟩⟩⟩ := H.blueprintSemantics.entry mowner hmowner localIndex hlocal
  have : origins₁ = origins := Option.some.inj (horig₁.symm.trans horig)
  subst this
  obtain ⟨originRoot, sourceType, O, D, -, hDtype, hcall⟩ := Hcalls.entry j hj
  obtain ⟨_, Rorigin, prior, Hprior, -, -, ⟨Csem⟩⟩ := HcallAt.entry j hj
  obtain ⟨Sc, hscope, -, hSreplay⟩ := Csem.semantic indTypes (H.recInfos.flatMap (·.minors)) []
  have hjR : j < S.recursiveFields.size := S.hypotheses_size ▸ hj
  obtain ⟨pos, hpos, hfield⟩ := S.recursiveField_pos Hsel j hjR
  have howner' : O.ownerIdx < H.recInfos.size := by
    have h := Csem.owner_lt
    rw [hcall] at h
    simpa using h
  have hoLt : O.ownerIdx < origins₁.recInfos.size := by
    have h := congrArg Array.size hmotives
    simp only [Array.size_map] at h
    omega
  -- The two replay traces agree.
  have hreplay : O.replayTrace S.fields_bound.fvars =
      Sc.generated.replayTrace S.fields_bound.fvars := by
    rw [O.replayTrace_eq_blueprint _ hcall hoLt, hmotives, hSreplay]
  obtain ⟨A, I, hA, hEq, HI, HA⟩ := H.recursorTelescope_hypothesisDomains howner T minorIdx D₀
    mowner hmowner localIndex hlocal hD hyps res hhyps hminorEq j origins₁ hmotives O D hDtype
    howner' pos hpos hfield
  -- Abbreviations.
  have hnf : S.fields_bound.fvars.length = S.fields.size := S.fields_bound.length_fvars
  have hposf : pos < S.fields.size := by omega
  have hfR : F.fieldsRecent.fvars = S.fields_bound.fvars :=
    F.fieldsRecent.toBoundFVarArray.exprArrayFVarIds.symm.trans S.fields_bound.exprArrayFVarIds
  have hPids : ExprArrayFVarIds stats.params = H.params.fvars := H.params.exprArrayFVarIds
  have hrootScope : ∀ fv, Sc.rootScope fv ↔
      fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars := by
    intro fv
    rw [hscope, hfield]
    simp only [RecursorFieldPrefixScope, recursorFVarId, hfR,
      List.Nodup.idxOf_getElem S.fields_nodup pos hpos, hPids]
  -- The call-local argument telescope of the semantic call mentions only the
  -- parameters and the fields before the recursive field.
  have hScT : (Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero)).FVarsIn
      (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars) := by
    let Rc := Sc.current_context
    have hargs : Sc.generated.localArgs.toList = Sc.recent.fvars.map Expr.fvar := by
      have key : ∀ (xs : Array Expr) (fvs : List FVarId), xs = (fvs.map Expr.fvar).toArray →
          xs.toList = fvs.map Expr.fvar := by
        intro xs fvs h; subst h; simp
      exact key _ _ Sc.recent.expressions
    have hrev : Rc.mlctx.fvarRevList Sc.generated.localArgs.size Sc.recent.size_le =
        Sc.recent.fvars.reverse := by
      have h1 := Sc.recent.reverse_eq
      rw [hargs, ← List.map_reverse] at h1
      have hinj : ∀ (l₁ l₂ : List FVarId), l₁.map Expr.fvar = l₂.map Expr.fvar → l₁ = l₂ := by
        intro l₁ l₂ h
        induction l₁ generalizing l₂ with
        | nil => cases l₂ <;> simp_all
        | cons a l ih =>
          cases l₂ with
          | nil => simp at h
          | cons b l' => simp only [List.map_cons, List.cons.injEq, Expr.fvar.injEq] at h; rw [h.1, ih _ h.2]
      exact (hinj _ _ h1).symm
    have hmk : Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero) =
        Rc.mlctx.mkForall Sc.generated.localArgs.size Sc.recent.size_le (.sort .zero) := by
      rw [← Rc.lctx_eq]
      exact Rc.mlctx_wf.mkForall_eq _ _ Sc.recent.reverse_eq (by simp [Closed])
    rw [hmk]
    apply MLCtxOnlyLams.mkForall_fvarsIn_upset Rc.onlyLams Rc.mlctx_wf
    · have hpred : (fun fv => fv ∈ Rc.mlctx.fvarRevList Sc.generated.localArgs.size
            Sc.recent.size_le ∨ (fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars)) =
          (fun fv => fv ∈ Sc.recent.fvars ∨ Sc.rootScope fv) := by
        funext fv
        rw [hrev, hrootScope]
        simp
      rw [hpred]
      exact Sc.current_scope_up
    · simp [FVarsIn, Level.hasMVar']
  -- The replayed argument telescopes coincide.
  have hOT : O.current.lctx.mkForall O.args (.sort .zero) =
      Sc.generated.current.lctx.mkForall Sc.generated.localArgs (.sort .zero) := by
    have h := congrArg RecursorLoopUArgsTrace.localTelescope hreplay
    simp only [RecInfoMinorHypothesisTypeOrigin.replayTrace,
      BoundGeneratedRecursiveCall.replayTrace] at h
    exact Expr.abstractList_injective h
  have hna : O.args.size = Sc.generated.localArgs.size :=
    congrArg RecursorLoopUArgsTrace.localArity hreplay
  have hnaO : O.arguments_bound.fvars.length = O.args.size := O.arguments_bound.length_fvars
  have hargsSc : Sc.generated.arguments_bound.fvars = Sc.recent.fvars :=
    Sc.generated.arguments_bound.toBoundFVarArray.exprArrayFVarIds.symm.trans
      Sc.recent.toBoundFVarArray.exprArrayFVarIds
  have hnaSc : Sc.generated.arguments_bound.fvars.length = Sc.generated.localArgs.size :=
    Sc.generated.arguments_bound.length_fvars
  -- Every argument domain mentions only parameters and earlier fields.
  have hdom : O.argDomains =
      Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)) := by
    have key : ∀ t body, t = O.current.lctx.mkForall O.args body →
        Expr.forallDomainList O.args.size t =
          Expr.forallDomainList O.args.size (O.current.lctx.mkForall O.args (.sort .zero)) := by
      intro t body ht
      rw [ht, ← Expr.forallDomainList_forallDomainsOnly O.args.size (O.current.lctx.mkForall _ body),
        O.arguments_bound.toBoundFVarArray.forallDomainsOnly O.current_wf O.arguments_bound.nodup]
    exact key _ _ O.type_eq
  have hArgScope : ∀ i, i < O.args.size → (O.argDomains[i]!).FVarsIn
      (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars) := by
    intro i hi
    have hi' : i < O.argDomains.length := by rw [O.argDomains_length]; exact hi
    have hall : ∀ d ∈ O.argDomains, d.FVarsIn
        (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars) := by
      rw [hdom]
      exact Expr.forallDomainList_fvarsIn _ (hOT ▸ hScT)
    rw [getElem!_pos O.argDomains i hi']
    exact hall _ (List.getElem_mem hi')
  -- Every exposed index, closed over its own arguments, mentions only parameters and earlier
  -- fields, and abstraction by `abstractN` agrees with `abstractList` on it.
  have hexposedClosed : Closed Sc.generated.exposedType 0 := by
    have h := Sc.exposed_translation.closed
    rwa [Sc.current_context.mlctx.noBV] at h
  have hIdxScope : ∀ e ∈ (O.exposedType.getAppArgs[origins₁.stats.params.size:] :
      Array Expr).toList,
      e.abstractN O.arguments_bound.fvars = e.abstractList O.arguments_bound.fvars ∧
      (e.abstractN O.arguments_bound.fvars).FVarsIn
        (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars) := by
    intro e he
    have hind := congrArg (fun t => t.indices.toList) hreplay
    simp only [RecInfoMinorHypothesisTypeOrigin.replayTrace,
      BoundGeneratedRecursiveCall.replayTrace, Array.toList_map] at hind
    have hmem := List.mem_map_of_mem
      (f := fun index => (index.abstractList O.arguments_bound.fvars).abstractList
        S.fields_bound.fvars O.args.size) he
    rw [hind] at hmem
    obtain ⟨e', he', heq⟩ := List.mem_map.1 hmem
    rw [← hna] at heq
    have heq' := Expr.abstractList_injective heq
    rw [Expr.getAppArgs_slice_toList] at he'
    have he'args := List.mem_of_mem_drop he'
    have hscope' := Lean4Lean.FVarsIn.getAppArgsList Sc.exposed_scope he'args
    have hclosed' := Closed.getAppArgsList hexposedClosed he'args
    have hclosedAbs : Closed (e.abstractList O.arguments_bound.fvars 0)
        (0 + O.arguments_bound.fvars.length) := by
      rw [← heq', hnaO, hna, ← hnaSc]
      simpa using Closed.abstractList_at (depth := 0) (outer := 0)
        (fvars := Sc.generated.arguments_bound.fvars) (by simpa using hclosed')
    have hclosedE : Closed e 0 := Expr.closed_of_abstractList hclosedAbs
    have hN : e.abstractN O.arguments_bound.fvars = e.abstractList O.arguments_bound.fvars :=
      Expr.abstractN_eq_abstractList_of_closed O.arguments_bound.nodup hclosedE
    refine ⟨hN, ?_⟩
    rw [hN, ← heq']
    have h := Lean4Lean.FVarsIn.abstractList_not (xs := Sc.generated.arguments_bound.fvars)
      (k := 0) hscope'
    apply h.mono
    intro fv hfv
    rcases hfv with ⟨h1 | h1, h2⟩
    · exact absurd (hargsSc ▸ h1) h2
    · exact (hrootScope fv).1 h1
  -- Distinctness of the closed variable groups.
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hPM : (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx)).Nodup := by
    rw [← List.append_assoc]
    apply List.Nodup.sublist _ houter
    exact List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _)
  have hfb : (S.fields_bound.fvars.take pos ++ S.fields_bound.fvars.drop pos).Nodup := by
    rw [List.take_append_drop]; exact S.fields_nodup
  have hfieldsOuter : ∀ fv ∈ S.fields_bound.fvars, fv ∉ H.params.fvars := by
    intro fv hfv hP
    apply H.blueprints.fields_outer_fresh mowner hmowner localIndex hlocal fv hfv
    rw [hPids]
    exact List.mem_append_left _ (List.mem_append_left _ hP)
  have hhypsD : ∀ fv ∈ S.hypotheses_bound.fvars.take j,
      fv ∉ S.fields_bound.fvars.take pos ∧ fv ∉ H.params.fvars := by
    intro fv hfv
    have hfv' := List.mem_of_mem_take hfv
    refine ⟨fun h => S.hypotheses_fields_fresh fv hfv' (List.mem_of_mem_take h), fun hP => ?_⟩
    have h := origins₁.hypotheses_outer_fresh fv (List.mem_append_left _ (by rw [hstats, hPids]; exact hP))
    rw [S.hypotheses_bound.exprArrayFVarIds] at h
    exact h hfv'
  have hF2D : ∀ fv ∈ S.fields_bound.fvars.drop pos,
      fv ∉ S.fields_bound.fvars.take pos ∧ fv ∉ H.params.fvars := by
    intro fv hfv
    refine ⟨fun h => ?_, hfieldsOuter fv (List.mem_of_mem_drop hfv)⟩
    exact (List.nodup_append.1 hfb).2.2 fv h fv hfv rfl
  -- Lengths.
  have hminorT : minorIdx < T.minors.length := by rw [T.minors_length]; exact D₀.inBounds
  have hjH : j ≤ S.hypotheses_bound.fvars.length := by
    rw [S.hypotheses_bound.length_fvars]; omega
  have hhypsLen : (S.hypotheses_bound.fvars.take j).length = j := by
    rw [List.length_take]; omega
  have hMLen : (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx).length =
      nmot + minorIdx := by
    rw [List.length_append, H.bindings.motives.length_fvars, List.length_take,
      H.bindings.flatMinors.length_fvars]
    have := D₀.inBounds
    simp only [nmot]
    omega
  have hsfLen : sourceFields.length = S.fields.size := by
    simp only [sourceFields, List.length_map]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  -- Source coincidences: the generator's closed sources are lifts of the small ones.
  have hsrc : ∀ (X : Expr) (d : Nat), X.FVarsIn
        (fun fv => fv ∈ S.fields_bound.fvars.take pos ∨ fv ∈ H.params.fvars) →
      ((X.abstractList (S.hypotheses_bound.fvars.take j) d).abstractList S.fields_bound.fvars
          (j + d)).abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx) (S.fields.size + j + d) =
        (((X.abstractList (S.fields_bound.fvars.take pos) d).abstractList H.params.fvars
          (pos + d)).liftLooseBVars' (pos + d) (nmot + minorIdx)).liftLooseBVars' d
            (S.fields.size - pos + j) := by
    intro X d hX
    have h := Expr.closeShapeSource X (S.hypotheses_bound.fvars.take j)
      (S.fields_bound.fvars.take pos) (S.fields_bound.fvars.drop pos) H.params.fvars
      (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx) d hX hhypsD hF2D
      hfb hPM
    rw [List.take_append_drop, ← List.append_assoc, hhypsLen, hMLen, List.length_take,
      List.length_drop, hnf, Nat.min_eq_left (by omega)] at h
    rw [show S.fields.size + j + d = pos + (S.fields.size - pos) + j + d by omega, h]
  -- Well-formedness of the generator contexts below the hypothesis.
  have henv : R.context.venv.WF := by rw [← H.recursorEnv]; exact H.recursorWF.checking.tr.wf
  have hOnA : OnCtx (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++
      A).reverse (R.context.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
    have Hty := T.typed.isType
    rw [T.target_eq] at Hty
    obtain ⟨hon, -⟩ := VEnv.IsType.wrapForalls_inv henv.ordered (ctx := []) trivial Hty
    rw [List.append_nil] at hon
    have hon' : OnCtx ((T.params ++ T.motives) ++ (T.minors ++ (T.indices ++ T.major))).reverse
        (R.context.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
      simpa only [List.append_assoc] using hon
    have hlenM : minorIdx < (T.minors ++ (T.indices ++ T.major)).length := by
      simp only [List.length_append]; omega
    have hMin := OnCtx.reverse_append_getElem hon' minorIdx hlenM
    have hctx := OnCtx.reverse_append_take hon' minorIdx
    rw [List.take_append_of_le_length (by omega)] at hMin hctx
    rw [List.getElem_append_left hminorT, hminorEq, ← VExpr.wrapForalls_append] at hMin
    obtain ⟨hon2, -⟩ := VEnv.IsType.wrapForalls_inv henv.ordered hctx hMin
    rw [← List.reverse_append] at hon2
    have hon2' : OnCtx ((T.params ++ T.motives ++ T.minors.take minorIdx ++ fields) ++ hyps).reverse
        (R.context.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
      simpa only [List.append_assoc] using hon2
    have hHj := OnCtx.reverse_append_getElem hon2' j (by omega)
    have hctx2 := OnCtx.reverse_append_take hon2' j
    rw [hEq] at hHj
    obtain ⟨hon3, -⟩ := VEnv.IsType.wrapForalls_inv henv.ordered hctx2 hHj
    rw [← List.reverse_append] at hon3
    exact hon3
  have hwfBig : ∀ i, i ≤ A.length → (abstractForallContext
      (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++ A.take i)
        []).WF R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams).length :=
    fun i _ => abstractForallContext_wf_of_onCtx' (OnCtx.reverse_append_take hOnA i)
  -- Remove the inserted groups from the argument telescope.
  let Mv := T.motives ++ T.minors.take minorIdx
  let Fs := sourceFields.take pos
  let G := fields.drop pos ++ hyps.take j
  have hMv : Mv.length = nmot + minorIdx := by
    simp only [Mv, List.length_append, T.motives_length, List.length_take, T.minors_length]
    have := D₀.inBounds
    simp only [nmot]
    omega
  have hFs : Fs.length = pos := by simp only [Fs, List.length_take, hsfLen]; omega
  have hG : G.length = S.fields.size - pos + j := by
    simp only [G, fields, InductiveSignature.insertBinders, List.length_append, List.length_drop,
      List.length_map, List.length_zipIdx, hsfLen, List.length_take]
    omega
  have hctxEq : ∀ X : List VExpr,
      T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++ X =
        T.params ++ Mv ++ InductiveSignature.insertBinders Fs Mv.length ++ G ++ X := by
    intro X
    have hf : fields = InductiveSignature.insertBinders Fs Mv.length ++ fields.drop pos := by
      rw [hMv, ← InductiveSignature.insertBinders_take]
      exact (List.take_append_drop _ _).symm
    conv => lhs; rw [hf]
    simp only [G, Mv, List.append_assoc]
  obtain ⟨B0, hB0len, hAeq, HB0⟩ := TrExprS.unliftTelescope henv (PP := T.params) (M := Mv)
    (Fs := Fs) (G := G) A
    (fun i => (O.argDomains[i]!.abstractList (S.fields_bound.fvars.take pos) i).abstractList
      H.params.fvars (pos + i))
    (fun i hi => by rw [← hctxEq]; exact hwfBig i hi)
    (fun i hi => by
      have h := HA i hi
      rw [hsrc _ i (hArgScope i (hA ▸ hi))] at h
      rw [← hctxEq, hFs, hMv, hG]
      exact h)
  -- Remove the inserted groups from the exposed indices.
  have hAfull : A = InductiveSignature.insertBinders
      ((B0.zipIdx Fs.length).map fun (e, k) => e.liftN Mv.length k) G.length := by
    rw [hAeq, zipIdx_twoLift_eq]
  have hwfI := hwfBig A.length (Nat.le_refl _)
  rw [List.take_length, hctxEq] at hwfI
  conv at hwfI => rw [hAfull]
  have hB0na : B0.length = O.args.size := hB0len.trans hA
  have HI' := HI
  rw [hctxEq] at HI'
  conv at HI' => rw [hAfull]
  have hIsrc : ((O.exposedType.getAppArgs[origins₁.stats.params.size:] : Array Expr).toList.map
      fun e => (((e.abstractN O.arguments_bound.fvars).abstractList
        (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
          (j + O.args.size)).abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx) (S.fields.size + j + O.args.size)) =
      ((O.exposedType.getAppArgs[origins₁.stats.params.size:] : Array Expr).toList.map
        fun e => ((e.abstractN O.arguments_bound.fvars).abstractList
          (S.fields_bound.fvars.take pos) O.args.size).abstractList H.params.fvars
            (pos + O.args.size)).map
        (fun s => (s.liftLooseBVars' (Fs.length + B0.length) Mv.length).liftLooseBVars'
          B0.length G.length) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    rw [hsrc _ _ (hIdxScope e he).2, hFs, hMv, hG, hB0na]
  rw [hIsrc] at HI'
  obtain ⟨indices, hIeq, HIsmall⟩ := TrExprS.unliftForall₂ henv hwfI _ I HI'
  -- Assemble.
  have hparamsT := H.recursorTelescope_params T
  have hunder : ∀ (e : VExpr) (k : Nat),
      (e.liftN Mv.length (Fs.length + k)).liftN G.length k =
        InductiveSignature.Instance.underFields e pos S.fields.size j (nmot + minorIdx) k := by
    intro e k
    simp only [InductiveSignature.Instance.underFields]
    rw [hFs, hMv, hG, VExpr.liftN'_comm _ _ _ _ _ (Nat.le_add_left k pos)]
    congr 1
    omega
  refine ⟨origins₁, originRoot, sourceType, O, pos, hpos, B0, indices, horig, hstats, hmotives,
    hfield, hB0na, howner', ?_, ?_, ?_, by rw [hcall], by rw [hcall], by rw [hcall], by rw [hcall],
    by rw [hcall], by rw [hcall], hdom, O.arguments_bound.toBoundFVarArray.exprArrayFVarIds⟩
  · rw [hEq, hIeq, hAeq]
    simp only [hunder, hB0na]
    rfl
  · intro i hi
    have h := HB0 i hi
    rwa [hparamsT] at h
  · rw [hparamsT] at HIsmall
    exact HIsmall

end Lean4Lean.VerifyInductive
