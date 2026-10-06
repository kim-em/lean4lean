import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Interp
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Definitions

/-! # Soundness of the observation model for rule-free environments (milestone M2)

`theorem sound`: for a strong derivation `Γ ⊢ t ≡ t' : T` in an environment whose rules
are all delta rules of definitions and which has no projections or eliminators
(`DefsOnly`, stage A1 of section 10.2 of the notes; `NoRules` is the rule-free special
case), and every pair of related
anchors `σ ≡ σ'` from `Γ` into a well-formed target context `Δ` with observation sets `S`
typed for both anchors:

* every observation of `t` under `(σ, S)` is subsumed by one of `t'` under `(σ', S)`, and
  conversely (`Ob.Sub`, i.e. `Obs t ⊆ ↑Obs t'`);
* every observation of `t` (under `σ`) and of `t'` (under `σ'`) is typed at observations of
  `T` (the typing invariant, proved simultaneously).

Relating two anchors (rather than one) is what lets the `beta` case change the
representative of a key class: the key's representative and the actual argument are only
definitionally equal (`docs/inductives/PHASE1B_NOTES.md`, section 10).

The cases follow section 9.2 of the notes: `appDF` uses the typing invariant of the
function to identify the domain class of its observations (`app_typed`, `Obs.piDom_mem`);
`lamDF`/`forallEDF` extend the anchors by a representative of the key class; `beta` uses
compactness, monotonicity and the substitution lemma; `eta` uses the typing invariant of
`e : Pi A B` (its observations are `app` observations with typed keys) and key enlargement
(`≼`); `proofIrrel` uses `TypedOb.not_prop`; `defeqDF` transfers typing along the
inclusions given by the type equality; `sortDF`/`constDF` see levels only through
`VLevel.eval`, and at a defined constant on level invariance of the value (`Obs.lvEq`);
`extra` is the delta clause in both directions, using `DefRules` (the rule of a defined
constant is unique and its type is the constant's). The other rule cases are vacuous
under `DefsOnly`. -/

namespace Lean4Lean
namespace VEnv

/-- An environment without definitional rules, projections or eliminators: the
milestone-M2 setting, in which every constant is rigid. -/
structure NoRules (env : VEnv) : Prop where
  defeqs : ∀ df, ¬ env.defeqs df
  projections : ∀ n p, ¬ env.projections n p
  eliminators : ∀ b s, ¬ env.eliminators b s

/-- Stage A1 (`docs/inductives/PHASE1B_NOTES.md`, section 10.2): every rule is the delta
rule of a definition (its left-hand side is a bare constant), and there are no
projections or eliminators. -/
structure DefsOnly (env : VEnv) : Prop where
  defeqs : ∀ df, env.defeqs df → ∃ n ls, df.lhs = .const n ls
  projections : ∀ n p, ¬ env.projections n p
  eliminators : ∀ b s, ¬ env.eliminators b s

theorem NoRules.defsOnly {env : VEnv} (h : env.NoRules) : env.DefsOnly :=
  ⟨fun df hdf => absurd hdf (h.defeqs df), h.projections, h.eliminators⟩

namespace Model

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The soundness statement for one derivation `Γ ⊢ t ≡ t' : T`. -/
def SoundAt (Γ : List VExpr) (t t' T : VExpr) : Prop :=
  ∀ σ σ' S, Ctx.SubstEq env U Δ σ σ' Γ → TV env U Δ Γ σ S → TV env U Δ Γ σ' S →
    Ob.Sub (Obs env U Δ σ S t) (Obs env U Δ σ' S t') ∧
    Ob.Sub (Obs env U Δ σ' S t') (Obs env U Δ σ S t) ∧
    (∀ o, Obs env U Δ σ S t o → TypedAt env U Δ σ S T o) ∧
    (∀ o, Obs env U Δ σ' S t' o → TypedAt env U Δ σ' S T o)

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Typing helpers -/

theorem TypedElCls.eq_of_mem' (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    c = ElCls env U Δ (TyCls env U Δ X₀) y :=
  let ⟨_, _, _, h⟩ := hc.mem henv hΔ hy; h

theorem imax_eval_zero {a b : Nat} (h : Lean.Nat.imax a b = 0) : b = 0 := by
  unfold Lean.Nat.imax at h
  split at h
  · assumption
  · rename_i hb
    exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hb) (Nat.le_max_right a b)))

theorem typedAt_sort_iff : TypedAt env U Δ σ S (.sort l) o ↔ TypedOb env U Δ o [.sort l.eval] := by
  constructor
  · rintro ⟨τs, h1, h2⟩
    exact h2.mono fun τ hτ => by rw [Obs.sort_mem (h1 τ hτ)]; exact List.mem_singleton_self _
  · intro h
    refine ⟨_, fun τ hτ => ?_, h⟩
    rw [List.mem_singleton] at hτ; subst hτ; exact .sort

/-- Observations typed at a Pi type are `app` observations. -/
theorem typed_pi_app (H : TypedOb env U Δ o τs) (hτ : ∀ τ ∈ τs, Obs' σ S (.forallE A B) τ) :
    ∃ D c K p, o = .app D c K p := by
  cases H with
  | app => exact ⟨_, _, _, _, rfl⟩
  | sort h | piDom h | piDomOb h | piCod h | piCodOb h | rigid h | rigidArg h | rigidArgOb h =>
    nomatch hτ _ h

/-- Enlarging the keys of a typed `app` observation by typed keys keeps it typed. -/
theorem TypedOb.app_enlarge (H : TypedOb env U Δ (.app D c K₁ p) τs) (hKK : Covers K K₁)
    (hd : ∀ x ∈ τd, Ob.piDomOb x ∈ τs) (hk : ∀ k ∈ K, TypedOb env U Δ k τd) :
    TypedOb env U Δ (.app D c K p) τs := by
  cases H with
  | app hD _ _ hc hcod hp =>
    exact .app hD hd hk hc (fun x hx => let ⟨K₀, h1, h2⟩ := hcod x hx; ⟨K₀, h1, hKK.trans h2⟩) hp

/-- The `app` observations of a lambda are typed at its Pi type. -/
theorem lam_typed (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c)
    (hK : ∀ k ∈ K, TypedAt env U Δ σ S A k) (hy : c y)
    (hp : TypedAt env U Δ (σ.cons y) (S.cons (listSet K)) B p) :
    TypedAt env U Δ σ S (.forallE A B) (.app (TyCls env U Δ (A.subst σ)) c K p) := by
  obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK
  obtain ⟨τc, hτc, hpc⟩ := hp
  refine ⟨.piDom (TyCls env U Δ (A.subst σ)) :: (τk.map .piDomOb ++ τc.map (.piCodOb c K)),
    ?_, ?_⟩
  · intro τ hτ
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hτ
    rcases hτ with rfl | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact .piDom
    · exact .piDomOb (hτk x hx)
    · exact .piCodOb hc hτk hkk hy (hτc x hx)
  · refine .app (τd := τk) (τc := τc) (List.mem_cons_self ..) (fun x hx => ?_) hkk hc
      (fun x hx => ⟨K, ?_, Covers.refl⟩) hpc
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hx))

/-- The observations of an application are typed at the instantiated codomain, given the
typing invariant of the function (which identifies the domain class) and soundness for
the codomain. -/
theorem app_typed (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U)) (hA : env.HasType U Γ A (.sort u))
    (ihB : SoundAt env U Δ (A::Γ) B B (.sort v)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (ha : env.HasType U Δ (a.subst σ) (A.subst σ))
    (hf : ∀ o, Obs' σ S f o → TypedAt env U Δ σ S (.forallE A B) o)
    (ho : Obs' σ S (.app f a) o) : TypedAt env U Δ σ S (B.inst a) o := by
  obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 ho
  obtain ⟨τs, hτs, hty⟩ := hf _ hfo
  cases hty with
  | @app _ _ _ _ _ τc _ hD _ _ _ hcod hoty =>
    have eD := Obs.piDom_mem (hτs _ hD); subst eD; subst hc
    have : ∀ x ∈ τc, ∃ x', Obs' σ S (B.inst a) x' ∧ x' ≼ x := by
      intro x hx
      obtain ⟨K₀, hm, hKK₀⟩ := hcod x hx
      obtain ⟨_, ⟨τk, hτk, hkk⟩, y, hy, hxB⟩ := Obs.piCodOb_mem (hτs _ hm)
      have hay : env.IsDefEq U Δ (a.subst σ) y (A.subst σ) := ElCls.collapse henv hΔ ha .self hy
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons (a.subst σ)) (A::Γ) :=
        .cons W hA hay.symm
      have tvK : ∀ k ∈ K₀, TypedAt env U Δ σ S A k := fun k hk => ⟨τk, hτk, hkk k hk⟩
      obtain ⟨x₁, hx₁, l₁⟩ := (ihB _ _ _ W' (tv.cons tvK) (tv.cons tvK)).1 x hxB
      obtain ⟨x₂, hx₂, l₂⟩ := hx₁.mono_le (S' := S.cons (Obs' σ S a)) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k, hk, l⟩ := hKK₀ o h
          obtain ⟨k', hk', l'⟩ := hcov k hk
          exact ⟨k', hK' k' hk', l'.trans l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨x₂, Obs.inst_iff.2 hx₂, l₂.trans l₁⟩
    obtain ⟨τc', h1, h2⟩ := exists_list_cover this
    exact ⟨τc', h1, hoty.strengthen h2⟩

/-! ## Soundness -/

theorem SoundAt.sub_A (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S) :
    Ob.Sub (Obs' σ S A) (Obs' σ' S A') := (ih σ σ' S W tv tv').1

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Key typing transfers from `A` under `σ` to `A` under `σ'` along `A ≡ A'`. -/
theorem keys_transfer {K : List Ob} (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S)
    (hK : ∀ k ∈ K, TypedAt env U Δ σ S A k) :
    (∀ k ∈ K, TypedAt env U Δ σ' S A' k) ∧ (∀ k ∈ K, TypedAt env U Δ σ' S A k) := by
  have W' := SubstEq.right henv hΔ W
  have h1 := (ih σ σ' S W tv tv').1
  have h2 := (ih σ' σ' S W' tv' tv').2.1
  exact ⟨fun k hk => (hK k hk).mono_le h1, fun k hk => ((hK k hk).mono_le h1).mono_le h2⟩

/-- Key typing transfers back from `A'` under `σ'` to `A` under `σ` and `σ'`. -/
theorem keys_transfer' {K : List Ob} (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S)
    (hK : ∀ k ∈ K, TypedAt env U Δ σ' S A' k) :
    (∀ k ∈ K, TypedAt env U Δ σ S A k) ∧ (∀ k ∈ K, TypedAt env U Δ σ' S A k) := by
  have W' := SubstEq.right henv hΔ W
  have h1 := (ih σ σ' S W tv tv').2.1
  have h2 := (ih σ' σ' S W' tv' tv').2.1
  exact ⟨fun k hk => (hK k hk).mono_le h1, fun k hk => (hK k hk).mono_le h2⟩

/-- **Soundness** of the observation model for rule-free environments. -/
theorem sound (hdo : env.DefsOnly) (hdr : env.DefRules) (H : env.IsDefEqStrong U Γ t t' T) :
    SoundAt env U Δ Γ t t' T := by
  induction H with
  | bvar hL =>
    intro σ σ' S W tv tv'
    exact ⟨.of_imp fun o h => .bvar (Obs.bvar_iff.1 h), .of_imp fun o h => .bvar (Obs.bvar_iff.1 h),
      fun o h => tv _ _ hL o (Obs.bvar_iff.1 h), fun o h => tv' _ _ hL o (Obs.bvar_iff.1 h)⟩
  | symm _ ih =>
    intro σ σ' S W tv tv'
    have := ih σ' σ S (SubstEq.symm henv hΔ W) tv' tv
    exact ⟨this.2.1, this.1, this.2.2.2, this.2.2.1⟩
  | trans _ _ ih1 ih2 =>
    intro σ σ' S W tv tv'
    have a := ih1 σ σ' S W tv tv'
    have b := ih2 σ' σ' S (SubstEq.right henv hΔ W) tv' tv'
    exact ⟨a.1.trans b.1, b.2.1.trans a.2.1, a.2.2.1, b.2.2.2⟩
  | @sortDF l l' _ _ _ h3 =>
    intro σ σ' S W tv tv'
    have e : l.eval = l'.eval := h3
    refine ⟨.of_imp fun o h => ?_, .of_imp fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · rw [Obs.sort_mem h, e]; exact .sort
    · rw [Obs.sort_mem h, ← e]; exact .sort
    · rw [Obs.sort_mem h]; exact typedAt_sort_iff.2 (.sort (List.mem_singleton_self _))
    · rw [Obs.sort_mem h, ← e]; exact typedAt_sort_iff.2 (.sort (List.mem_singleton_self _))
  | @constDF c ci ls ls' u Γ hci hlw hlw' _ hls _ _ _ ih0 _ =>
    intro σ σ' S W tv tv'
    have IH0 := ih0 .id .id .empty .nil TV.empty TV.empty
    have eℓ : ls.map (·.eval) = ls'.map (·.eval) := map_eval_eq hls
    have hcl : ∀ ls, (ci.type.instL ls).ClosedN := fun _ => (henv.closedC hci).instL
    have lv : ∀ e : VExpr, LvEq U (e.instL ls) (e.instL ls') := fun e => .instL e hlw hlw' hls
    have lv' : ∀ e : VExpr, LvEq U (e.instL ls') (e.instL ls) :=
      fun e => .instL e hlw' hlw (forall₂_equiv_symm hls)
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · rcases Obs.const_iff.1 h with ⟨ci', τs, keys, r, rfl, hrig, hci', hτ, hty, hr⟩ |
        ⟨df, ci', τs, hdf, hlhs, hci', hτ, hty, hv⟩ <;> cases hci.symm.trans hci' <;>
        obtain ⟨τs', h1, h2⟩ := TypedAt.mono_le ⟨τs, hτ, hty⟩ IH0.1
      · exact ⟨_, .const hrig hci h1 h2 (eℓ ▸ hr), .refl⟩
      · exact ⟨_, .delta hdf hlhs hci h1 h2 (hv.lvEq (lv _)), .refl⟩
    · rcases Obs.const_iff.1 h with ⟨ci', τs, keys, r, rfl, hrig, hci', hτ, hty, hr⟩ |
        ⟨df, ci', τs, hdf, hlhs, hci', hτ, hty, hv⟩ <;> cases hci.symm.trans hci' <;>
        obtain ⟨τs', h1, h2⟩ := TypedAt.mono_le ⟨τs, hτ, hty⟩ IH0.2.1
      · exact ⟨_, .const hrig hci h1 h2 (eℓ ▸ hr), .refl⟩
      · exact ⟨_, .delta hdf hlhs hci h1 h2 (hv.lvEq (lv' _)), .refl⟩
    · rcases Obs.const_iff.1 h with ⟨ci', τs, keys, r, rfl, hrig, hci', hτ, hty, hr⟩ |
        ⟨df, ci', τs, hdf, hlhs, hci', hτ, hty, hv⟩ <;> cases hci.symm.trans hci' <;>
        exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id (hcl ls)).2 (hτ τ hτ'), hty⟩
    · rcases Obs.const_iff.1 h with ⟨ci', τs, keys, r, rfl, hrig, hci', hτ, hty, hr⟩ |
        ⟨df, ci', τs, hdf, hlhs, hci', hτ, hty, hv⟩ <;> cases hci.symm.trans hci' <;>
        obtain ⟨τs', h1, h2⟩ := TypedAt.mono_le ⟨τs, hτ, hty⟩ IH0.2.1 <;>
        exact ⟨τs', fun τ hτ' => (Obs.closed_iff_id (hcl ls)).2 (h1 τ hτ'), h2⟩
  | elimDF h1 => exact absurd h1 (hdo.eliminators _ _)
  | @appDF Γ A u B v f f' a a' _ _ hA hB hf ha hBB ihA ihB ihf iha ihBB =>
    intro σ σ' S W tv tv'
    have W'' := SubstEq.right henv hΔ W
    have hΓ := W.wf
    have haa : env.IsDefEq U Δ (a.subst σ) (a'.subst σ') (A.subst σ) :=
      ha.defeq.substDF henv hΓ hΔ W
    have hAA : env.IsDefEq U Δ (A.subst σ) (A.subst σ') (.sort u) :=
      hA.defeq.substDF henv hΓ hΔ W
    have IHf := ihf σ σ' S W tv tv'
    have IHa := iha σ σ' S W tv tv'
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 h
      obtain ⟨τs, hτs, hty⟩ := IHf.2.2.1 _ hfo
      cases hty with
      | app hD =>
        have eD := Obs.piDom_mem (hτs _ hD); subst eD
        obtain ⟨o₁, ho₁, l₁⟩ := IHf.1 _ hfo
        obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.app_inv
        obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHa.1 k (hK' k hk)
        refine ⟨y, .app ho₁ (hc.trans (ElCls.eq_of_defeq .self haa)) hK1
          (Covers.trans hK2 (hcov.trans hKK₀)), ly⟩
    · obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 h
      obtain ⟨τs, hτs, hty⟩ := IHf.2.2.2 _ hfo
      cases hty with
      | app hD =>
        have eD := Obs.piDom_mem (hτs _ hD); subst eD
        obtain ⟨o₁, ho₁, l₁⟩ := IHf.2.1 _ hfo
        obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.app_inv
        obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHa.2.1 k (hK' k hk)
        refine ⟨y, .app ho₁ (hc.trans (ElCls.eq_of_defeq (.inr (.single (.inl ⟨_, hAA.symm⟩))) haa).symm)
          hK1 (Covers.trans hK2 (hcov.trans hKK₀)), ly⟩
    · exact app_typed henv hΔ hA.defeq (ihB) W.left tv
        (ha.defeq.hasType.1.substDF henv hΓ hΔ W.left) IHf.2.2.1 h
    · have := app_typed henv hΔ hA.defeq (ihB) W'' tv'
        (ha.defeq.hasType.2.substDF henv hΓ hΔ W'') IHf.2.2.2 h
      exact this.mono_le (ihBB σ' σ' S W'' tv' tv').2.1
  | projDF h1 => exact absurd h1 (hdo.projections _ _)
  | @lamDF Γ A A' u B v body body' _ _ hAA _ _ _ _ ihA _ _ ihb _ =>
    intro σ σ' S W tv tv'
    have W'' := SubstEq.right henv hΔ W
    have hΓ := W.wf
    have hA := hAA.defeq.hasType.1
    have eD : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A'.subst σ') :=
      TyCls.eq_of_defeq (hAA.defeq.substDF henv hΓ hΔ W)
    have eD' : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
      TyCls.eq_of_defeq (hA.substDF henv hΓ hΔ W)
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihb _ _ _ W' (tv.cons hKσ) (tv'.cons hK2)).1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      refine ⟨_, ?_, Ob.Le.app' Covers.refl l⟩
      rw [eD]; exact .lam (hc.congr_D eD) h1 h2 hy hp'
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer' henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihb _ _ _ W' (tv.cons hK1) (tv'.cons hK2)).2.1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      refine ⟨_, ?_, Ob.Le.app' Covers.refl l⟩
      rw [← eD]; exact .lam hc' h1 h2 hy hp'
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨_, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      exact lam_typed hc hKσ hy ((ihb _ _ _ W' (tv.cons hKσ) (tv'.cons hK2)).2.2.1 p hp)
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer' henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      have hp' := (ihb _ _ _ W' (tv.cons hK1) (tv'.cons hK2)).2.2.2 p hp
      rw [← eD, eD']
      exact lam_typed (hc'.congr_D eD') hK2 hy hp'
  | @forallEDF Γ A A' u B B' v hu hv hAA hBB _ ihA ihB _ =>
    intro σ σ' S W tv tv'
    have hΓ := W.wf
    have hA := hAA.defeq.hasType.1
    have eD : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A'.subst σ') :=
      TyCls.eq_of_defeq (hAA.defeq.substDF henv hΓ hΔ W)
    have IHA := ihA σ σ' S W tv tv'
    have imax0 : ∀ ns, (VLevel.imax u v).eval ns = 0 → v.eval ns = 0 := by
      intro ns h; exact imax_eval_zero h
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
        ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩
      · exact ⟨_, by rw [eD]; exact .piDom, .refl⟩
      · obtain ⟨p', hp', l⟩ := IHA.1 p hp; exact ⟨_, .piDomOb hp', .piDomOb l⟩
      · have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
          .cons W hA (hc.hasType henv hΔ hy)
        have eC := TyCls.eq_of_defeq (hBB.defeq.substDF henv W'.wf hΔ W')
        exact ⟨_, by rw [eC]; exact .piCod (hc.congr_D eD) hy, .refl⟩
      · have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
        have ⟨hK1, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
        have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
          .cons W hA (hc.hasType henv hΔ hy)
        obtain ⟨p', hp', l⟩ := (ihB _ _ _ W' (tv.cons hKσ) (tv'.cons hK2)).1 p hp
        obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
        exact ⟨_, .piCodOb (hc.congr_D eD) h1 h2 hy hp', .piCodOb' Covers.refl l⟩
    · rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
        ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩
      · exact ⟨_, by rw [← eD]; exact .piDom, .refl⟩
      · obtain ⟨p', hp', l⟩ := IHA.2.1 p hp; exact ⟨_, .piDomOb hp', .piDomOb l⟩
      · have hc' := hc.congr_D eD.symm
        have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
          .cons W hA (hc'.hasType henv hΔ hy)
        have eC := TyCls.eq_of_defeq (hBB.defeq.substDF henv W'.wf hΔ W')
        exact ⟨_, by rw [← eC]; exact .piCod hc' hy, .refl⟩
      · have hKσ' : ∀ k ∈ K, TypedAt env U Δ σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
        have ⟨hK1, hK2⟩ := keys_transfer' henv hΔ ihA W tv tv' hKσ'
        have hc' := hc.congr_D eD.symm
        have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
          .cons W hA (hc'.hasType henv hΔ hy)
        obtain ⟨p', hp', l⟩ := (ihB _ _ _ W' (tv.cons hK1) (tv'.cons hK2)).2.1 p hp
        obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
        exact ⟨_, .piCodOb hc' h1 h2 hy hp', .piCodOb' Covers.refl l⟩
    · refine typedAt_sort_iff.2 ?_
      rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
        ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩
      · exact .piDom (List.mem_singleton_self _)
      · exact .piDomOb (List.mem_singleton_self _)
      · exact .piCod (List.mem_singleton_self _)
      · have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
        have ⟨_, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
        have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
          .cons W hA (hc.hasType henv hΔ hy)
        have := (ihB _ _ _ W' (tv.cons hKσ) (tv'.cons hK2)).2.2.1 p hp
        exact .piCodOb (List.mem_singleton_self _) (typedAt_sort_iff.1 this) imax0
    · refine typedAt_sort_iff.2 ?_
      rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
        ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩
      · exact .piDom (List.mem_singleton_self _)
      · exact .piDomOb (List.mem_singleton_self _)
      · exact .piCod (List.mem_singleton_self _)
      · have hKσ' : ∀ k ∈ K, TypedAt env U Δ σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
        have ⟨hK1, hK2⟩ := keys_transfer' henv hΔ ihA W tv tv' hKσ'
        have hc' := hc.congr_D eD.symm
        have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
          .cons W hA (hc'.hasType henv hΔ hy)
        have := (ihB _ _ _ W' (tv.cons hK1) (tv'.cons hK2)).2.2.2 p hp
        exact .piCodOb (List.mem_singleton_self _) (typedAt_sort_iff.1 this) imax0
  | defeqDF _ _ _ ihAB ihe =>
    intro σ σ' S W tv tv'
    have IH := ihe σ σ' S W tv tv'
    exact ⟨IH.1, IH.2.1,
      fun o h => (IH.2.2.1 o h).mono_le (ihAB σ σ S W.left tv tv).1,
      fun o h => (IH.2.2.2 o h).mono_le
        (ihAB σ' σ' S (SubstEq.right henv hΔ W) tv' tv').1⟩
  | @beta Γ A u B v e e' _ _ hA _ he he' _ _ ihA ihB ihe ihe' _ ihee' =>
    intro σ σ' S W tv tv'
    have W'' := SubstEq.right henv hΔ W
    have hΓ := W.wf
    have hee : env.IsDefEq U Δ (e'.subst σ) (e'.subst σ') (A.subst σ) :=
      he'.defeq.substDF henv hΓ hΔ W
    have IHA := ihA σ σ' S W tv tv'
    have IHe' := ihe' σ σ' S W tv tv'
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨D, c, K, K', hlo, hc, hK', hcov⟩ := Obs.app_iff.1 h
      obtain ⟨c₁, K₁, y, τs, p, e₁, hc₁, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 hlo
      injection e₁ with eD ec eK eo
      subst eD ec eK eo hc
      have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ σ' S A k := fun k hk => (hKσ k hk).mono_le IHA.1
      have hy' : env.IsDefEq U Δ y (e'.subst σ') (A.subst σ) :=
        (ElCls.collapse henv hΔ hee.hasType.1 .self hy).symm.trans hee
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons (e'.subst σ')) (A::Γ) :=
        .cons W hA.defeq hy'
      obtain ⟨o₁, ho₁, l₁⟩ := (ihe _ _ _ W' (tv.cons hKσ) (tv'.cons hKσ')).1 _ hp
      obtain ⟨o₂, ho₂, l₂⟩ := ho₁.mono_le (S' := S.cons (Obs' σ' S e')) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k, hk, l⟩ := hcov o h
          obtain ⟨k', hk', l'⟩ := IHe'.1 k (hK' k hk)
          exact ⟨k', hk', l'.trans l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨o₂, Obs.inst_iff.2 ho₂, l₂.trans l₁⟩
    · obtain ⟨K, hK, ho⟩ := (Obs.inst_iff.1 h).compact0
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ σ' S A k := fun k hk => IHe'.2.2.2 k (hK k hk)
      have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => (hKσ' k hk).mono_le IHA.2.1
      have W' : Ctx.SubstEq env U Δ (σ.cons (e'.subst σ)) (σ'.cons (e'.subst σ')) (A::Γ) :=
        .cons W hA.defeq hee
      obtain ⟨o₁, ho₁, l₁⟩ := (ihe _ _ _ W' (tv.cons hKσ) (tv'.cons hKσ')).2.1 o ho
      obtain ⟨τs, h1, h2⟩ := TypedAt.merge hKσ
      have hlam := Obs.lam (TypedElCls.of_hasType hee.hasType.1) h1 h2 ElCls.self ho₁
      obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHe'.2.1 k (hK k hk)
      exact ⟨o₁, .app hlam rfl hK1 hK2, l₁⟩
    · refine app_typed henv hΔ hA.defeq ihB W.left tv hee.hasType.1 (fun o h => ?_) h
      obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ : ∀ k ∈ K, TypedAt env U Δ σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons y) (A::Γ) :=
        .cons W.left hA.defeq (hc.hasType henv hΔ hy)
      exact lam_typed hc hKσ hy ((ihe _ _ _ W' (tv.cons hKσ) (tv.cons hKσ)).2.2.1 p hp)
    · exact (ihee' σ' σ' S W'' tv' tv').2.2.1 o h
  | @eta Γ A u B v e _ _ hA _ _ he _ _ ihA _ _ ihe _ _ =>
    intro σ σ' S W tv tv'
    have hΓ := W.wf
    have IHe := ihe σ σ' S W tv tv'
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      obtain ⟨D₁, c₁, K₁, K₁', he₁, hc₁, hK₁', hcov₁⟩ := Obs.app_iff.1 hp
      have he₁' := Obs.lift_cons_iff.1 he₁
      obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ he₁'
      cases hty₁ with
      | app hD =>
        have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
        have ec : c₁ = c := hc₁.trans (TypedElCls.eq_of_mem' henv hΔ hc hy).symm
        subst ec
        obtain ⟨o₂, ho₂, l₂⟩ := IHe.1 _ he₁'
        refine ⟨o₂, ho₂, l₂.trans (Ob.Le.app' ?_ .refl)⟩
        exact Covers.trans (Covers.of_subset fun k hk => Obs.bvar_iff.1 (hK₁' k hk)) hcov₁
    · obtain ⟨o₁, ho₁, l₁⟩ := IHe.2.1 o h
      obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ ho₁
      obtain ⟨D, c, K, p, rfl⟩ := typed_pi_app hty₁ hτs₁
      cases hty₁ with
      | app hD hd hk hc =>
        have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
        have hτd : ∀ x ∈ _, Obs' σ S A x := fun x hx => Obs.piDomOb_mem (hτs₁ _ (hd x hx))
        obtain ⟨y, hy⟩ := hc.nonempty
        refine ⟨_, .lam hc hτd hk hy ?_, l₁⟩
        refine .app (Obs.lift_cons_iff.2 ho₁) (TypedElCls.eq_of_mem' henv hΔ hc hy) (K' := K)
          (fun k hk => Obs.bvar_iff.2 hk) Covers.refl
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hy, hp⟩ := Obs.lam_iff.1 h
      obtain ⟨D₁, c₁, K₁, K₁', he₁, hc₁, hK₁', hcov₁⟩ := Obs.app_iff.1 hp
      have he₁' := Obs.lift_cons_iff.1 he₁
      obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ he₁'
      have hty₁' := hty₁
      cases hty₁ with
      | app hD =>
        have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
        have ec : c₁ = c := hc₁.trans (TypedElCls.eq_of_mem' henv hΔ hc hy).symm
        subst ec
        have hKK : Covers K K₁ :=
          Covers.trans (Covers.of_subset fun k hk => Obs.bvar_iff.1 (hK₁' k hk)) hcov₁
        refine ⟨τs₁ ++ τs.map .piDomOb, fun τ hτ' => ?_,
          (hty₁'.mono fun τ hτ' => List.mem_append_left _ hτ').app_enlarge hKK
            (fun x hx => List.mem_append_right _ (List.mem_map_of_mem hx)) hK⟩
        rcases List.mem_append.1 hτ' with hτ' | hτ'
        · exact hτs₁ τ hτ'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hτ'; exact .piDomOb (hτ x hx)
    · exact IHe.2.2.2 o h
  | proofIrrel _ _ _ ihp ihh ihh' =>
    intro σ σ' S W tv tv'
    have IHp := ihp σ σ' S W tv tv'
    have IHh := ihh σ σ' S W tv tv'
    have IHh' := ihh' σ σ' S W tv tv'
    have e1 : ∀ o, ¬ Obs' σ S _ o := fun o h => by
      obtain ⟨τs, h1, h2⟩ := IHh.2.2.1 o h
      exact h2.not_prop fun τ hτ => typedAt_sort_iff.1 (IHp.2.2.1 τ (h1 τ hτ))
    have e2 : ∀ o, ¬ Obs' σ' S _ o := fun o h => by
      obtain ⟨τs, h1, h2⟩ := IHh'.2.2.2 o h
      exact h2.not_prop fun τ hτ => typedAt_sort_iff.1 (IHp.2.2.2 τ (h1 τ hτ))
    exact ⟨fun o h => (e1 o h).elim, fun o h => (e2 o h).elim,
      fun o h => (e1 o h).elim, fun o h => (e2 o h).elim⟩
  | @extra df ls u Γ hdf hlw hlen _ _ _ _ _ _ _ _ _ _ ihR =>
    intro σ σ' S W tv tv'
    obtain ⟨n, ls₀, hlhs⟩ := hdo.defeqs df hdf
    obtain ⟨rfl, hci⟩ := hdr.const df hdf n ls₀ hlhs
    have elhs : df.lhs.instL ls = .const n ls := by
      rw [hlhs]; simp only [VExpr.instL, VLevel.inst_map_id hlen]
    rw [elhs]
    have hrcl : (df.rhs.instL ls).ClosedN := ((henv.closed.2 hdf).2.1).instL
    have htcl : (df.type.instL ls).ClosedN := ((henv.closed.2 hdf).1.2).instL
    have IHR := ihR σ' σ' S (SubstEq.right henv hΔ W) tv' tv'
    have notRigid : ¬ env.Rigid n := fun hrig => hrig df hdf _ (by rw [hlhs]; rfl)
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, IHR.2.2.1⟩
    · rcases Obs.const_iff.1 h with ⟨_, _, _, _, _, hrig, _⟩ |
        ⟨df', ci', τs, hdf', hlhs', hci', hτ, hty, hv⟩
      · exact absurd hrig notRigid
      · cases hdr.excl df df' hdf hdf' n _ _ hlhs (by rw [hlhs']; rfl)
        exact ⟨o, (Obs.closed_iff_id hrcl).2 hv, .refl⟩
    · obtain ⟨τs, hτ, hty⟩ := IHR.2.2.1 o h
      exact ⟨o, .delta hdf (by rw [hlhs]) hci (ci := ⟨df.uvars, df.type⟩)
        (fun τ hτ' => (Obs.closed_iff_id htcl).1 (hτ τ hτ')) hty
        ((Obs.closed_iff_id hrcl).1 h), .refl⟩
    · rcases Obs.const_iff.1 h with ⟨_, _, _, _, _, hrig, _⟩ |
        ⟨df', ci', τs, hdf', hlhs', hci', hτ, hty, hv⟩
      · exact absurd hrig notRigid
      · cases hci.symm.trans hci'
        exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id htcl).2 (hτ τ hτ'), hty⟩
  | elimIota h1 => exact absurd h1 (hdo.eliminators _ _)
  | projIota h1 => exact absurd h1 (hdo.projections _ _)
  | structEta h1 => exact absurd h1 (hdo.projections _ _)
  | unitLike h1 => exact absurd h1 (hdo.projections _ _)

end

end Model
end VEnv
end Lean4Lean
