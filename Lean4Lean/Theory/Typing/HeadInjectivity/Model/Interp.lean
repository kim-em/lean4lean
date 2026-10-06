import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Obs

/-! # The observation interpretation (milestone M2, structural part)

`Obs env U Δ σ S t o`: under the valuation `(σ, S)` the term `t` (in a source context `Γ`)
has the observation `o` (`docs/inductives/PHASE1B_NOTES.md`, section 9.1). The valuation
consists of an *anchor* substitution `σ` from `Γ` into the target context `Δ`, from which
all classes are computed (`TyCls Δ (A.subst σ)`, `ElCls Δ D (a.subst σ)`), and observation
sets `S i` for the variables (the semantic part).

Deviation from section 9.1 (recorded in section 10 of the notes): valuations are pairs of
an anchor substitution and observation sets instead of lists of (class, observation set);
a key `(c, K)` extends the anchor by a representative `x` of `c`. With anchors the
substitution lemma (`Obs.subst_iff`) is purely syntactic, needing no typing; the price is
that a key's representative is chosen, so representative invariance becomes part of
soundness (its motive relates two definitionally equal anchors).

Clauses (every occurrence of `Obs` strictly positive, key typing inlined):
* `bvar i`: the observations `S i`;
* `sort l`: `.sort l.eval`;
* `forallE A B`: `piDom` of the domain class, `piDomOb o` for observations of `A`,
  `piCod c C` and `piCodOb c K o` for typed keys `(c, K)` at `A` (`c` a typed class at the
  domain class, every `k ∈ K` typed at observations of `A`), `B` read at the anchor extended
  by a representative `x` of `c` and the observation set `K`;
* `lam A t`: `app D c K o` for typed keys, `D` the domain class;
* `app f a`: `o` whenever `f` has `app D c K o` with `c` the class of `a` at `D` and `K`
  covered by observations of `a`;
* `const n ls`: rigid spine observations `wrap keys r` (`r` the head observation `rigid n
  (ls.map eval) keys.length` or an argument observation `rigidArg i cᵢ`), **filtered**: kept
  only when typed at observations of `ci.type.instL ls`, read at the fixed valuation
  `(id, ∅)` (the type is closed; `Obs.closed_iff` shows the valuation is irrelevant there).
  Milestone M2 is for rule-free environments: every constant is rigid.
* `elim` and `proj` have no observations in this milestone.

Structural lemmas: inversion (`*_iff`), weakening (`Obs.lift'_iff`), substitution
(`Obs.subst_iff`), monotonicity in the observation sets (`Obs.mono`, `Obs.mono_le`),
compactness (`Obs.compact`), and invariance for closed terms (`Obs.closed_iff`). Typed
valuations (`TV`) are defined at the end. -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- Observation sets of the variables of a valuation. -/
abbrev ObSets := Nat → Ob → Prop

namespace ObSets

def cons (S : ObSets) (X : Ob → Prop) : ObSets
  | 0 => X
  | i+1 => S i

def lift_l (ρ : Lift) (S : ObSets) : ObSets := fun i => S (ρ.liftVar i)

protected def empty : ObSets := fun _ _ => False

def update (S : ObSets) (n : Nat) (X : Ob → Prop) : ObSets := fun i => if i = n then X else S i

theorem lift_l_cons {S : ObSets} : (S.cons X).lift_l ρ.cons = (S.lift_l ρ).cons X := by
  funext i; cases i <;> rfl

theorem update_cons {S : ObSets} : (S.cons X).update (n+1) Y = (S.update n Y).cons X := by
  funext i; cases i <;> simp [update, cons]

end ObSets

theorem _root_.Lean4Lean.VExpr.Subst.lift_l_cons {σ : VExpr.Subst} :
    (σ.cons x).lift_l ρ.cons = (σ.lift_l ρ).cons x := by
  funext i; cases i <;> rfl

theorem _root_.Lean4Lean.VExpr.Subst.lift_comp_cons {τ σ : VExpr.Subst} :
    τ.lift.comp (σ.cons x) = (τ.comp σ).cons x := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons, VExpr.lift_subst_cons]

/-- The finite set of a list of observations. -/
def listSet (K : List Ob) : Ob → Prop := fun k => k ∈ K

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The observation interpretation. See the module docstring for the clauses. -/
inductive Obs : VExpr.Subst → ObSets → VExpr → Ob → Prop
  | bvar : S i o → Obs σ S (.bvar i) o
  | sort : Obs σ S (.sort l) (.sort l.eval)
  | piDom : Obs σ S (.forallE A B) (.piDom (TyCls env U Δ (A.subst σ)))
  | piDomOb : Obs σ S A o → Obs σ S (.forallE A B) (.piDomOb o)
  | piCod : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c → c x →
    Obs σ S (.forallE A B) (.piCod c (TyCls env U Δ (B.subst (σ.cons x))))
  | piCodOb : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c →
    (∀ τ ∈ τs, Obs σ S A τ) → (∀ k ∈ K, TypedOb env U Δ k τs) → c x →
    Obs (σ.cons x) (S.cons (listSet K)) B o → Obs σ S (.forallE A B) (.piCodOb c K o)
  | lam : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c →
    (∀ τ ∈ τs, Obs σ S A τ) → (∀ k ∈ K, TypedOb env U Δ k τs) → c x →
    Obs (σ.cons x) (S.cons (listSet K)) t o →
    Obs σ S (.lam A t) (.app (TyCls env U Δ (A.subst σ)) c K o)
  | app : Obs σ S f (.app D c K o) → c = ElCls env U Δ D (a.subst σ) →
    (∀ k ∈ K', Obs σ S a k) → Covers K' K → Obs σ S (.app f a) o
  | const : env.constants n = some ci →
    (∀ τ ∈ τs, Obs .id .empty (ci.type.instL ls) τ) →
    TypedOb env U Δ (wrap keys r) τs → RigidEnd n (ls.map (·.eval)) keys r →
    Obs σ S (.const n ls) (wrap keys r)

/-- `o` is typed at a list of observations of `T`. -/
def TypedAt (σ : VExpr.Subst) (S : ObSets) (T : VExpr) (o : Ob) : Prop :=
  ∃ τs, (∀ τ ∈ τs, Obs env U Δ σ S T τ) ∧ TypedOb env U Δ o τs

/-- A typed valuation for `Γ`: every observation of a variable is typed at observations of
its type. (The anchor's typing, `Ctx.SubstEq env U Δ σ σ Γ`, is a separate hypothesis.) -/
def TV (Γ : List VExpr) (σ : VExpr.Subst) (S : ObSets) : Prop :=
  ∀ i A, Lookup Γ i A → ∀ o, S i o → TypedAt env U Δ σ S A o

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Inversion -/

namespace Obs

theorem bvar_iff : Obs' σ S (.bvar i) o ↔ S i o :=
  ⟨fun | .bvar h => h, .bvar⟩

theorem sort_iff : Obs' σ S (.sort l) o ↔ o = .sort l.eval :=
  ⟨fun | .sort => rfl, fun h => h ▸ .sort⟩

theorem forallE_iff : Obs' σ S (.forallE A B) o ↔
    o = .piDom (TyCls env U Δ (A.subst σ)) ∨
    (∃ p, o = .piDomOb p ∧ Obs' σ S A p) ∨
    (∃ c x, o = .piCod c (TyCls env U Δ (B.subst (σ.cons x))) ∧
      TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧ c x) ∨
    (∃ c K x τs p, o = .piCodOb c K p ∧ TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∀ τ ∈ τs, Obs' σ S A τ) ∧ (∀ k ∈ K, TypedOb env U Δ k τs) ∧ c x ∧
      Obs' (σ.cons x) (S.cons (listSet K)) B p) := by
  constructor
  · intro h; cases h with
    | piDom => exact .inl rfl
    | piDomOb h => exact .inr (.inl ⟨_, rfl, h⟩)
    | piCod h1 h2 => exact .inr (.inr (.inl ⟨_, _, rfl, h1, h2⟩))
    | piCodOb h1 h2 h3 h4 h5 => exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, h1, h2, h3, h4, h5⟩))
  · rintro (rfl | ⟨_, rfl, h⟩ | ⟨_, _, rfl, h1, h2⟩ | ⟨_, _, _, _, _, rfl, h1, h2, h3, h4, h5⟩)
    · exact .piDom
    · exact .piDomOb h
    · exact .piCod h1 h2
    · exact .piCodOb h1 h2 h3 h4 h5

theorem lam_iff : Obs' σ S (.lam A t) o ↔
    ∃ c K x τs p, o = .app (TyCls env U Δ (A.subst σ)) c K p ∧
      TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∀ τ ∈ τs, Obs' σ S A τ) ∧ (∀ k ∈ K, TypedOb env U Δ k τs) ∧ c x ∧
      Obs' (σ.cons x) (S.cons (listSet K)) t p := by
  constructor
  · intro h; cases h with
    | lam h1 h2 h3 h4 h5 => exact ⟨_, _, _, _, _, rfl, h1, h2, h3, h4, h5⟩
  · rintro ⟨_, _, _, _, _, rfl, h1, h2, h3, h4, h5⟩; exact .lam h1 h2 h3 h4 h5

theorem app_iff : Obs' σ S (.app f a) o ↔
    ∃ D c K K', Obs' σ S f (.app D c K o) ∧ c = ElCls env U Δ D (a.subst σ) ∧
      (∀ k ∈ K', Obs' σ S a k) ∧ Covers K' K := by
  constructor
  · intro h; cases h with
    | app h1 h2 h3 h4 => exact ⟨_, _, _, _, h1, h2, h3, h4⟩
  · rintro ⟨_, _, _, _, h1, h2, h3, h4⟩; exact .app h1 h2 h3 h4

theorem const_iff : Obs' σ S (.const n ls) o ↔
    ∃ ci τs keys r, o = wrap keys r ∧ env.constants n = some ci ∧
      (∀ τ ∈ τs, Obs' .id .empty (ci.type.instL ls) τ) ∧
      TypedOb env U Δ (wrap keys r) τs ∧ RigidEnd n (ls.map (·.eval)) keys r := by
  constructor
  · intro h; cases h with
    | const h1 h2 h3 h4 => exact ⟨_, _, _, _, rfl, h1, h2, h3, h4⟩
  · rintro ⟨_, _, _, _, rfl, h1, h2, h3, h4⟩; exact .const h1 h2 h3 h4

theorem elim_iff : Obs' σ S (.elim b i ls) o ↔ False := ⟨nofun, nofun⟩

theorem proj_iff : Obs' σ S (.proj n i e) o ↔ False := ⟨nofun, nofun⟩

/-- The `piDom` observation of a Pi type records its domain class. -/
theorem piDom_mem (h : Obs' σ S (.forallE A B) (.piDom D)) : D = TyCls env U Δ (A.subst σ) := by
  cases h; rfl

theorem piDomOb_mem (h : Obs' σ S (.forallE A B) (.piDomOb p)) : Obs' σ S A p := by
  cases h; assumption

theorem piCod_mem (h : Obs' σ S (.forallE A B) (.piCod c C)) :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      ∃ x, c x ∧ C = TyCls env U Δ (B.subst (σ.cons x)) := by
  cases h with | piCod h1 h2 => exact ⟨h1, _, h2, rfl⟩

theorem piCodOb_mem (h : Obs' σ S (.forallE A B) (.piCodOb c K p)) :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c ∧
      (∃ τs, (∀ τ ∈ τs, Obs' σ S A τ) ∧ ∀ k ∈ K, TypedOb env U Δ k τs) ∧
      ∃ x, c x ∧ Obs' (σ.cons x) (S.cons (listSet K)) B p := by
  cases h with | piCodOb h1 h2 h3 h4 h5 => exact ⟨h1, ⟨_, h2, h3⟩, _, h4, h5⟩

theorem sort_mem (h : Obs' σ S (.sort l) o) : o = .sort l.eval := sort_iff.1 h

/-! ## Weakening -/

theorem lift'_iff {t : VExpr} {ρ : Lift} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.lift' ρ) o ↔ Obs' (σ.lift_l ρ) (S.lift_l ρ) t o := by
  induction t generalizing ρ σ S o with
  | bvar i => simp only [VExpr.lift', bvar_iff]; rfl
  | sort => simp only [VExpr.lift', sort_iff]
  | const => simp only [VExpr.lift', const_iff]
  | elim => simp only [VExpr.lift', elim_iff]
  | proj => simp only [VExpr.lift', proj_iff]
  | app f a ihf iha =>
    simp only [VExpr.lift', app_iff, ihf, iha, VExpr.subst_lift']
  | lam A t ihA iht =>
    simp only [VExpr.lift', lam_iff, ihA, iht, VExpr.subst_lift', ObSets.lift_l_cons,
      VExpr.Subst.lift_l_cons]
  | forallE A B ihA ihB =>
    simp only [VExpr.lift', forallE_iff, ihA, ihB, VExpr.subst_lift', ObSets.lift_l_cons,
      VExpr.Subst.lift_l_cons]

theorem lift_cons_iff {t : VExpr} :
    Obs' (σ.cons x) (S.cons X) t.lift o ↔ Obs' σ S t o := by
  rw [VExpr.lift_eq_lift', lift'_iff]; rfl

/-! ## Substitution -/

theorem lift_cons_set {σ : VExpr.Subst} {S : ObSets} (τ : VExpr.Subst) :
    (fun i => Obs' (σ.cons x) (S.cons (listSet K)) (τ.lift i)) =
      ObSets.cons (fun i => Obs' σ S (τ i)) (listSet K) := by
  funext i o; cases i with
  | zero => exact propext bvar_iff
  | succ i => exact propext lift_cons_iff

theorem subst_iff {t : VExpr} {τ σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.subst τ) o ↔ Obs' (τ.comp σ) (fun i => Obs' σ S (τ i)) t o := by
  induction t generalizing τ σ S o with
  | bvar i => simp only [VExpr.subst, bvar_iff]
  | sort => simp only [VExpr.subst, sort_iff]
  | const => simp only [VExpr.subst, const_iff]
  | elim => simp only [VExpr.subst, elim_iff]
  | proj => simp only [VExpr.subst, proj_iff]
  | app f a ihf iha =>
    simp only [VExpr.subst, app_iff, ihf, iha, VExpr.subst_subst]
  | lam A t ihA iht =>
    simp only [VExpr.subst, lam_iff, ihA, iht, VExpr.subst_subst, VExpr.Subst.lift_comp_cons,
      lift_cons_set]
  | forallE A B ihA ihB =>
    simp only [VExpr.subst, forallE_iff, ihA, ihB, VExpr.subst_subst,
      VExpr.Subst.lift_comp_cons, lift_cons_set]

/-- Instantiation: the observations of `t.inst a` are those of `t` with the bound variable
read as `a` (anchor `a.subst σ`, observation set the observations of `a`). -/
theorem inst_iff {t a : VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (t.inst a) o ↔ Obs' (σ.cons (a.subst σ)) (S.cons (Obs' σ S a)) t o := by
  rw [VExpr.inst_eq, subst_iff]
  have h1 : (VExpr.Subst.one a).comp σ = σ.cons (a.subst σ) := by
    funext i; cases i <;> rfl
  have h2 : (fun i => Obs' σ S (VExpr.Subst.one a i)) = S.cons (Obs' σ S a) := by
    funext i o; cases i with
    | zero => rfl
    | succ i => exact propext bvar_iff
  rw [h1, h2]

/-! ## Monotonicity and compactness -/

/-- Monotonicity under inclusion of the observation sets. -/
theorem mono (h : Obs' σ S t o) (hS : ∀ i o, S i o → S' i o) : Obs' σ S' t o := by
  induction h generalizing S' with
  | bvar h => exact .bvar (hS _ _ h)
  | sort => exact .sort
  | piDom => exact .piDom
  | piDomOb _ ih => exact .piDomOb (ih hS)
  | piCod h1 h2 => exact .piCod h1 h2
  | piCodOb h1 _ h3 h4 _ ih2 ih5 =>
    refine .piCodOb h1 (fun τ hτ => ih2 τ hτ hS) h3 h4 (ih5 fun i o h => ?_)
    cases i with
    | zero => exact h
    | succ i => exact hS i o h
  | lam h1 _ h3 h4 _ ih2 ih5 =>
    refine .lam h1 (fun τ hτ => ih2 τ hτ hS) h3 h4 (ih5 fun i o h => ?_)
    cases i with
    | zero => exact h
    | succ i => exact hS i o h
  | app _ h2 _ h4 ih1 ih3 => exact .app (ih1 hS) h2 (fun k hk => ih3 k hk hS) h4
  | const h1 h2 h3 h4 => exact .const h1 h2 h3 h4

/-- Monotonicity up to subsumption: if every observation of `S` is subsumed by one of
`S'`, every observation under `S` is subsumed by one under `S'`. -/
theorem mono_le (h : Obs' σ S t o) (hS : ∀ i o, S i o → ∃ o', S' i o' ∧ o' ≼ o) :
    ∃ o', Obs' σ S' t o' ∧ o' ≼ o := by
  induction h generalizing S' with
  | bvar h => let ⟨o', h1, h2⟩ := hS _ _ h; exact ⟨o', .bvar h1, h2⟩
  | sort => exact ⟨_, .sort, .refl⟩
  | piDom => exact ⟨_, .piDom, .refl⟩
  | piDomOb _ ih => let ⟨o', h1, h2⟩ := ih hS; exact ⟨_, .piDomOb h1, .piDomOb h2⟩
  | piCod h1 h2 => exact ⟨_, .piCod h1 h2, .refl⟩
  | @piCodOb _ τs _ _ _ K _ _ _ h1 _ h3 h4 _ ih2 ih5 =>
    have ⟨τs', hτ1, hτ2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => ih2 τ hτ hS
    have ⟨o', ho1, ho2⟩ := ih5 (S' := S'.cons (listSet K)) fun i o h => by
      cases i with
      | zero => exact ⟨o, h, .refl⟩
      | succ i => exact hS i o h
    exact ⟨_, .piCodOb h1 hτ1 (fun k hk => (h3 k hk).strengthen hτ2) h4 ho1,
      .piCodOb' .refl ho2⟩
  | @lam _ τs _ _ _ K _ _ _ h1 _ h3 h4 _ ih2 ih5 =>
    have ⟨τs', hτ1, hτ2⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
      fun τ hτ => ih2 τ hτ hS
    have ⟨o', ho1, ho2⟩ := ih5 (S' := S'.cons (listSet K)) fun i o h => by
      cases i with
      | zero => exact ⟨o, h, .refl⟩
      | succ i => exact hS i o h
    exact ⟨_, .lam h1 hτ1 (fun k hk => (h3 k hk).strengthen hτ2) h4 ho1, .app' .refl ho2⟩
  | @app _ _ _ _ _ _ _ K' _ _ h2 _ h4 ih1 ih3 =>
    have ⟨o₁, h1', l₁⟩ := ih1 hS
    have ⟨K₀, y, e, hK₀, ly⟩ := l₁.app_inv; subst e
    have ⟨K'', hK1, hK2⟩ := exists_list_cover (L := K') (R := fun y x => y ≼ x)
      fun k hk => ih3 k hk hS
    exact ⟨y, .app h1' h2 hK1 (Covers.trans hK2 (h4.trans hK₀)), ly⟩
  | const h1 h2 h3 h4 => exact ⟨_, .const h1 h2 h3 h4, .refl⟩

/-- Merge finitely many finite witnesses into one. -/
theorem collect {α : Type} {Q : Ob → Prop} {P : List Ob → α → Prop}
    (hP : ∀ K K' x, (∀ k ∈ K, k ∈ K') → P K x → P K' x) :
    ∀ {L : List α}, (∀ x ∈ L, ∃ K, (∀ k ∈ K, Q k) ∧ P K x) →
      ∃ K, (∀ k ∈ K, Q k) ∧ ∀ x ∈ L, P K x
  | [], _ => ⟨[], nofun, nofun⟩
  | x :: L, h => by
    obtain ⟨K₁, hQ₁, hP₁⟩ := h x (.head _)
    obtain ⟨K₂, hQ₂, hP₂⟩ := collect hP fun y hy => h y (.tail _ hy)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, fun y hy => ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hQ₁ k hk
      · exact hQ₂ k hk
    · cases hy with
      | head => exact hP _ _ _ (fun k hk => List.mem_append_left _ hk) hP₁
      | tail _ hy => exact hP _ _ _ (fun k hk => List.mem_append_right _ hk) (hP₂ y hy)

theorem update_mono {S : ObSets} (h : ∀ k ∈ K, k ∈ K') :
    ∀ i o, S.update n (listSet K) i o → S.update n (listSet K') i o := by
  intro i o h'; unfold ObSets.update at h' ⊢; split <;> simp_all [listSet]

theorem compact_bvar {S : ObSets} (h : S i o) (n : Nat) :
    ∃ K : List Ob, (∀ k ∈ K, S n k) ∧ Obs' σ (S.update n (listSet K)) (.bvar i) o := by
  by_cases e : i = n
  · subst e; exact ⟨[o], by simpa using h, .bvar (by simp [ObSets.update, listSet])⟩
  · exact ⟨[], nofun, .bvar (by simpa [ObSets.update, e] using h)⟩

/-- **Compactness**: a derivation uses finitely many observations of each variable. -/
theorem compact (h : Obs' σ S t o) (n : Nat) :
    ∃ K : List Ob, (∀ k ∈ K, S n k) ∧ Obs' σ (S.update n (listSet K)) t o := by
  induction h generalizing n with
  | bvar h => exact compact_bvar h n
  | sort => exact ⟨[], nofun, .sort⟩
  | piDom => exact ⟨[], nofun, .piDom⟩
  | piDomOb _ ih => let ⟨K, h1, h2⟩ := ih n; exact ⟨K, h1, .piDomOb h2⟩
  | piCod h1 h2 => exact ⟨[], nofun, .piCod h1 h2⟩
  | piCodOb h1 _ h3 h4 _ ih2 ih5 =>
    have ⟨K₁, hK₁, hA⟩ := collect (P := fun K τ => Obs' _ (ObSets.update _ n (listSet K)) _ τ)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun τ hτ => ih2 τ hτ n
    have ⟨K₂, hK₂, hB⟩ := ih5 (n+1)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, .piCodOb h1
      (fun τ hτ => (hA τ hτ).mono (update_mono fun k hk => List.mem_append_left _ hk))
      h3 h4 ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hK₁ k hk
      · exact hK₂ k hk
    · rw [ObSets.update_cons] at hB
      refine hB.mono fun i o h => ?_
      cases i with
      | zero => exact h
      | succ i => exact update_mono (fun k hk => List.mem_append_right _ hk) i o h
  | lam h1 _ h3 h4 _ ih2 ih5 =>
    have ⟨K₁, hK₁, hA⟩ := collect (P := fun K τ => Obs' _ (ObSets.update _ n (listSet K)) _ τ)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun τ hτ => ih2 τ hτ n
    have ⟨K₂, hK₂, hB⟩ := ih5 (n+1)
    refine ⟨K₁ ++ K₂, fun k hk => ?_, .lam h1
      (fun τ hτ => (hA τ hτ).mono (update_mono fun k hk => List.mem_append_left _ hk))
      h3 h4 ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hK₁ k hk
      · exact hK₂ k hk
    · rw [ObSets.update_cons] at hB
      refine hB.mono fun i o h => ?_
      cases i with
      | zero => exact h
      | succ i => exact update_mono (fun k hk => List.mem_append_right _ hk) i o h
  | app _ h2 _ h4 ih1 ih3 =>
    have ⟨K₁, hK₁, hf⟩ := ih1 n
    have ⟨K₂, hK₂, ha⟩ := collect (P := fun K k => Obs' _ (ObSets.update _ n (listSet K)) _ k)
      (fun _ _ _ hK h => h.mono (update_mono hK)) fun k hk => ih3 k hk n
    refine ⟨K₁ ++ K₂, fun k hk => ?_,
      .app (hf.mono (update_mono fun k hk => List.mem_append_left _ hk)) h2
        (fun k hk => (ha k hk).mono (update_mono fun k hk => List.mem_append_right _ hk)) h4⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact hK₁ k hk
    · exact hK₂ k hk
  | const h1 h2 h3 h4 => exact ⟨[], nofun, .const h1 h2 h3 h4⟩

/-- Compactness at the bound variable of an instantiation. -/
theorem compact0 {S : ObSets} {X : Ob → Prop} (h : Obs' σ (S.cons X) t o) :
    ∃ K : List Ob, (∀ k ∈ K, X k) ∧ Obs' σ (S.cons (listSet K)) t o := by
  have ⟨K, h1, h2⟩ := h.compact 0
  refine ⟨K, h1, h2.mono fun i o h => ?_⟩
  cases i <;> simpa [ObSets.update, ObSets.cons] using h

/-! ## Closed terms -/

theorem _root_.Lean4Lean.VExpr.ClosedN.subst_congr {e : VExpr} {σ σ' : VExpr.Subst}
    (h : e.ClosedN k) (hσ : ∀ i < k, σ i = σ' i) : e.subst σ = e.subst σ' := by
  induction e generalizing k σ σ' with
  | bvar i => exact hσ i h
  | sort | const | elim => rfl
  | app _ _ ih1 ih2 => simp only [VExpr.subst, ih1 h.1 hσ, ih2 h.2 hσ]
  | proj _ _ _ ih => simp only [VExpr.subst, ih h hσ]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp only [VExpr.subst, ih1 h.1 hσ]
    rw [ih2 h.2 fun i hi => ?_]
    cases i with
    | zero => rfl
    | succ i => simp [VExpr.Subst.lift, hσ i (by omega)]

/-- The observations of a term depend only on the valuation of its free variables. -/
theorem closed_iff {t : VExpr} (ht : t.ClosedN k) (hσ : ∀ i < k, σ i = σ' i)
    (hS : ∀ i < k, S i = S' i) : Obs' σ S t o ↔ Obs' σ' S' t o := by
  induction t generalizing k σ σ' S S' o with
  | bvar i => simp only [bvar_iff, hS i ht]
  | sort => simp only [sort_iff]
  | const => simp only [const_iff]
  | elim => simp only [elim_iff]
  | proj => simp only [proj_iff]
  | app f a ihf iha =>
    simp only [app_iff, ihf ht.1 hσ hS, iha ht.2 hσ hS, ht.2.subst_congr hσ]
  | lam A t ihA iht =>
    have hσ' : ∀ x, ∀ i < k+1, (σ.cons x) i = (σ'.cons x) i := fun x i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hσ i (by omega)
    have hS' : ∀ X, ∀ i < k+1, (S.cons X) i = (S'.cons X) i := fun X i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hS i (by omega)
    simp only [lam_iff, ihA ht.1 hσ hS, ht.1.subst_congr hσ,
      fun x X o => iht (o := o) ht.2 (hσ' x) (hS' X)]
  | forallE A B ihA ihB =>
    have hσ' : ∀ x, ∀ i < k+1, (σ.cons x) i = (σ'.cons x) i := fun x i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hσ i (by omega)
    have hS' : ∀ X, ∀ i < k+1, (S.cons X) i = (S'.cons X) i := fun X i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hS i (by omega)
    simp only [forallE_iff, ihA ht.1 hσ hS, ht.1.subst_congr hσ,
      fun x => ht.2.subst_congr (hσ' x), fun x X o => ihB (o := o) ht.2 (hσ' x) (hS' X)]

theorem closed_iff_id {t : VExpr} (ht : t.ClosedN) : Obs' σ S t o ↔ Obs' .id .empty t o :=
  closed_iff ht (fun _ h => nomatch h) (fun _ h => nomatch h)

end Obs

/-! ## Typed observations at a type, typed valuations -/

theorem TypedAt.mono_le (h : TypedAt env U Δ σ S T o)
    (hT : Ob.Sub (Obs' σ S T) (Obs' σ' S' T')) : TypedAt env U Δ σ' S' T' o := by
  obtain ⟨τs, h1, h2⟩ := h
  have ⟨τs', h3, h4⟩ := exists_list_cover (L := τs) (R := fun y x => y ≼ x)
    fun τ hτ => hT τ (h1 τ hτ)
  exact ⟨τs', h3, h2.strengthen h4⟩

/-- Finitely many typed observations are typed at one common list. -/
theorem TypedAt.merge {K : List Ob} (h : ∀ k ∈ K, TypedAt env U Δ σ S T k) :
    ∃ τs, (∀ τ ∈ τs, Obs' σ S T τ) ∧ ∀ k ∈ K, TypedOb env U Δ k τs := by
  have ⟨τs, h1, h2⟩ := Obs.collect (Q := fun τ => Obs' σ S T τ)
    (P := fun τs k => TypedOb env U Δ k τs) (fun _ _ _ hK h => h.mono hK) fun k hk =>
      let ⟨τs, h1, h2⟩ := h k hk; ⟨τs, h1, h2⟩
  exact ⟨τs, h1, h2⟩

theorem TypedAt.of_list (h1 : ∀ τ ∈ τs, Obs' σ S T τ) (h2 : TypedOb env U Δ o τs) :
    TypedAt env U Δ σ S T o := ⟨τs, h1, h2⟩

theorem TypedAt.lift_cons {T : VExpr} (h : TypedAt env U Δ σ S T o) :
    TypedAt env U Δ (σ.cons x) (S.cons X) T.lift o :=
  let ⟨τs, h1, h2⟩ := h; ⟨τs, fun τ hτ => Obs.lift_cons_iff.2 (h1 τ hτ), h2⟩

theorem TV.empty : TV env U Δ Γ σ .empty := fun _ _ _ _ h => nomatch h

theorem TV.cons (h : TV env U Δ Γ σ S) (hK : ∀ k ∈ K, TypedAt env U Δ σ S A k) :
    TV env U Δ (A :: Γ) (σ.cons x) (S.cons (listSet K)) := by
  intro i B hL o ho
  cases hL with
  | zero => exact (hK o ho).lift_cons
  | succ hL => exact (h _ _ hL o ho).lift_cons

end Model
end VEnv
end Lean4Lean
