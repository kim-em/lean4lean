import Lean4Lean.Theory.Typing.Strengthening.SeparatedParallel

/-! # Preservation of a separated pattern's fixed structure

A matching occurrence has no declaration step at its fixed constant positions.
Pattern uniqueness excludes a registered pattern strictly inside another rule's
fixed structure. Parallel computation there therefore acts only on captures.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Every constant position fixed by a match excludes declaration unfolding.
Captured arguments are unrestricted and need not be typed. -/
inductive PatternSkeleton (D : Definitions) : Pattern → VExpr → Prop where
  | const : (∀ rhs, ¬ D.unfolds c levels rhs) → PatternSkeleton D (.const c) (.const c levels)
  | app : PatternSkeleton D p f → PatternSkeleton D q a → PatternSkeleton D (.app p q) (.app f a)
  | var : PatternSkeleton D p f → PatternSkeleton D (.var p) (.app f a)

omit [Params] in
/-- A constant-spine match is protected by non-unfolding of its head alone. -/
theorem PatternSkeleton.spine
    (hm : ((Pattern.const c).varN n).Matches source levels captures)
    (hn : ∀ rhs, ¬ D.unfolds c levels rhs) :
    PatternSkeleton D ((Pattern.const c).varN n) source := by
  induction n generalizing source with
  | zero => cases hm; exact .const hn
  | succ n ih => cases hm with | var hm => exact .var (ih hm)

/-- A registered pattern's recursor position is protected by its separation
certificate, and its constructor positions by environmental rigidity. -/
theorem PatternSkeleton.of_match
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hp : Pat p r) (hm : p.Matches source levels captures)
    (hn : ∀ rhs, ¬ D.unfolds p.headConst levels rhs) : PatternSkeleton D p source := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn c => cases hm; exact .const hn
  | iota rc mr cc kc =>
    cases hm with
    | app hrec hctor =>
      exact .app (.spine hrec (by simpa only [SimplePattern.iota_headConst] using hn))
        (.spine hctor (hr (pat_ctor_rigid hp) _))

omit [Params] in
/-- Every capture is a strict subterm of the matching occurrence. -/
theorem matches_capture_size {p : Pattern} {captures : p.Path → VExpr}
    (hm : p.Matches source levels captures) (path : p.Path) :
    sizeOf (captures path) < sizeOf source := by
  induction hm with
  | const => cases path
  | var hm ih =>
    cases path with
    | none => simp; omega
    | some path => have := ih path; simp; omega
  | app hm1 hm2 ih1 ih2 =>
    cases path with
    | inl path => have := ih1 path; simp; omega
    | inr path => have := ih2 path; simp; omega

/-- Inside a proper fixed subpattern of a registered rule, parallel computation
preserves matching and only computes its captures. Root overlap is excluded by
pattern uniqueness; fixed constants are protected by the skeleton certificate. -/
theorem SeparatedPar.preserve_match (R : SeparatedPar D source out)
    (hp : Pat root rule) (hs : Subpattern p root) (hn : p ≠ root)
    (hm : p.Matches source levels captures) (hf : PatternSkeleton D p source) :
    ∃ captures', p.Matches out levels captures' ∧ ∀ path, SeparatedPar D (captures path) (captures' path) := by
  induction R generalizing p levels with
  | const => cases hm; exact ⟨_, .const, nofun⟩
  | delta HD =>
    cases hm
    cases hf with | const H => exact (H _ HD).elim
  | app RF RA ihf iha =>
    cases hm with
    | var hm =>
      cases hf with | var hf =>
        obtain ⟨caps, HM, HC⟩ := ihf ((Subpattern.varL .refl).trans hs)
          (by rintro rfl; have := hs.sizeOf_le; simp at this; omega) hm hf
        exact ⟨_, .var HM, fun path => path.casesOn RA HC⟩
    | app hmf hma =>
      cases hf with | app hsf hsa =>
        obtain ⟨capsf, HMF, HCF⟩ := ihf ((Subpattern.appL .refl).trans hs)
          (by rintro rfl; have := hs.sizeOf_le; simp at this; omega) hmf hsf
        obtain ⟨capsa, HMA, HCA⟩ := iha ((Subpattern.appR .refl).trans hs)
          (by rintro rfl; have := hs.sizeOf_le; simp at this; omega) hma hsa
        exact ⟨_, .app HMF HMA, fun path => path.casesOn HCF HCA⟩
  | pattern hp' hm' _ _ _ _ =>
    obtain ⟨_, _, _, hi, _⟩ := Pattern.matches_inter.1 ⟨⟨_, _, hm'⟩, ⟨_, _, hm⟩⟩
    obtain ⟨h1, h2, _⟩ := pat_uniq hp hp' hs hi
    exact (hn (h1.trans h2).symm).elim
  | beta => cases hm with | var hm | app hm => cases hm
  | bvar | sort | lam | forallE | proj | projIota => cases hm

end Lean4Lean.VEnv.Strengthening.PureObservation
