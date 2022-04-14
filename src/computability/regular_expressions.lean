/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import tactic.rcases
import computability.language
import computability.DFA

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent.
* `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.
-/

open list set

universe u

variables {α β γ : Type*} [dec : decidable_eq α]

namespace list

@[simp] lemma join_map_singleton : ∀ l : list α, (l.map $ λ a, [a]).join = l
| [] := rfl
| (a :: l) := congr_arg (cons a) (join_map_singleton _)

@[simp] lemma sum_append_singleton [has_zero α] [has_add α] (a : α) (l : list α) :
  (l ++ [a]).sum = l.sum + a :=
foldl_append _ _ _ _

end list
open list

/--
This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive regular_expression (α : Type u) : Type u
| zero : regular_expression
| epsilon : regular_expression
| char : α → regular_expression
| plus : regular_expression → regular_expression → regular_expression
| comp : regular_expression → regular_expression → regular_expression
| star : regular_expression → regular_expression

namespace regular_expression
variables {a b : α}

instance : inhabited (regular_expression α) := ⟨zero⟩

instance : has_add (regular_expression α) := ⟨plus⟩
instance : has_mul (regular_expression α) := ⟨comp⟩
instance : has_one (regular_expression α) := ⟨epsilon⟩
instance : has_zero (regular_expression α) := ⟨zero⟩

attribute [pattern] has_mul.mul

@[simp] lemma zero_def : (zero : regular_expression α) = 0 := rfl
@[simp] lemma one_def : (epsilon : regular_expression α) = 1 := rfl

@[simp] lemma plus_def (P Q : regular_expression α) : plus P Q = P + Q := rfl
@[simp] lemma comp_def (P Q : regular_expression α) : comp P Q = P * Q := rfl

/-- `matches P` provides a language which contains all strings that `P` matches -/
@[simp] def matches : regular_expression α → language α
| 0 := 0
| 1 := 1
| (char a) := {[a]}
| (P + Q) := P.matches + Q.matches
| (P * Q) := P.matches * Q.matches
| (star P) := P.matches.star

@[simp] lemma matches_zero : (0 : regular_expression α).matches = 0 := rfl
@[simp] lemma matches_epsilon : (1 : regular_expression α).matches = 1 := rfl
@[simp] lemma matches_char (a : α) : (char a).matches = {[a]} := rfl
@[simp] lemma matches_add (P Q : regular_expression α) :
  (P + Q).matches = P.matches + Q.matches := rfl
@[simp] lemma matches_mul (P Q : regular_expression α) :
  (P * Q).matches = P.matches * Q.matches := rfl
@[simp] lemma matches_star (P : regular_expression α) : P.star.matches = P.matches.star := rfl

-- Note: This is NOT obvious because `regular_expression α` is not an `add_zero_class`
@[simp] lemma matches_sum (l : list (regular_expression α)) : l.sum.matches = (l.map matches).sum :=
begin
  induction l using list.reverse_rec_on with l P ih,
  { refl },
  { simp_rw [map_append, map_singleton, sum_append_singleton, matches_add, ih] }
end

/-- `match_epsilon P` is true if and only if `P` matches the empty string -/
def match_epsilon : regular_expression α → bool
| 0 := ff
| 1 := tt
| (char _) := ff
| (P + Q) := P.match_epsilon || Q.match_epsilon
| (P * Q) := P.match_epsilon && Q.match_epsilon
| (star P) := tt

include dec

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : regular_expression α → α → regular_expression α
| 0 _ := 0
| 1 _ := 0
| (char a₁) a₂ := if a₁ = a₂ then 1 else 0
| (P + Q) a := deriv P a + deriv Q a
| (P * Q) a :=
  if P.match_epsilon then
    deriv P a * Q + deriv Q a
  else
    deriv P a * Q
| (star P) a := deriv P a * star P

@[simp] lemma deriv_zero (a : α) : deriv 0 a = 0 := rfl
@[simp] lemma deriv_one (a : α) : deriv 1 a = 0 := rfl
@[simp] lemma deriv_char_self (a : α) : deriv (char a) a = 1 := if_pos rfl
@[simp] lemma deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 := if_neg h
@[simp] lemma deriv_add (P Q : regular_expression α) (a : α) :
  deriv (P + Q) a = deriv P a + deriv Q a := rfl
@[simp] lemma deriv_star (P : regular_expression α) (a : α) :
  deriv (P.star) a = deriv P a * star P := rfl

@[simp] lemma deriv_sum (L : list (regular_expression α)) : L.sum.deriv = (L.map deriv).sum :=
begin
  ext a,
  induction L using list.reverse_rec_on with l P ih,
  { refl },
  { simp_rw [map_append, map_singleton, sum_append_singleton, deriv_add, ih],
    refl }
end

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches`. -/
def rmatch : regular_expression α → list α → bool
| P [] := match_epsilon P
| P (a::as) := rmatch (P.deriv a) as

@[simp] lemma zero_rmatch (x : list α) : rmatch 0 x = ff :=
by induction x; simp [rmatch, match_epsilon, *]

lemma one_rmatch_iff (x : list α) : rmatch 1 x ↔ x = [] :=
by induction x; simp [rmatch, match_epsilon, *]

lemma char_rmatch_iff (a : α) (x : list α) : rmatch (char a) x ↔ x = [a] :=
begin
  cases x with _ x,
    dec_trivial,
  cases x,
    rw [rmatch, deriv],
    split_ifs;
    tauto,
  rw [rmatch, deriv],
  split_ifs,
    rw one_rmatch_iff,
    tauto,
  rw zero_rmatch,
  tauto
end

lemma add_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
begin
  induction x with _ _ ih generalizing P Q,
  { simp only [rmatch, match_epsilon, bor_coe_iff] },
  { repeat {rw rmatch},
    rw deriv,
    exact ih _ _ }
end

lemma mul_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P * Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
begin
  induction x with a x ih generalizing P Q,
  { rw [rmatch, match_epsilon],
    split,
    { intro h,
      refine ⟨ [], [], rfl, _ ⟩,
      rw [rmatch, rmatch],
      rwa band_coe_iff at h },
    { rintro ⟨ t, u, h₁, h₂ ⟩,
      cases list.append_eq_nil.1 h₁.symm with ht hu,
      subst ht,
      subst hu,
      repeat {rw rmatch at h₂},
      simp [h₂] } },
  { rw [rmatch, deriv],
    split_ifs with hepsilon,
    { rw [add_rmatch_iff, ih],
      split,
      { rintro (⟨ t, u, _ ⟩ | h),
        { exact ⟨ a :: t, u, by tauto ⟩ },
        { exact ⟨ [], a :: x, rfl, hepsilon, h ⟩ } },
      { rintro ⟨ t, u, h, hP, hQ ⟩,
        cases t with b t,
        { right,
          rw list.nil_append at h,
          rw ←h at hQ,
          exact hQ },
        { left,
          simp only [list.cons_append] at h,
          refine ⟨ t, u, h.2, _, hQ ⟩,
          rw rmatch at hP,
          convert hP,
          exact h.1 } } },
    { rw ih,
      split;
      rintro ⟨ t, u, h, hP, hQ ⟩,
      { exact ⟨ a :: t, u, by tauto ⟩ },
      { cases t with b t,
        { contradiction },
        { simp only [list.cons_append] at h,
          refine ⟨ t, u, h.2, _, hQ ⟩,
          rw rmatch at hP,
          convert hP,
          exact h.1 } } } }
end

lemma star_rmatch_iff (P : regular_expression α) : ∀ (x : list α),
  (star P).rmatch x ↔ ∃ S : list (list α), x = S.join ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t
| x :=
begin
  have A : ∀ (m n : ℕ), n < m + n + 1,
  { assume m n,
    convert add_lt_add_of_le_of_lt (add_le_add (zero_le m) (le_refl n)) zero_lt_one,
    simp },
  have IH := λ t (h : list.length t < list.length x), star_rmatch_iff t,
  clear star_rmatch_iff,
  split,
  { cases x with a x,
    { intro,
      fconstructor,
      exact [],
      tauto },
    { rw [rmatch, deriv, mul_rmatch_iff],
      rintro ⟨ t, u, hs, ht, hu ⟩,
      have hwf : u.length < (list.cons a x).length,
      { rw [hs, list.length_cons, list.length_append],
        apply A },
      rw IH _ hwf at hu,
      rcases hu with ⟨ S', hsum, helem ⟩,
      use (a :: t) :: S',
      split,
      { simp [hs, hsum] },
      { intros t' ht',
        cases ht' with ht' ht',
        { rw ht',
          exact ⟨ dec_trivial, ht ⟩ },
        { exact helem _ ht' } } } },
  { rintro ⟨ S, hsum, helem ⟩,
    cases x with a x,
    { dec_trivial },
    { rw [rmatch, deriv, mul_rmatch_iff],
      cases S with t' U,
      { exact ⟨ [], [], by tauto ⟩ },
      { cases t' with b t,
        { simp only [forall_eq_or_imp, list.mem_cons_iff] at helem,
          simp only [eq_self_iff_true, not_true, ne.def, false_and] at helem,
          cases helem },
        simp only [list.join, list.cons_append] at hsum,
        refine ⟨ t, U.join, hsum.2, _, _ ⟩,
        { specialize helem (b :: t) (by simp),
          rw rmatch at helem,
          convert helem.2,
          exact hsum.1 },
        { have hwf : U.join.length < (list.cons a x).length,
          { rw [hsum.1, hsum.2],
            simp only [list.length_append, list.length_join, list.length],
            apply A },
          rw IH _ hwf,
          refine ⟨ U, rfl, λ t h, helem t _ ⟩,
          right,
          assumption } } } }
end
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨(λ L₁ L₂ : list _, L₁.length < L₂.length), inv_image.wf _ nat.lt_wf⟩] }

@[simp] lemma rmatch_iff_matches (P : regular_expression α) :
  ∀ x : list α, P.rmatch x ↔ x ∈ P.matches :=
begin
  intro x,
  induction P generalizing x,
  all_goals
  { try {rw zero_def},
    try {rw one_def},
    try {rw plus_def},
    try {rw comp_def},
    rw matches },
  case zero :
  { rw zero_rmatch,
    tauto },
  case epsilon :
  { rw one_rmatch_iff,
    refl },
  case char :
  { rw char_rmatch_iff,
    refl },
  case plus : _ _ ih₁ ih₂
  { rw [add_rmatch_iff, ih₁, ih₂],
    refl },
  case comp : P Q ih₁ ih₂
  { simp only [mul_rmatch_iff, comp_def, language.mul_def, exists_and_distrib_left, set.mem_image2,
      set.image_prod],
    split,
    { rintro ⟨ x, y, hsum, hmatch₁, hmatch₂ ⟩,
      rw ih₁ at hmatch₁,
      rw ih₂ at hmatch₂,
      exact ⟨ x, hmatch₁, y, hmatch₂, hsum.symm ⟩ },
    { rintro ⟨ x, hmatch₁, y, hmatch₂, hsum ⟩,
      rw ←ih₁ at hmatch₁,
      rw ←ih₂ at hmatch₂,
      exact ⟨ x, y, hsum.symm, hmatch₁, hmatch₂ ⟩ } },
  case star : _ ih
  { rw [star_rmatch_iff, language.star_def_nonempty],
    split,
    all_goals
    { rintro ⟨ S, hx, hS ⟩,
      refine ⟨ S, hx, _ ⟩,
      intro y,
      specialize hS y },
    { rw ←ih y,
      tauto },
    { rw ih y,
      tauto } }
end

instance (P : regular_expression α) : decidable_pred P.matches :=
begin
  intro x,
  change decidable (x ∈ P.matches),
  rw ←rmatch_iff_matches,
  exact eq.decidable _ _
end

omit dec

/-- Map the alphabet of a regular expression. -/
@[simp] def map (f : α → β) : regular_expression α → regular_expression β
| 0 := 0
| 1 := 1
| (char a) := char (f a)
| (R + S) := map R + map S
| (R * S) := map R * map S
| (star R) := star (map R)

@[simp] lemma map_id : ∀ (P : regular_expression α), P.map id = P
| 0 := rfl
| 1 := rfl
| (char a) := rfl
| (R + S) := by simp_rw [map, map_id]
| (R * S) := by simp_rw [map, map_id]
| (star R) := by simp_rw [map, map_id]

@[simp] lemma map_map (g : β → γ) (f : α → β) :
  ∀ (P : regular_expression α), (P.map f).map g = P.map (g ∘ f)
| 0 := rfl
| 1 := rfl
| (char a) := rfl
| (R + S) := by simp_rw [map, map_map]
| (R * S) := by simp_rw [map, map_map]
| (star R) := by simp_rw [map, map_map]

/-- The language of the map is the map of the language. -/
@[simp] lemma matches_map (f : α → β) :
  ∀ P : regular_expression α, (P.map f).matches = language.map f P.matches
| 0 := (map_zero _).symm
| 1 := (map_one _).symm
| (char a) := by { rw eq_comm, exact image_singleton }
| (R + S) := by simp only [matches_map, map, matches_add, map_add]
| (R * S) := by simp only [matches_map, map, matches_mul, map_mul]
| (star R) := begin
    simp_rw [map, matches, matches_map],
    rw [language.star_eq_supr_pow, language.star_eq_supr_pow],
    simp_rw ←map_pow,
    exact image_Union.symm,
  end

/-- The wildcard. -/
def wild (l : list α) : regular_expression α := (l.map char).sum

@[simp] lemma wild_nil : wild ([] : list α) = 0 := rfl

@[simp] lemma matches_wild (l : list α) : (wild l).matches = (l.map $ λ a, {[a]}).sum :=
by { rw [wild, matches_sum, list.map_map], refl }

lemma mem_matches_wild_iff {l x : list α} : x ∈ (wild l).matches ↔ ∃ a ∈ l, x = [a] := by simp

lemma deriv_wild [decidable_eq α] (l : list α) (a : α) :
  (wild l).deriv a = if a ∈ l then 1 else 0 :=
begin
  rw [wild, deriv_sum, list.map_map],
  sorry
end

def any' {n : nat} : regular_expression (fin n) := (wild $ fin_range _).star

lemma any'_matches_any {n : nat} (x : list (fin n)) : any'.matches x :=
⟨x.map (λ a, [a]), x.join_map_singleton.symm, by simp⟩

lemma fin_univ_succ {n : nat} : (@fin.cast_succ n) '' set.univ ∪ {n} = set.univ :=
begin
  ext x,
  split,
    tauto,
  have : x ≤ n := fin.le_coe_last x,
  cases (le_iff_lt_or_eq.1 this) with h h,
  { simp only [set.image_univ, set.mem_insert_iff, set.mem_univ, forall_true_left, set.mem_set_of_eq, fin.range_cast_succ,
      set.union_singleton],
    right,
    rw [←fin.coe_fin_lt, fin.coe_coe_of_lt] at h,
    assumption,
    simp },
  simp [h],
end

def to_regular_expression : Π {n : nat} (σ ≃ fin n), DFA α σ → regular_expression α
| 0 σ E M := absurd (E M.start).property (nat.not_lt_zero _)
| 1 σ E M :=
    if (E.inv_fun 0 ∈ M.accept) then ()
| (n+2) e M := sorry



end regular_expression
