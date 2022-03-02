/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn
-/
import data.pnat.basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `nat.find`.

-/

namespace pnat

variables {p q : ℕ+ → Prop} [decidable_pred p] [decidable_pred q] (h : ∃ n, p n)

instance decidable_pred_exists_nat :
  decidable_pred (λ n' : ℕ, ∃ (n : ℕ+) (hn : n' = n), p n)
| 0       := is_false begin
    push_neg,
    rintro ⟨x, hx⟩,
    simp [hx.ne]
  end
| (n' + 1) := if hp : p (n' + 1).to_pnat' then is_true ⟨(n' + 1).to_pnat', rfl, hp⟩
  else is_false $ begin
    contrapose! hp,
    obtain ⟨n, hn, hp⟩ := hp,
    simp [hn, hp]
  end

include h

/--
If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `pnat.find hp` is the
smallest positive natural number satisfying `p`. Note that `pnat.find` is protected,
meaning that you can't just write `find`, even if the `pnat` namespace is open.

The API for `pnat.find` is:

* `pnat.find_spec` is the proof that `pnat.find hp` satisfies `p`.
* `pnat.find_min` is the proof that if `m < pnat.find hp` then `m` does not satisfy `p`.
* `pnat.find_min'` is the proof that if `m` does satisfy `p` then `pnat.find hp ≤ m`.
-/
protected def find_aux
  (H' : ∃ (n' : ℕ) (n : ℕ+) (hn' : n' = n), p n := exists.elim h (λ n hn, ⟨n, n, rfl, hn⟩)) : ℕ :=
nat.find H'

protected theorem find_aux_spec
  (H' : ∃ (n' : ℕ) (n : ℕ+) (hn' : n' = n), p n := exists.elim h (λ n hn, ⟨n, n, rfl, hn⟩)) :
  ∃ (n : ℕ+) (hn' : pnat.find_aux h = n), p n :=
nat.find_spec H'

/--
If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `pnat.find hp` is the
smallest positive natural number satisfying `p`. Note that `pnat.find` is protected,
meaning that you can't just write `find`, even if the `pnat` namespace is open.

The API for `pnat.find` is:

* `pnat.find_spec` is the proof that `pnat.find hp` satisfies `p`.
* `pnat.find_min` is the proof that if `m < pnat.find hp` then `m` does not satisfy `p`.
* `pnat.find_min'` is the proof that if `m` does satisfy `p` then `pnat.find hp ≤ m`.
-/
protected def find : ℕ+ :=
⟨pnat.find_aux h, begin
  obtain ⟨⟨n, hn⟩, h, -⟩ := pnat.find_aux_spec h,
  rw h,
  exact hn
end⟩

protected theorem find_spec : p (pnat.find h) :=
begin
  rw pnat.find,
  obtain ⟨n, h, hp⟩ := pnat.find_aux_spec h,
  simp [h, hp]
end

protected theorem find_min : ∀ {m : ℕ+}, m < pnat.find h → ¬p m :=
begin
  simp only [pnat.find, ←pnat.coe_lt_coe, pnat.find_aux, mk_coe, nat.lt_find_iff, exists_prop,
             not_exists, not_and],
  rintro ⟨m, hm⟩,
  contrapose!,
  intro h,
  refine ⟨m, le_rfl, m.to_pnat', _, _⟩,
  { simp [hm] },
  { convert h,
    simp [subtype.ext_iff, hm] }
end

protected theorem find_min' {m : ℕ+} (hm : p m) : pnat.find h ≤ m :=
le_of_not_lt (λ l, pnat.find_min h l hm)

variables {n m : ℕ+}

lemma find_eq_iff : pnat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n :=
begin
  split,
  { rintro rfl, exact ⟨pnat.find_spec h, λ _, pnat.find_min h⟩ },
  { rintro ⟨hm, hlt⟩,
    exact le_antisymm (pnat.find_min' h hm) (not_lt.1 $ imp_not_comm.1 (hlt _) $ pnat.find_spec h) }
end

@[simp] lemma find_lt_iff (n : ℕ+) : pnat.find h < n ↔ ∃ m < n, p m :=
⟨λ h2, ⟨pnat.find h, h2, pnat.find_spec h⟩, λ ⟨m, hmn, hm⟩, (pnat.find_min' h hm).trans_lt hmn⟩

@[simp] lemma find_le_iff (n : ℕ+) : pnat.find h ≤ n ↔ ∃ m ≤ n, p m :=
by simp only [exists_prop, ← lt_add_one_iff, find_lt_iff]

@[simp] lemma le_find_iff (n : ℕ+) : n ≤ pnat.find h ↔ ∀ m < n, ¬ p m :=
by simp_rw [← not_lt, find_lt_iff, not_exists]

@[simp] lemma lt_find_iff (n : ℕ+) : n < pnat.find h ↔ ∀ m ≤ n, ¬ p m :=
by simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]

@[simp] lemma find_eq_one : pnat.find h = 1 ↔ p 1 :=
by simp [find_eq_iff]

@[simp] lemma one_le_find : 1 < pnat.find h ↔ ¬ p 1 :=
not_iff_not.mp $ by simp

theorem find_mono (h : ∀ n, q n → p n)
  {hp : ∃ n, p n} {hq : ∃ n, q n} :
  pnat.find hp ≤ pnat.find hq :=
pnat.find_min' _ (h _ (pnat.find_spec hq))

lemma find_le {h : ∃ n, p n} (hn : p n) : pnat.find h ≤ n :=
(pnat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬ p 1) :
  pnat.find h₁ = pnat.find h₂ + 1 :=
begin
  refine (find_eq_iff _).2 ⟨pnat.find_spec h₂, λ n hn, _⟩,
  revert n,
  intro n,
  refine pnat.rec_on n _ _,
  { simp [h1] },
  intros m IH hm,
  simp only [add_lt_add_iff_right, lt_find_iff] at hm,
  exact hm _ le_rfl
end

end pnat
