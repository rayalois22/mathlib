/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.zmod.basic
import group_theory.quotient_group
import ring_theory.int.basic

/-!
# `zmod n` and quotient groups / rings

This file relates `zmod n` to the quotient group
`quotient_add_group.quotient (add_subgroup.zmultiples n)` and to the quotient ring
`(ideal.span {n}).quotient`.

## Main definitions

 - `zmod.quotient_zmultiples_nat_equiv_zmod` and `zmod.quotient_zmultiples_equiv_zmod`:
   `zmod n` is the group quotient of `ℤ` by `n ℤ := add_subgroup.zmultiples (n)`,
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.quotient_span_nat_equiv_zmod` and `zmod.quotient_span_equiv_zmod`:
   `zmod n` is the ring quotient of `ℤ` by `n ℤ : ideal.span {n}`
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.lift n f` is the map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group, quotient ring, ideal quotient
-/

open quotient_add_group
open zmod

variables (n : ℕ) {A R : Type*} [add_group A] [ring R]

namespace int

/-- `ℤ` modulo multiples of `n : ℕ` is `zmod n`. -/
def quotient_zmultiples_nat_equiv_zmod :
  quotient (add_subgroup.zmultiples (n : ℤ)) ≃+ zmod n :=
(equiv_quotient_of_eq (zmod.ker_int_cast_add_hom _)).symm.trans $
quotient_ker_equiv_of_right_inverse (int.cast_add_hom (zmod n)) coe int_cast_zmod_cast

/-- `ℤ` modulo multiples of `a : ℤ` is `zmod a.nat_abs`. -/
def quotient_zmultiples_equiv_zmod (a : ℤ) :
  quotient (add_subgroup.zmultiples a) ≃+ zmod a.nat_abs :=
(equiv_quotient_of_eq (zmultiples_nat_abs a)).symm.trans
  (quotient_zmultiples_nat_equiv_zmod a.nat_abs)

/-- `ℤ` modulo the ideal generated by `n : ℕ` is `zmod n`. -/
def quotient_span_nat_equiv_zmod :
  (ideal.span {↑n}).quotient ≃+* zmod n :=
(ideal.quot_equiv_of_eq (zmod.ker_int_cast_ring_hom _)).symm.trans $
  ring_hom.quotient_ker_equiv_of_right_inverse $
  show function.right_inverse coe (int.cast_ring_hom (zmod n)),
  from int_cast_zmod_cast

/-- `ℤ` modulo the ideal generated by `a : ℤ` is `zmod a.nat_abs`. -/
def quotient_span_equiv_zmod (a : ℤ) :
  (ideal.span ({a} : set ℤ)).quotient ≃+* zmod a.nat_abs :=
(ideal.quot_equiv_of_eq (span_nat_abs a)).symm.trans
  (quotient_span_nat_equiv_zmod a.nat_abs)

end int
