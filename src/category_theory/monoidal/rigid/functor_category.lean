/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.rigid.basic
import category_theory.monoidal.functor_category

/-!
# Functors from a groupoid into a right/left rigid category form a right/left rigid category.

(Using the pointwise monoidal structure on the functor category.)
-/

noncomputable theory

open category_theory
open category_theory.monoidal_category

variables {C D : Type*} [groupoid C] [category D] [monoidal_category D]

instance functor_has_right_dual [right_rigid_category D] (F : C ⥤ D) : has_right_dual F :=
{ right_dual :=
  { obj := λ X, (F.obj X)ᘁ,
    map := λ X Y f, (F.map (inv f))ᘁ,
    map_comp' := λ X Y Z f g, by { simp [comp_right_adjoint_mate], }, },
  exact :=
  { evaluation :=
    { app := λ X, ε_ _ _,
      naturality' := λ X Y f, begin
        dsimp,
        rw [category.comp_id, functor.map_inv,
          ←id_tensor_comp_tensor_id, category.assoc, right_adjoint_mate_comp_evaluation,
          ←category.assoc, ←id_tensor_comp, is_iso.hom_inv_id, tensor_id, category.id_comp],
      end },
    coevaluation :=
    { app := λ X, η_ _ _,
      naturality' := λ X Y f, begin
        dsimp,
        rw [functor.map_inv, category.id_comp,
           ←id_tensor_comp_tensor_id, ←category.assoc, coevaluation_comp_right_adjoint_mate_comp,
          category.assoc, ←comp_tensor_id, is_iso.inv_hom_id, tensor_id, category.comp_id],
      end, }, }, }

instance right_rigid_functor_category [right_rigid_category D] : right_rigid_category (C ⥤ D) := {}
