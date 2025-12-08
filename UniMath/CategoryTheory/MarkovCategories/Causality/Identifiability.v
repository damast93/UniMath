(*********************************************
Identifiability

This file contains some experiments into causal identifiability and the do-calculus, 
formulated in the language of Markov categories.

References
- J. Pearl - 'Causality' (2009)
- B. Jacobs, A. Kissinger, F. Zanasi - 'Causal inference via string diagram surgery: A diagrammatic approach to interventions and counterfactuals'
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.Univalence.

Require Import UniMath.CategoryTheory.MarkovCategories.State.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

Definition full_support {C : markov_category} {x : C} (p : I_{C} --> x) : UU
  := ∏ (y : C) (f g : x --> y), (f =_{p} g) -> f = g.  

Section BackdoorExample.
  Context {C : markov_category_with_conditionals}.

(* 
In the causal structure  

X --> Y
^     ^
 \   / 
  \ / 
   Z

we can compute the causal effect P(Y|do(X)) by adjusting on Z.
*)

  Context (x y z : C).

  Definition causal_model : UU := 
    (I_{C} --> z) × (z --> x) × (x ⊗ z --> y).

  Definition y_do_x (m : causal_model) : x --> y.
  Proof.
    destruct m as (pz & px & py).
    refine (mon_rinvunitor _ · (identity x #⊗ pz) · py).
  Defined.

  Definition joint (m : causal_model) : I_{C} --> x ⊗ z ⊗ y.
  Proof.
    destruct m as (pz & px & py).
    exact (pz · ⟨px, identity z⟩ · ⟨identity _, py⟩).
  Defined.  

  Proposition y_do_x_identifiable1 
    (m1 m2 : causal_model) 
    (e : joint m1 = joint m2)
    :  y_do_x m1 = y_do_x m2.
  Proof.
  Admitted.

  (* support fn *)
  Definition y_do_x_compute
    (pxzy : I_{C} --> x ⊗ z ⊗ y)
    : x --> y.
  Proof.
  Admitted.

  (* exists fn, ... *)

  Proposition y_do_x_identifiable2 
    (m : causal_model)
    : y_do_x_compute (joint m) = y_do_x m.
  Proof.
  Admitted.

  
  Proposition y_do_x_identifiable3 
    (pxzy : I_{C} --> x ⊗ z ⊗ y)
    (m : causal_model)
    (e : pxzy = joint m)
    (ff : full_support pxzy)
    : y_do_x_compute pxzy = y_do_x m.
  Proof.
  Admitted.

End BackdoorExample.