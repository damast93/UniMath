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

Section BackdoorExample.
  Context {C : markov_category_with_conditionals}.

(* 
Theorem: For any distribution compatible with the causal structure  

X --> Y
^     ^
 \   / 
  \ / 
   Z

we can compute the causal effect P(Y|do(X)) by adjusting on Z.

P(Y|do(X)) = ∑ P(Y|X,Z)P(Z)
*)

  Context (x y z : C).

  Definition causal_model : UU := 
    (I_{C} --> z) × (z --> x) × (x ⊗ z --> y).

  Definition intervene_x (m : causal_model) : x --> y.
  Proof.
    destruct m as (pz & px & py).
    refine (mon_rinvunitor _ · (identity x #⊗ pz) · py).
  Defined.

  Definition joint (m : causal_model) : I_{C} --> x ⊗ z ⊗ y.
  Proof.
    destruct m as (pz & px & py).
    exact (pz · ⟨px, identity z⟩ · ⟨identity _, py⟩).
  Defined.  

  (* explicit formula to compute the intervention *)

  Definition y_do_x_formula (p : I_{C} --> x ⊗ z ⊗ y) : x --> y := 
    let pz := p · proj1 · proj2 in
    mon_rinvunitor _ · (identity x #⊗ pz) · p|1.
  
  (* Identifiability proof:
     for any distribution compatible with the causal structure,
     the intervention can be computed extensionally using the formula
  *)

  Section IdentifiabilityProof.
    Context  
      (p : I_{C} --> x ⊗ z ⊗ y)
      (ff : full_support (p · proj1))
      (pz : I_{C} --> z)
      (px : z --> x)
      (py : x ⊗ z --> y)
      (e : p = joint (pz ,, px ,, py)).

    Local Lemma lem1 : p|1 = py.
    Proof.
      apply ff.
      apply ase_symm.
      apply conditional_distribution_1_ase_unique.
      rewrite e.
      unfold joint.
      rewrite <- !assoc.
      do 2 apply maponpaths.
      rewrite assoc, pairing_proj1, id_left.
      reflexivity.
    Qed.

    Local Lemma lem2 : p · proj1 · proj2 = pz.
    Proof.
      assert (r : p · proj1 = pz · ⟨px, identity z⟩).
      { rewrite e.
        unfold joint.
        rewrite <- assoc, pairing_proj1, id_right.
        reflexivity. }
      rewrite r, <- assoc, pairing_proj2, id_right.
      reflexivity.
    Qed.

    Lemma identifiability_aux : y_do_x_formula p = intervene_x (pz ,, px ,, py).
    Proof.
      unfold y_do_x_formula, intervene_x.
      rewrite lem1.
      rewrite lem2.
      reflexivity.
    Qed.  

  End IdentifiabilityProof.

  Proposition y_do_x_identifiability
    (p : I_{C} --> x ⊗ z ⊗ y)
    (ff : full_support (p · proj1))
    (m : causal_model)
    (e : p = joint m)
    : y_do_x_formula p = intervene_x m.
  Proof.
    destruct m as (pz & px & py).
    apply identifiability_aux; assumption.
  Qed.

End BackdoorExample.