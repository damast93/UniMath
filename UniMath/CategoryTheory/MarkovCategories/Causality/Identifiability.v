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

(* General identifiability *)

Definition weakly_identifiable {X Y Z : UU} (s : X -> Y) (t : X -> Z) : UU 
  := ∏ x1 x2, s x1 = s x2 -> t x1 = t x2.

Definition strongly_identifiable {X Y Z : UU} (s : X -> Y) (t : X -> Z) : UU 
  := ∑ f : Y -> Z, ∏ x : X, t x = f (s x).

Proposition strongly_identifiable_implies_weakly {X Y Z : UU} {s : X -> Y} {t : X -> Z}
  : strongly_identifiable s t -> weakly_identifiable s t.
Proof.
  intros [f p] x1 x2 q.
  rewrite p, p, q.
  reflexivity.
Qed.

Definition strongly_conditionally_identifiable {X Y Z : UU} (P : Y -> UU) (s : X -> Y) (t : X -> Z) : UU 
  := ∑ f : Y -> Z, ∏ x : X, P (s x) -> t x = f (s x).

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

  (* Accessors *)
  Definition make_causal_model
    (pz : I_{C} --> z)
    (px : z --> x)
    (py : x ⊗ z --> y)
    : causal_model := (pz ,, px ,, py).

  Definition pz (m : causal_model) := pr1 m.
  Definition px (m : causal_model) := pr12 m.
  Definition py (m : causal_model) := pr22 m.

  #[global] Opaque causal_model.

  Definition intervene_x (m : causal_model) : x --> y
    := mon_rinvunitor _ · (identity x #⊗ (pz m)) · (py m).

  Definition joint (m : causal_model) : I_{C} --> x ⊗ z ⊗ y
    := (pz m) · ⟨(px m), identity z⟩ · ⟨identity _, py m⟩.

  (* explicit formula to compute the intervention *)

  Definition adjustment_formula (p : I_{C} --> x ⊗ z ⊗ y) : x --> y := 
    mon_rinvunitor _ · (identity x #⊗ (p · proj1 · proj2)) · p|1.
  
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

    Lemma identifiability_aux : adjustment_formula p = intervene_x (pz ,, px ,, py).
    Proof.
      unfold adjustment_formula, intervene_x.
      rewrite lem1.
      rewrite lem2.
      reflexivity.
    Qed.  

  End IdentifiabilityProof.

  Proposition intervene_x_identifiability
    (p : I_{C} --> x ⊗ z ⊗ y)
    (ff : full_support (p · proj1))
    (m : causal_model)
    (e : p = joint m)
    : adjustment_formula p = intervene_x m.
  Proof.
    destruct m as (pz & px & py).
    apply identifiability_aux; assumption.
  Qed.

  (* We can cast this as a strong identifiability result *)

  (* TODO: Come up with a good notation for strong identifiability
   Notation "given x , { y = s | p } ~> t" 
    := (strongly_conditionally_identifiable (fun y => p) (fun x => s) (fun x => t))
    (at level 0).
  *)

  Theorem intervene_x_strong_identifiability :
    strongly_conditionally_identifiable (fun p => full_support (p · proj1)) joint intervene_x.
  Proof.
    exists adjustment_formula.
    intros m ff.
    refine (!_).
    apply intervene_x_identifiability.
    - exact ff.
    - reflexivity.
  Qed.

End BackdoorExample.


Section SmokingExample.
  Context {C : markov_category_with_conditionals}.

  (* An example of Pearl's front door criterion. Consider the following causal structure

  S -> T -> C 
  ^         ^
  \        /
   \      /
    \    /
       H

  where smoking (S) causes cancer (C), mediated by tar (T). Despite smoking and cancer being
  confounded by hidden factors (H), we can use the do-calculus to derive an expression for P(C|do(S)).

  *)

  Context (s t c : C).

  Definition smoking_model : UU
    := ∑ (h : C)
         , (I_{C} --> h)
         × (h --> s)
         × (s --> t)
         × (t ⊗ h --> c).

  Definition auxcoh {x y z w : C} : x ⊗ (y ⊗ z) ⊗ w --> (x ⊗ y) ⊗ (z ⊗ w)
    := (mon_rassociator _ _ _ #⊗ identity _) · mon_lassociator _ _ _.

  Definition smoking_joint (m : smoking_model) : I_{C} --> s ⊗ t ⊗ c.
  Proof.
    destruct m as (h & ph & ps & pt & pc).
    exact (
      ph · 
        ⟨ps · ⟨ identity s , pt · copy t⟩,
         identity h⟩
      · auxcoh · (identity _ #⊗ pc)).
  Defined.

  Definition smoking_intervention (m : smoking_model) : s --> s ⊗ t ⊗ c.
  Proof.
    destruct m as (h & ph & ps & pt & pc).
    refine (
      mon_rinvunitor _ ·
      (⟨ identity s , pt · copy t ⟩ #⊗ ph)
      · auxcoh
      · (identity _ #⊗ pc)
    ).
  Defined.

  Proposition smoking_intervention_identifiable 
    : strongly_conditionally_identifiable 
      (fun p => full_support (p · proj1))
      smoking_joint
      smoking_intervention.
  Proof.
    (* TODO *)
  Abort.

End SmokingExample.