(*********************************************
Relative Positivity

**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Univalence.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** * 1. Definition of Relative Positivity *)

Section InformationFlowAxioms.
    Context (C : markov_category).

    Definition is_rel_positive : UU
        := ∏ (a x y z : C) (p : a --> x) (f : x --> y) (g : y --> z),
           is_deterministic_ase p (f · g) 
           -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩.

    Proposition isaprop_is_rel_positive
      : isaprop is_rel_positive.
    Proof.
      repeat (use impred ; intro).
      apply isaprop_ase.
    Qed.

End InformationFlowAxioms.

(** * 2. Accessors *)
    
Section Accessors.
    Context (C : markov_category).

    Proposition rel_positivity_r {ispos : is_rel_positive C}
          {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z) :
      is_deterministic_ase p (f · g) -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩.
    Proof. apply ispos. Qed.

    Proposition rel_positivity_l {ispos : is_rel_positive C}
          {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z) :
      is_deterministic_ase p (f · g) -> f · ⟨g, identity _⟩ =_{p} ⟨f · g, f⟩.
    Proof.
      intros det.
      apply cancel_braiding_ase.
      rewrite !assoc', !pairing_sym_mon_braiding.
      use rel_positivity_r; assumption.
    Qed.

    Proposition make_rel_positivity_r :
      (∏ {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z),
        is_deterministic_ase p (f · g) -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩)
      -> is_rel_positive C.
    Proof.
      intros p. exact p.
    Qed.

    Proposition make_rel_positivity_l :
      (∏ {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z),
        is_deterministic_ase p (f · g) -> f · ⟨g, identity _⟩ =_{p} ⟨f · g, f⟩)
      -> is_rel_positive C.
    Proof.
      intros r. 
      apply make_rel_positivity_r.
      intros a x y z p f g d.
      apply cancel_braiding_ase.
      rewrite !assoc', !pairing_sym_mon_braiding.
      apply r.
      assumption.
    Qed.

End Accessors.

(** 4. Implications between the Axioms *)

Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.

Section ImplicationsBetweenAxioms.

(* ase-inverses are ase-deterministic *)

  Proposition ase_inverses_are_ase_deterministic 
    (C : markov_category) (rp : is_rel_positive C) {x y : C}
    (p : I_{C} --> x) (q : I_{C} --> y)
    (f : x --> y) (g : y --> x)
    (pres_f : p · f = q) (pres_g : q · g = p)
    (inv_fg : f · g =_{p} identity x)
    (inv_gf : g · f =_{q} identity y)
    : is_deterministic_ase p f.
  Proof.
    unfold is_deterministic_ase.

    assert(fg_det_ase : is_deterministic_ase p (f · g)).
    { apply is_deterministic_ase_stable with (identity _).
      - apply ase_symm. exact inv_fg.
      - apply deterministic_implies_determinstic_ase.
        apply is_deterministic_identity. } 
      
    (* Show that f, g are necessarily Bayesian inverses of each other *)
    assert(bi : p · ⟨f, identity _⟩ = p · f · ⟨identity _, g⟩).
    { admit. }

    (*
      Strategy: we can show from relative postivity that f, g are Bayesian inverses.
      Then it follows ...
    *)
    admit.
  Admitted.

  
End ImplicationsBetweenAxioms.

#[global] Opaque is_rel_positive.
