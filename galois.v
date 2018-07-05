Require Import Omega.
Require Import Ensembles.
Require Import Classical_sets.

Module Type Poset.
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.

  Axiom eq_refl : forall x, eq x x.
  Axiom eq_sym : forall x y, eq x y -> eq y x.
  Axiom eq_trans : forall x y z, eq x y -> eq y z -> eq x z.

  Parameter order : t -> t -> Prop.

  Axiom order_refl : forall x y, eq x y -> order x y.
  Axiom order_antisym: forall x y, order x y -> order y x -> eq x y.
  Axiom order_trans : forall x y z, order x y -> order y z ->  order x z.
End Poset.

(*-------------------------------------------------------------------------------*)

Module Type Galois (A : Poset) (C : Poset).
  Parameter alpha : C.t -> A.t.
  Parameter gamma : A.t -> C.t.

  Axiom connection1 : forall (a : A.t) (c : C.t), C.order c (gamma (alpha c)) <-> A.order (alpha (gamma a)) a.
  Axiom connection2 : forall (a : A.t) (c : C.t), C.order c (gamma a) <-> A.order (alpha c) a.
End Galois.

(*-------------------------------------------------------------------------------*)

Module PosetEnsembleNat <: Poset.
  Definition t : Type := Ensemble nat.
  Definition eq : t -> t -> Prop := (fun t1 t2 => t1 = t2).

Check eq.
Check t.
Eval compute in eq.

  Theorem eq_refl : forall x, eq x x.
  Proof.
    reflexivity.
   Qed.

  Theorem eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    intros x y.
    intros H.
    unfold eq in *.
    subst.
    reflexivity.
  Qed.

  Theorem eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z.
    intros H0 H1.
    unfold eq in *.
    subst.
    reflexivity.
  Qed.

  Definition order : t -> t -> Prop := (fun t1 t2 => Included _ t1 t2).

  Theorem order_refl : forall x y, eq x y -> order x y.
  Proof.
    intros x y.
    intros H.
    unfold eq in *.
    unfold order.
    unfold Included.
    intros x0.
    intros H0.
    unfold In in *.
    subst.
    assumption.
  Qed.

  Theorem order_antisym : forall x y, order x y -> order y x -> eq x y.
  Proof.
    intros x y.
    intros H0 H1.
    unfold eq.
    apply Extensionality_Ensembles.
    unfold Same_set.
    split.
    assumption.
    unfold order in H1.
    assumption.
  Qed.

  Theorem order_trans : forall x y z, order x y -> order y z -> order x z.
  Proof.
    intros x y z.
    unfold order.
    unfold Included.
    unfold In.
    intros x_y y_z.
    intros x0.
    auto.
  Qed.

End PosetEnsembleNat.

(*-------------------------------------------------------------------------------*)

Inductive EO :=
|even : EO
|odd : EO.

Module EvenOdd <: Poset.
  Definition t : Type := Ensemble EO.
  Definition eq : t -> t -> Prop := (fun t1 t2 => t1 = t2).

  Theorem eq_refl : forall x, eq x x.
  Proof.
    reflexivity.
   Qed.

  Theorem eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    intros x y.
    intros H.
    unfold eq in *.
    subst.
    reflexivity.
  Qed.

  Theorem eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z.
    intros H0 H1.
    unfold eq in *.
    subst.
    reflexivity.
  Qed.

  Definition order : t -> t -> Prop := (fun t1 t2 => Included EO t1 t2).

  Theorem order_refl : forall x y, eq x y -> order x y.
  Proof.
    intros x y.
    intros H.
    unfold eq in *.
    unfold order.
    unfold Included.
    intros x0.
    intros H0.
    unfold In in *.
    subst.
    assumption.
  Qed.

  Theorem order_antisym : forall x y, order x y -> order y x -> eq x y.
  Proof.
    intros x y.
    intros H0 H1.
    unfold eq.
    apply Extensionality_Ensembles.
    unfold Same_set.
    split.
    assumption.
    unfold order in H1.
    assumption.
  Qed.

  Theorem order_trans : forall x y z, order x y -> order y z -> order x z.
  Proof.
    intros x y z.
    unfold order.
    unfold Included.
    unfold In.
    intros x_y y_z.
    intros x0.
    auto.
  Qed.

End EvenOdd.

(*-------------------------------------------------------------------------------*)

Definition evenness x :=
  x mod 2 = 0.
Definition EvenSet :=
  Singleton EO even.

Definition oddness x :=
  x mod 2 = 1.
Definition OddSet :=
  Singleton EO odd.

Module GaloisEvenOdd <: (Galois EvenOdd PosetEnsembleNat).

Inductive alphaR : Ensemble nat -> Ensemble EO -> Prop :=
|Even_intro_a : forall x : Ensemble nat, x <> Empty_set nat -> Included nat x evenness -> alphaR x EvenSet
|Odd_intro_a : forall x : Ensemble nat, x <> Empty_set nat -> Included nat x oddness -> alphaR x OddSet
|Bottom_intro_a : alphaR (Empty_set nat) (Empty_set EO)
|Top_intro_a : forall x : Ensemble nat, x <> Empty_set nat -> ~(Included nat x evenness) -> ~(Included nat x oddness) -> alphaR x (Full_set EO).
(*Try to find an alternative to Top_intro_a*)

Inductive gammaR : Ensemble EO -> Ensemble nat -> Prop :=
|Even_intro_g : gammaR EvenSet evenness
|Odd_intro_g : gammaR OddSet oddness
|Bottom_intro_g : gammaR (Empty_set EO) (Empty_set nat)
|Top_intro_g : gammaR (Full_set EO) (Full_set nat).

Lemma alphaEx : alphaR (Add _ (Add _ (Empty_set nat) 1) 2) (Full_set EO).
Proof.
  apply Top_intro_a.
  apply Add_not_Empty.
  intros H.
  unfold Included in H.
  unfold Add in H.
  unfold evenness in H.
  specialize H with 1.
  simpl in H.
  cbv in H.
  assert (Union nat (Union nat (Empty_set nat) (Singleton nat 1)) (Singleton nat 2) 1).
  apply Union_introl.
  apply Union_intror.
  cbv.
  apply In_singleton.
  intuition.
  intros H.
  unfold Included in H.
  unfold Add in H.
  unfold evenness in H.
  specialize H with 2.
  simpl in H.
  cbv in H.
  assert (Union nat (Union nat (Empty_set nat) (Singleton nat 1)) (Singleton nat 2) 2).
  apply Union_intror.
  cbv.
  apply In_singleton.
  intuition.
Qed.

Lemma xIncludedOddnessEvennessIsEmpty : forall x : Ensemble nat, Included nat x oddness -> Included nat x evenness -> x = Empty_set nat.
Proof.
intros x H0 H1.
apply Extensionality_Ensembles.
unfold Same_set.
split.
unfold Included in *.
unfold oddness in H0.
unfold evenness in H1.
intros x0.
intros H2.
specialize H0 with x0.
specialize H1 with x0.
intuition.
unfold In in *.
intuition.
rewrite H in H0.
inversion H0.

unfold Included.
intros x0.
intros H2.
inversion H2.
Qed.

Lemma xIncludedEmptySetIsEmpty: forall x : Ensemble nat, Included nat x (Empty_set nat) -> x = Empty_set nat.
Proof.
intros x H0.
apply Extensionality_Ensembles.
unfold Same_set.
split.
assumption.
intuition.
Qed.

Theorem connectionR : forall c c' : Ensemble nat, forall a a' : Ensemble EO, alphaR c a -> gammaR a' c' -> Included EO a a' <-> Included nat c c'.
Proof.
intros c c' a a' Halpha Hgamma.
split.
induction Halpha; induction Hgamma; (try intuition).

unfold EvenSet in H1.
unfold OddSet in H1.
unfold Included in H1.
specialize H1 with even.
assert (In EO (Singleton EO even) even).
cbv.
apply In_singleton.
intuition.
inversion H3.

unfold EvenSet in H1.
unfold Included in H1.
specialize H1 with even.
assert (In EO (Singleton EO even) even).
apply In_singleton.
intuition.
inversion H3.

unfold Included.
intros x0 H2.
apply Full_intro.

unfold Included in H1.
specialize H1 with odd.
unfold OddSet in H1.
unfold EvenSet in H1.
assert (In EO (Singleton EO odd) odd).
apply In_singleton.
intuition.
inversion H3.

unfold Included in H1.
specialize H1 with odd.
unfold OddSet in H1.
assert (In EO (Singleton EO odd) odd).
apply In_singleton.
intuition.
inversion H3.

unfold Included.
intros x0 H2.
apply Full_intro.

unfold Included in H2.
specialize H2 with odd.
assert (In EO (Full_set EO) odd).
apply Full_intro.
intuition.
unfold EvenSet in H4.
inversion H4.

unfold Included in H2.
specialize H2 with even.
assert (In EO (Full_set EO) even).
apply Full_intro.
intuition.
unfold OddSet in H4.
inversion H4.

unfold Included in H2.
specialize H2 with even.
assert (In EO (Full_set EO) even).
apply Full_intro.
intuition.
inversion H4.

unfold Included.
intros x0 H3.
apply Full_intro.

induction Hgamma; induction Halpha; (try intuition).

assert (x=Empty_set nat).
apply xIncludedOddnessEvennessIsEmpty.
assumption.
assumption.
contradiction.

assert (x=Empty_set nat).
apply xIncludedOddnessEvennessIsEmpty.
assumption.
assumption.
contradiction.

assert (x=Empty_set nat).
apply xIncludedEmptySetIsEmpty.
assumption.
contradiction.

assert (x=Empty_set nat).
apply xIncludedEmptySetIsEmpty.
assumption.
contradiction.

assert (x=Empty_set nat).
apply xIncludedEmptySetIsEmpty.
assumption.
contradiction.

unfold Included.
intros x0 H2.
apply Full_intro.

unfold Included.
intros x0 H2.
apply Full_intro.
Qed.










