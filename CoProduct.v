From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual Initial Product.
Require Import FunctionalExtensionality.

Set Universe Polymorphism.

(** Binary CoProducts *)

Class CoProduct (C: Category) (A B sum: @obj C): Type :=
{
  inl      : @arrow C sum A;
  inr      : @arrow C sum B;  
  sum_f    : forall (Z: @obj C) (f: @arrow C Z A) (g: @arrow C Z B), @arrow C Z sum;
  sum_f_c1 : forall (Z: @obj C) (f: @arrow C Z A) (g: @arrow C Z B), f = sum_f Z f g o inl;
  sum_f_c2 : forall (Z: @obj C) (f: @arrow C Z A) (g: @arrow C Z B), g = sum_f Z f g o inr;
  sum_f_uni: forall (Z: @obj C) (f: @arrow C Z A) (g: @arrow C Z B) (s1 s2: @arrow C Z sum),
              f = s1 o inl -> f = s2 o inl -> g = s1 o inr -> g = s2 o inr -> s1 = s2
}.

Class hasCoProducts (C: Category): Type :=
{
  cpobj: forall (A B: @obj C), @obj C;
  hascp: forall (A B: @obj C), CoProduct C A B (cpobj A B) 
}.

Lemma prod_coprod: forall (C: Category) (A B AxB: @obj C) (p: Product C A B AxB), CoProduct (DualCategory C) A B AxB.
Proof. intros C A B AxB (pi1, pi2, h, hax1, hax2, huniq).
       unshelve econstructor.
       - simpl. exact pi1.
       - simpl. exact pi2.
       - simpl. intros Z f g. exact (h Z f g).
       - simpl. intros Z f g. apply (hax1 Z f g).
       - simpl. intros Z f g. apply (hax2 Z f g).
       - simpl. intros Z f g s1 s2 Ha Hb Hc Hd.
         pose proof huniq as hhuniq. 
         rewrite <- (huniq Z f g s1).
         rewrite <- (hhuniq Z f g s2); easy.
         easy.
         easy.

Qed.

Lemma coprod_prod: forall (C: Category) (A B s: @obj C) (p: CoProduct C A B s), Product (DualCategory C) A B s.
Proof. intros C A B s (inl, inr, h, hax1, hax2, huniq).
       unshelve econstructor.
       - simpl. exact inl.
       - simpl. exact inr.
       - simpl. intros Z f g. exact (h Z f g).
       - simpl. intros Z f g. apply (hax1 Z f g).
       - simpl. intros Z f g. apply (hax2 Z f g).
       - simpl. intros Z f g s1 s2 Ha. 
         rewrite (huniq Z f g (h Z f g) s1); easy.
Qed.

(** TODO: Coproducts are unique up to (unique) isomorphism *)

Lemma setCoProd: forall A B: @obj SetCat, CoProduct SetCat A B (sum A B).
Proof. intros.
       unshelve econstructor.
       - simpl. intros a. exact (@Datatypes.inl A B a).
       - simpl. intros b. exact (@Datatypes.inr A B b).
       - simpl. intros Z f g z.
         destruct z as [a | b].
         + exact (f a).
         + exact (g b).
       - simpl. intros Z f g. easy.
       - simpl. intros Z f g. easy.
       - simpl. intros Z f g s1 s2 H1 H2 H3 H4.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H1) as Hax1';
         cbv beta in Hax1'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H2) as Hax2';
         cbv beta in Hax2'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H3) as Hax3';
         cbv beta in Hax3'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H4) as Hax4';
         cbv beta in Hax4'.
         apply functional_extensionality.
         intros [a | b].
         + specialize (Hax1' a).
           specialize (Hax2' a).
           rewrite <- Hax1', <- Hax2'. reflexivity.
         + specialize (Hax3' b).
           specialize (Hax4' b).
           rewrite <- Hax3', <- Hax4'.
           reflexivity.
Defined.
















