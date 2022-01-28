From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal.

(** Dual of a category *)

(* Definition Dual_Category (C: Category) : Category.
Proof. 
  refine (@mk_Category 
           (@obj C)%type
           (fun a b => (@arrow C b a %type))
           (fun a => (@identity C a))
           (fun a b c f1 f2 => f2 o f1)
           _ _ _ _ 
         ).
 - intros. now rewrite <- assoc.
 - intros. now rewrite f_identity.
 - intros. now rewrite identity_f.
Defined. *)

Definition DualCategory (C: Category) : Category.
Proof. unshelve econstructor.
       - exact (@obj C).
       - intros A B. exact (@arrow C B A).
       - simpl. intro a. exact (@identity C a).
       - simpl. intros a b c f g. exact (g o f).
       - simpl. repeat intro. now subst.
       - simpl. intros a b c d f g h. rewrite assoc. reflexivity.
       - simpl. intros a b f. rewrite f_identity. reflexivity.
       - simpl. intros a b f. rewrite identity_f. reflexivity.
Defined.
