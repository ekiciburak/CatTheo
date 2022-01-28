From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple Monad.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import JMeq.
Set Universe Polymorphism.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.
Arguments Compose_Functors {_} {_} {_} _ _.
Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.
Arguments Compose_NaturalTransformations {_ _ _ _ _ } _ _.
Arguments Compose_NaturalTransformations_H {_ _ _ _ _ } _ _.

(* Definition Presheaf (C: Category) := Functor C TypeCat.

Definition PresheafCat (C: Category): Category.
Proof. unshelve econstructor.
       - exact (Presheaf C).
       - intros F G.
         exact {eta: NaturalTransformation F G | 
                forall X Y (f: @arrow C Y X), fmap G f o trans eta X = trans eta Y o fmap F f}.
       - simpl. intros F.
         exists (IdNt _ _ F).
         intros X Y f.
         simpl.
         apply functional_extensionality.
         intro Z.
         rewrite !preserve_id.
         simpl.
         reflexivity.
       - simpl. intros F G H (eta, Heta) (mu, Hmu).
         unfold Presheaf in *.
         exists (@Compose_NaturalTransformations C TypeCat H G F eta mu).
         intros X Y f.
         apply functional_extensionality.
         intros Z.
         simpl.
         specialize (Heta X Y f).
         specialize (Hmu X Y f).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl Heta) as Heta';
         cbv beta in Heta'.
         rewrite <- Heta'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl Hmu) as Hmu';
         cbv beta in Hmu'.
         rewrite <- Hmu'.
         reflexivity.
       - repeat intro. now subst.
       - simpl. intros F G H I (eta, Heta) (mu, Hmu) (theta, Htheta).
         simpl.
(*          Search exist. *)
         apply subset_eq_compat.
         rewrite Compose_NaturalTransformations_Assoc.
         reflexivity.
       - simpl. intros F G (eta, Heta).
         apply subset_eq_compat.
         apply Nt_split.
         simpl.
         extensionality x.
         extensionality y.
         rewrite preserve_id.
         simpl.
         reflexivity.
       - intros F G (eta, Heta).
         apply subset_eq_compat.
         apply Nt_split.
         simpl.
         extensionality x.
         extensionality y.
         rewrite preserve_id.
         simpl.
         reflexivity.
Defined.
 *)

Definition Presheaf (C: Category) := Functor (DualCategory C) TypeCat.

Definition PresheafCat (C : Category) := FunctorCategory (DualCategory C) TypeCat.

(* Definition PresheafCat (C: Category): Category.
Proof. unshelve econstructor.
       - exact (Presheaf C).
       - intros F G.
         exact {eta: NaturalTransformation G F | 
                forall Y X (f: @arrow C X Y), fmap F f o trans eta X = trans eta Y o fmap G f}.
       - simpl. intros F.
         exists (IdNt _ _ F).
         intros Y X f.
         simpl.
         apply functional_extensionality.
         intro Z.
         specialize (@preserve_id (DualCategory C) TypeCat F); intro H.
         rewrite !H. simpl.
         reflexivity.
       - simpl. intros F G H (eta, Heta) (mu, Hmu).
         exists (@Compose_NaturalTransformations (DualCategory C) TypeCat F G H mu eta).
         intros X Y f.
         apply functional_extensionality.
         intros Z.
         simpl.
         specialize (Hmu X Y f).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl Hmu) as Hmu';
         cbv beta in Hmu'.
         rewrite <- Hmu'.
         specialize (Heta X Y f).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl Heta) as Heta';
         cbv beta in Heta'.
         rewrite <- Heta'.
         reflexivity.
       - repeat intro. now subst.
       - simpl. intros F G H I (eta, Heta) (mu, Hmu) (theta, Htheta).
         simpl.
(*          Search exist. *)
         apply subset_eq_compat.
         rewrite Compose_NaturalTransformations_Assoc.
         reflexivity.
       - simpl. intros F G (eta, Heta).
         apply subset_eq_compat.
         apply Nt_split.
         simpl.
         extensionality x.
         extensionality y.
         specialize (@preserve_id (DualCategory C) TypeCat G); intro H.
         rewrite H. simpl.
         reflexivity.
       - intros F G (eta, Heta).
         apply subset_eq_compat.
         apply Nt_split.
         simpl.
         extensionality x.
         extensionality y.
         specialize (@preserve_id (DualCategory C) TypeCat F); intro H.
         rewrite H.
         simpl.
         reflexivity.
Defined. *)

