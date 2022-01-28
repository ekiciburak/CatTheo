From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor NaturalTransformation Adjunction.
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

Class PKT (C: Category) (hp: hasProducts C): Type :=
{
  ktobj : @obj C -> @obj C;
  ktmap : forall X: @obj C, arrow (ktobj X) X;
  ktstar: forall {X Y Z: @obj C} (f: arrow (ktobj Z) (@pobj C hp X Y)), arrow (ktobj Z) (@pobj C hp X (ktobj Y));
  ktob1 : forall {X X' Y Z: @obj C} (f: arrow X' X) (g: arrow (ktobj Z) (@pobj C hp X' Y)),
          (ktstar (g o (fprod f (identity Y)))) = (ktstar g) o (fprod f (identity (ktobj Y)));
  ktob2 : forall {X Y Z: @obj C} (f: arrow (ktobj Z) (@pobj C hp X Y)),
          ktstar f o (fprod (identity X) (ktmap Y)) = f;
  ktob3 : forall {X Y Z W: @obj C} (f: arrow (ktobj Z) (@pobj C hp X Y)) (g: arrow (ktobj W) (@pobj C hp X Z)),
          ktstar (ktstar g o (@prod_f C X (ktobj Z) (@pobj C hp X (ktobj Z)) (@hasp C hp X (ktobj Z)) (pobj X Y)
                                      (@pi1 C X Y (@pobj C hp X Y) (@hasp C hp X Y)) 
                                      f)) = 
          ktstar g o (@prod_f C X (ktobj Z) (@pobj C hp X (ktobj Z)) (@hasp C hp X (ktobj Z)) (pobj X (ktobj Y))
                              (@pi1 C X (ktobj Y) (@pobj C hp X (ktobj Y)) (@hasp C hp X (ktobj Y)))
                              (ktstar f))
}.

Definition fobjFs (s a : Set) := s -> (a * s).

Definition fmapFs (s A B: Set) (f: A -> B) (x : fobjFs s A) :=
  fun st =>
    match x st with
      | (a, st') => (f a, st')
    end.

Definition Fs: forall (s: @obj TypeCat), Functor TypeCat TypeCat.
Proof. intro s.
       unshelve econstructor.
       - intros a. exact (fobjFs s a).
       - intros a b f. exact (fmapFs s a b f).
       - repeat intro. now subst.
       - intros. cbn in *.
         extensionality X. compute.
         extensionality st. now destruct X.
       - intros. cbn in *.
         extensionality X. compute.
         extensionality st. now destruct X.
Defined.

Definition State (S: Set): PKT SetCat hasProductsSetCat.
Proof. specialize (hasProductsSetCat); intro hp.
       unshelve econstructor.
       - intro X.
         exact (S -> (X * S)).
       - simpl.
         intros X x s.
         exact (x, s).
       - simpl. intros X Y Z f (x, t) s.
         destruct (t s) as (y, s').
         exact (f (x, y) s').
       - simpl. intros X X' Y Z f g.
         apply functional_extensionality.
         intros (x, h).
         unfold fprod.
         simpl.
         reflexivity.
       - simpl. intros X Y Z f.
         apply functional_extensionality.
         intros (x, y).
         reflexivity.
       - simpl. intros X Y Z W f g.
         apply functional_extensionality.
         intros (x, h).
         simpl.
         apply functional_extensionality.
         intro s.
         destruct (h s) as (y, s').
         reflexivity.
Defined.


Definition Error: PKT SetCat hasProductsSetCat.
Proof. specialize (hasProductsSetCat); intro hp.
       unshelve econstructor.
       - intro X.
         exact (X + Datatypes.unit)%type.
       - simpl.
         intros X x.
         left. exact x.
       - simpl. intros X Y Z f (x, g).
         destruct g as [y | tt].
         + exact (f (x, y)).
         + right. exact tt.
       - simpl. intros X X' Y Z f g.
         apply functional_extensionality.
         intros (x, h).
         destruct h as [y | tt].
         + unfold fprod. 
           simpl.
           reflexivity.
         + reflexivity.
       - simpl. intros X Y Z f.
         apply functional_extensionality.
         intros (x, g).
         reflexivity.
       - simpl. intros X Y Z W f g.
         apply functional_extensionality.
         intros (x, h).
         destruct h as [y | tt].
         + reflexivity.
         + reflexivity.
Defined.

Definition Continuation (R: Set): PKT SetCat hasProductsSetCat.
Proof. specialize (hasProductsSetCat); intro hp.
       unshelve econstructor.
       - intro X.
         exact ((X -> R) -> R).
       - simpl.
         intros X x f.
         exact (f x).
       - simpl. intros X Y Z f (x, r) g.
         apply r.
         intro y.
         exact (f (x, y) g).
       - simpl.
         intros X X' Y Z f g.
         apply functional_extensionality.
         intros (x, h).
         unfold fprod.
         simpl.
         reflexivity.
       - simpl. intros X Y Z f.
         apply functional_extensionality.
         intros (x, g).
         reflexivity.
       - simpl. intros X Y Z W f g.
         apply functional_extensionality.
         intros (x, h).
         reflexivity.
Defined.



