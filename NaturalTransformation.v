From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import JMeq.
Set Universe Polymorphism.

(* Arguments Compose_Functors {_} {_} {_} _ _. *)
Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.

Check fobj.
Class NaturalTransformation (C D: Category) 
                            (F  : Functor C D)
                            (G  : Functor C D): Type :=
  mk_nt
  {
    trans    : forall (a: @obj C), (@arrow D (fobj G a) (fobj F a));
    comm_diag: forall {a b: @obj C} (f: arrow  b a), fmap G f o trans a  = trans b o fmap F f;
  }.
Check NaturalTransformation.

Arguments NaturalTransformation {_} {_} _ _.
Arguments trans {_} {_} {_} {_} _ _.

Example NT1: NaturalTransformation (@IdFunctor SetCat) (Compose_Functors FreeMonoidFunctor Forgetful1).
Proof. unshelve econstructor.
       - simpl. unfold id. intros X x.
         exact (eta x).
       - simpl. intros X Y f.
         unfold eta. reflexivity.
Defined.

(** sameness of natural transformations *)
Lemma Nt_split: forall (C D: Category)
                       (F  : @Functor C D) 
                       (G  : @Functor C D)
                       (nt1: NaturalTransformation F G)
                       (nt2: NaturalTransformation F G), trans nt1 = trans nt2 <-> nt1 = nt2.
Proof. intros. split. intros. destruct nt1, nt2, F, G.
       simpl in *. revert comm_diag0. rewrite H. intros.
       specialize (proof_irrelevance (forall (a b : @obj C) (f : arrow b a),
             fmap0 a b f o trans1 a = trans1 b o fmap a b f) comm_diag0 comm_diag1).
       now destruct (proof_irrelevance _ comm_diag0 comm_diag1).
       intros. rewrite H. easy.
Qed.

Program Definition Compose_NaturalTransformations 
                      (C D: Category)
                      (F  : @Functor C D)
                      (G  : @Functor C D)
                      (H  : @Functor C D)
                      (nt1: NaturalTransformation F G)
                      (nt2: NaturalTransformation G H): `(NaturalTransformation F H) :=
{|
    trans := fun a: @obj C =>  trans nt2 a o trans nt1 a;
|}.
Next Obligation.
      rewrite assoc.
      rewrite (@comm_diag C D G H nt2 a).
      do 2 rewrite <- assoc.
      rewrite (@comm_diag C D F G nt1 a).
      reflexivity.
Defined.

(** composing natural transformations *)
Program Definition Compose_NaturalTransformations_H 
                          (C D E: Category)
                          (F    : Functor C D)
                          (G    : Functor C D)
                          (H    : Functor D E)
                          (I    : Functor D E)
                          (nt1  : NaturalTransformation F G)
                          (nt2  : NaturalTransformation H I):
                                `(NaturalTransformation (Compose_Functors F H) 
                                                        (Compose_Functors G I)).
Proof. unshelve econstructor.
       - destruct F, G, H, I, nt1, nt2. simpl in *.
         intros. exact (((fmap2 _ _ (trans0 a)) o trans1 (fobj  a))).
       - destruct F, G, H, I, nt1, nt2. simpl in *.
         intros. rewrite !comm_diag1. rewrite assoc.
         rewrite comm_diag1. rewrite <- assoc.
         rewrite <- !preserve_comp1.
         rewrite <- assoc.
         rewrite <- !preserve_comp1. now rewrite comm_diag0.
Defined.

(** the identity natural transformation *)
Definition IdNt (C D: Category) 
                (F  : Functor C D): NaturalTransformation F F.
Proof. unshelve econstructor.
       - intros. exact (fmap _(@identity C a)).
       - intros. destruct F. simpl. rewrite !preserve_id.
         now rewrite identity_f, f_identity.
Defined.

Arguments Compose_NaturalTransformations {_} {_} {_} {_} {_} _ _.

Lemma Compose_NaturalTransformations_Assoc: forall (C D: Category) (F G H I: Functor C D)
  (nt1: NaturalTransformation F G) (nt2: NaturalTransformation G H) (nt3: NaturalTransformation H I),
  @Compose_NaturalTransformations _ _ _ _ _ (@Compose_NaturalTransformations C D F G H nt1 nt2) nt3 =
  @Compose_NaturalTransformations _ _ _ _ _ nt1 (@Compose_NaturalTransformations C D G H I nt2 nt3).
Proof. intros.
       apply Nt_split.
       simpl.
       extensionality x.
       rewrite assoc.
       reflexivity.
Qed.

(** the category of all functors defined from the same source to 
the same target category *)
Definition FunctorCategory (C D: Category): Category.
Proof.
       unshelve econstructor.
       - exact (Functor C D).
       - intros F G. exact (NaturalTransformation G F).
       - intros. exact (@IdNt C D a).
       - intros F G H nt1 nt2.
         exact (Compose_NaturalTransformations nt2 nt1).
       - repeat intro. now rewrite H, H0.
       - intros. apply Nt_split. simpl.
         destruct f, g, h. simpl.
         extensionality a0. now rewrite assoc.
       - intros. apply Nt_split. simpl.
         destruct f, a, b. simpl.
         extensionality a0.
         now rewrite preserve_id0, identity_f.
       - intros. apply Nt_split. simpl.
         destruct f, a, b. simpl.
         extensionality a0.
         now rewrite preserve_id, f_identity.
Defined.

Class CatEquivalence (C D: Category): Type :=
{
   lfunctor: Functor C D;
   rfunctor: Functor D C;
   eq_obl  : @Isomorphic (FunctorCategory C C) (Compose_Functors lfunctor rfunctor) (@IdFunctor C);
   eq_obr  : @Isomorphic (FunctorCategory D D) (Compose_Functors rfunctor lfunctor) (@IdFunctor D)
}.

Definition appFunctor (C D: Category): Functor ((ProductCategory (FunctorCategory C D) C)) D.
Proof. unshelve econstructor.
       - intros (F, X).
         exact (fobj F X).
       - intros (F, X) (G, Y) (nt, f).
         exact (trans nt Y o (fmap F f)).
       - repeat intro. now subst.
       - intros (F, X).
         unfold IdNt.
         simpl.
         rewrite preserve_id, f_identity.
         reflexivity.
       - intros (F, X) (G, Y) (H, Z) (nt1, f) (nt2, g).
         unfold Compose_NaturalTransformations.
         simpl.
         rewrite preserve_comp.
         rewrite assoc.
         setoid_rewrite <- assoc at 2.
         rewrite <- comm_diag.
         rewrite assoc.
         rewrite assoc.
         reflexivity.
Defined.

Definition curFunctor {C D E: Category} (F: Functor (ProductCategory E C) D): Functor E (FunctorCategory C D).
Proof. unshelve econstructor.
       - intro Z.
         unshelve econstructor.
         + intro X.
           exact (fobj F (Z, X)).
         + intros X X' f.
           exact (@fmap (ProductCategory E C) D F (Z, X) (Z, X') (identity Z, f)).
         + repeat intro. now subst.
         + intro X.
           simpl.
           rewrite (@preserve_id).
           reflexivity.
         + intros X Y T g f.
           simpl.
           rewrite <- (@preserve_comp).
           simpl. rewrite f_identity.
           reflexivity.
       - intros Z Z' g.
         unshelve econstructor.
         + intro X.
           exact (@fmap (ProductCategory E C) D F (Z, X) (Z', X) (g, identity X)).
         + intros X Y f.
           simpl.
           rewrite <- !(@preserve_comp).
           simpl.
           rewrite !f_identity, !identity_f.
           reflexivity. 
       - repeat intro. now subst.
       - intro X. unfold IdNt.
         apply Nt_split. reflexivity.
       - unfold Compose_NaturalTransformations.
         intros X Y Z g f.
         apply Nt_split.
         extensionality x.
         simpl.
         rewrite <- preserve_comp.
         simpl.
         rewrite f_identity.
         reflexivity.
Defined.

Lemma arrowRW: forall {C: Category} (X Y Z T: @obj C), 
  X = Z -> Y = T -> arrow Y X = arrow T Z.
Proof. intros. subst. easy. Qed.

Require Import Coq.Program.Equality.

Arguments fmap {_} {_} _ {_} {_} _.
Arguments fobj {_} {_} _ _.

Lemma fmapFcurF: forall (C D E: Category) 
                   (F: Functor (ProductCategory E C) D)
                   (a1 b1: @obj E) (a2 b2: @obj C) 
                   (f1: arrow b1 a1) (f2: arrow b2 a2),
  trans (fmap (curFunctor F) f1) b2 o fmap (fobj (curFunctor F) a1) f2 = 
  @fmap (ProductCategory E C) D F (a1, a2) (b1, b2) (f1, f2).
Proof. intros C D E a1 b1 a2 b2 f1 f2 F.
       simpl.
       rewrite <- preserve_comp.
       simpl.
       rewrite f_identity, identity_f.
       reflexivity.
Qed.

Lemma fmap_dist: forall {C D E: Category} {X Y: @obj C} {f: arrow Y X} (F: Functor C D) (G: Functor D E),
  fmap (Compose_Functors F G) f = fmap G (fmap F f).
Proof. simpl. easy. Defined.


Lemma commDiagExp: forall (C D E: Category) (F: Functor (ProductCategory E C) D),
  Compose_Functors (ProductFunctor (curFunctor F) (@IdFunctor C)) (appFunctor C D) = F.
Proof. intros.
       assert (fobj (Compose_Functors (ProductFunctor (curFunctor F) IdFunctor) (appFunctor C D)) = fobj F).
       {
         extensionality a.
         destruct a as (a, b).
         simpl. reflexivity.
       }
(*        simpl in H. *)
(*        pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H) as H';
       cbv beta in H'. *)
       eapply F_splitA with (ObjEq := H).
       extensionality a.
       extensionality b.
       extensionality f.
       destruct a as (a1, a2).
       destruct b as (b1, b2).
       destruct f as (f1, f2).
       specialize (fmapFcurF C D E F); intro HH.
       simpl in HH.
       destruct (curFunctor F) as (CF, CFM, cfn, cfpid, cfpcomp). 
       destruct F as (FO, FM, fn, fpid, fpcomp).
       simpl in *.
       subst.
       unfold id in *.
       subst.
       simpl.
       
       destruct (CFM a1 b1 f1).
       simpl in *.
       rewrite <- comm_diag0.
       simpl.
       cbn in CF.
Admitted.





















 


