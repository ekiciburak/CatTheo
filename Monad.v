From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple.
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

Arguments unit {_ _ _ _} _.
Arguments counit {_ _ _ _} _.

Class Monad (C: Category) (T: Functor C C): Type :=
  mk_Monad
  {
    eta : NaturalTransformation IdFunctor T;
    mu  : NaturalTransformation (Compose_Functors T T) T;
    comm_diagram1   : forall (a: @obj C), 
                        (trans mu a) o (fmap T (trans mu a)) = 
                        (trans mu a) o (trans mu (fobj T a));
    comm_diagram2   : forall (a: @obj C), 
                        (trans mu a) o (fmap T (trans eta a)) = 
                        (trans mu a) o (trans eta (fobj T a));
    comm_diagram2_b1: forall (a: @obj C), 
                        (trans mu a) o (fmap T (trans eta a)) = 
                        (identity (fobj T a));
    comm_diagram2_b2: forall (a: @obj C), (trans mu a) o (trans eta (fobj T a)) =
                        (identity (fobj T a))
  }.

  (** comonads *)
Class coMonad (C: Category) 
              (D: Functor C C): Type :=
  mk_coMonad
  {
    eps    : NaturalTransformation D IdFunctor;
    delta  : NaturalTransformation D (Compose_Functors D D);
    ccomm_diagram1   : forall (a: @obj C),
                       (fmap D (trans delta a)) o (trans delta a) = 
                       (trans delta (fobj D a)) o (trans delta a);
    ccomm_diagram2   : forall (a: @obj C),
                       (fmap D (trans eps a)) o (trans delta a) =
                       (trans eps (fobj D a)) o (trans delta a);
    ccomm_diagram2_b1: forall (a: @obj C),
                       (trans eps (fobj D a)) o (trans delta a) =
                       (identity (fobj D a));
    ccomm_diagram2_b2: forall (a: @obj C),
                       (fmap D (trans eps a)) o (trans delta a) =
                       (identity (fobj D a))
  }.

Theorem rcancel:  forall {C: Category} {a b c: @obj C}
                         (f g: arrow c b) (h: arrow b a), 
                          f = g -> f o h = g o h.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem lcancel:  forall {C: Category} {a b c: @obj C}
                         (f g: arrow b a) (h: arrow c b), 
                         f = g -> h o f  = h o g.
Proof. intros. rewrite H. reflexivity. Qed.

(** every adjunction gives raise to a monad *)
Theorem adj_mon: ∏ {C1 C2: Category}(F: Functor C1 C2) (G: Functor C2 C1),
                 Adjunction F G -> Monad C1 (Compose_Functors F G).
Proof. intros C1 C2 F G A.
       unshelve econstructor.
       - exact (unit A).
       - unshelve econstructor.
         + intro X. exact (fmap G (trans (counit A) (fobj F X))).
         + intros X Y f. cbn.
           rewrite <- !preserve_comp.
           specialize (@comm_diag _ _ _ _ (counit A) _ _ (fmap F f)); intro H.
           cbn in *.  unfold id in *. now rewrite H.
       - intros X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@comm_diag _ _ _ _ (counit A) _ _ (trans (counit A) (fobj F X))); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A X); intro H1.
         specialize (@ob2 _ _ _ _ A (fobj F X)); intro H2.
         cbn in *.  unfold id in *. 
         now rewrite H2, H1, preserve_id.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A X); intro H1.
         cbn in *.  unfold id in *.
         now rewrite H1, preserve_id.
       - intro X. cbn in *.
         specialize (@ob2 _ _ _ _ A (fobj F X)); intro H2.
         cbn in *.  unfold id in *.
         now rewrite H2.
Defined.
Check adj_mon.

(** every adjunction gives raise to a monad *)
Theorem homadj_mon: ∏ {C1 C2: Category}(F: Functor C1 C2) (G: Functor C2 C1),
                      HomAdjunction F G -> Monad C1 (Compose_Functors F G).
Proof. intros C1 C2 F G A.
       apply HomAdj_eq in A.
       unshelve econstructor.
       - exact (unit A).
       - unshelve econstructor.
         + intro X. exact (fmap G (trans (counit A) (fobj F X))).
         + intros X Y f. cbn.
           rewrite <- !preserve_comp.
           specialize (@comm_diag _ _ _ _ (counit A) _ _ (fmap F f)); intro H.
           cbn in *.  unfold id in *. now rewrite H.
       - intros X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@comm_diag _ _ _ _ (counit A) _ _ (trans (counit A) (fobj F X))); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A X); intro H1.
         specialize (@ob2 _ _ _ _ A (fobj F X)); intro H2.
         cbn in *.  unfold id in *. 
         now rewrite H2, H1, preserve_id.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A X); intro H1.
         cbn in *.  unfold id in *.
         now rewrite H1, preserve_id.
       - intro X. cbn in *.
         specialize (@ob2 _ _ _ _ A (fobj F X)); intro H2.
         cbn in *.  unfold id in *.
         now rewrite H2.
Defined.
Check homadj_mon.


(** every adjunction gives raise to a comonad *)
Theorem adj_comon: ∏ {C1 C2: Category}(F: @Functor C1 C2)(G: @Functor C2 C1),
                 Adjunction F G -> coMonad C2 (Compose_Functors G F).
Proof. intros C1 C2 F G A. 
       unshelve econstructor.
       - exact (counit A).
       - unshelve econstructor.
         + intro X. exact (fmap F (trans (unit A) (fobj G X))).
         + intros X Y f. cbn.
           rewrite <- !preserve_comp.
           specialize (@comm_diag _ _ _ _ (unit A) _ _ (fmap G f)); intro H.
           cbn in *.  unfold id in *. now rewrite H.
       - intros X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@comm_diag _ _ _ _ (unit A) _ _ (trans (unit A) (fobj G X))); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob1 _ _ _ _ A (fobj G X)); intro H1.
         specialize (@ob2 _ _ _ _ A X); intro H2.
         cbn in *.  unfold id in *. 
         now rewrite H2, H1, preserve_id.
       - intro X. cbn in *.
         specialize (@ob1 _ _ _ _ A (fobj G X)); intro H1.
         cbn in *.  unfold id in *.
         now rewrite H1.
       - intro X. cbn in *.
         rewrite <- !preserve_comp.
         specialize (@ob2 _ _ _ _ A X); intro H2.
         cbn in *.  unfold id in *.
         now rewrite H2, preserve_id.
Defined.
Check adj_comon.

Fixpoint flatten {A: Type} (l: list (list A)): list A :=
  match l with
   | nil       => nil
   | cons x xs => x ++ flatten xs
  end.

Lemma listMonad: let T := (Compose_Functors FreeMonoidFunctor Forgetful1) in Monad SetCat T.
Proof. intros T.
       unfold T in *.
       unshelve econstructor.
       - unshelve econstructor.
         + simpl.
           intros A a.
           exact (Initial.eta a).
         + simpl.
           intros a b f.
           unfold Initial.eta.
           reflexivity.
       - unshelve econstructor.
         + simpl. 
           intros A l.
           exact (flatten l).
         + simpl. intros a b f.
           extensionality l.
           induction l; intros.
           ++ simpl. reflexivity.
           ++ simpl in *. rewrite <- IHl.
              rewrite List.map_app.
              reflexivity.
       - simpl. intros A.
         extensionality l.
         induction l; intros.
         + simpl. reflexivity.
         + simpl. rewrite IHl.
           induction a; intros.
           ++ simpl. reflexivity.
           ++ simpl. rewrite List.app_assoc_reverse, IHa. reflexivity.
       - simpl. intros A.
         extensionality l.
         induction l; intros.
         + simpl. reflexivity.
         + simpl. rewrite IHl. reflexivity.
       - simpl. intros A.
         extensionality l.
         unfold Initial.eta.
         induction l; intros.
         + simpl. reflexivity.
         + simpl. rewrite IHl. reflexivity.
       - simpl. intros A.
         extensionality l.
         unfold Initial.eta.
         induction l; intros.
         + simpl. reflexivity.
         + simpl. rewrite IHl. reflexivity.
Defined.

(** the Kleisli category of a monad *)
Definition Kleisli_Category 
            (C: Category) 
            (T: Functor C C)
            (M: Monad C T) : (Category).
Proof. 
       unshelve econstructor.
       - exact (@obj C).
       - intros a b. exact (@arrow C (fobj T a) b).
       - intros.
       
       destruct M as (eta, mu, ob1, ob2, ob3, ob4).
       destruct eta as (teta, cdeta).
       destruct mu as (tmu, cdmu). simpl in *.
        exact (teta a).
       - intros a b c g f. simpl in *.
       destruct M as (eta, mu, ob1, ob2, ob3, ob4).
       destruct eta as (teta, cdeta).
       destruct mu as (tmu, cdmu). simpl in *.
         exact ((tmu c) o (fmap T g) o f).
       - repeat intro. now subst.
       -
       destruct M as (eta, mu, ob1, ob2, ob3, ob4).
       destruct eta as (teta, cdeta).
       destruct mu as (tmu, cdmu). simpl in *.
        intros. simpl in *. destruct T. simpl in *.
         unfold IdFunctor, id in *. simpl in *.
         rewrite preserve_comp.
         rewrite assoc. rewrite preserve_comp. 
         rewrite assoc. do 2 rewrite assoc. 
         rewrite (ob1 d).
         specialize(@cdeta c (fobj d) h).
         apply rcancel. apply rcancel.
         rewrite <- assoc. rewrite <- assoc.
         rewrite cdmu.
         reflexivity.
       -
       destruct M as (eta, mu, ob1, ob2, ob3, ob4).
       destruct eta as (teta, cdeta).
       destruct mu as (tmu, cdmu). simpl in *.
        intros. unfold id in *. simpl in *. unfold id in *.
         rewrite ob3.
         now rewrite identity_f.
       -
       destruct M as (eta, mu, ob1, ob2, ob3, ob4).
       destruct eta as (teta, cdeta).
       destruct mu as (tmu, cdmu). simpl in *.
        intros. unfold id in *. simpl in *. unfold id in *.
         specialize (cdmu a (fobj T b) f).
         rewrite <- assoc.
         rewrite cdeta. rewrite assoc.
         now rewrite ob4, identity_f.
Defined.

(** left adjoint functor that acts as F_T *)
Definition FTK {C  : Category}
              (T  : Functor C C)
              (M  : Monad C T)
              (KC := Kleisli_Category C T M): Functor C KC.
Proof. unshelve econstructor.
       - exact id.
       - destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
         intros a b f. exact (teta b o f).
       - repeat intro. subst. easy.
       - destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
         intros. simpl in *. rewrite f_identity. easy.
       - destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
         intros. simpl in *. 
         rewrite !preserve_comp.
         do 3 rewrite assoc.
         rewrite cc3.
         rewrite identity_f.
         now rewrite cd1.
Defined.

(** right adjoint functor that acts as G_T *)
Definition GTK  {C  : Category}
               (T  : Functor C C)
               (M  : Monad C T)
               (KC := Kleisli_Category C T M): Functor KC C.
Proof. unshelve econstructor.
       - exact (fobj T).
       - destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
         intros a b f. exact (tmu b o fmap T f).
       - repeat intro. subst. easy.
       - destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
         intros. simpl in *. clear KC.
         specialize (cc3 a). easy.
       - destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
         intros. unfold id in *.
         simpl in *.
         rewrite !preserve_comp.
         repeat rewrite assoc.
         apply rcancel.
         repeat rewrite assoc.
         simpl in *.
         rewrite !cc1.
         repeat rewrite <- assoc.
         now rewrite cd2.
Defined.


(** every monad gives raise to a Kleisli adjunction *)
Theorem mon_kladj: forall
                   {C D: Category}
                   (F  : Functor C D)
                   (G  : Functor D C)
                   (T  := Compose_Functors F G)
                   (M  : Monad C T)
                   (FT := FTK T M)
                   (GT := GTK T M), Adjunction FT GT.
Proof. intros C D F G T M FT GT.
       destruct M as ((teta, cd1), (tmu, cd2), cc1, cc2, cc3, cc4).
       unshelve econstructor.
       - unshelve econstructor.
         + intro a.
           exact (teta a).
         + intros. simpl in *.
           destruct FT, GT.
           unfold id in *.
           rewrite <- assoc.
           rewrite cd1.
           rewrite assoc.
           simpl in *.
           rewrite cc4.
           now rewrite identity_f.
       - unshelve econstructor.
         + intro a. exact (identity (fobj G (fobj F a))).
         + intros. simpl.
           destruct FT, GT.
           simpl in *. unfold id in *.
           rewrite f_identity.
           repeat rewrite assoc.
           symmetry.
           assert (tmu b o Functor.fmap G 
           (Functor.fmap F f) =
           (@identity C (Functor.fobj G (Functor.fobj F b))) o tmu b o 
           Functor.fmap G (Functor.fmap F f) ).
           {
              now rewrite identity_f.
           }
           rewrite H. apply rcancel. apply rcancel.
           rewrite <- assoc.
           rewrite cd1, f_identity.
           now rewrite cc4.
       - intros. simpl in *.
         destruct FT, GT. simpl in *.
         unfold id in *.
         rewrite assoc.
         assert (teta a = (@identity C (Functor.fobj G (Functor.fobj F a))) o  teta a).
         {
            now rewrite identity_f.
         }
         rewrite H.
         rewrite assoc.
         apply rcancel.
         rewrite f_identity.
         rewrite <- assoc.
         rewrite cd1, f_identity.
         now rewrite cc4.
       - intros. simpl in *.
         destruct FT, GT. simpl in *.
         unfold id in *.
         rewrite <- assoc.
         rewrite cd1, f_identity.
         now rewrite cc4.
Defined.

