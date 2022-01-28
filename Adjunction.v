From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor NaturalTransformation.
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


(* Notation CoqCat U :=
{|
  obj := U;
  arrow := (fun A B => B -> A);
  identity := (fun _ => id);
  comp :=   (fun A B C (g: B -> C) (f: A -> B) a => g (f a))
|}.

Program Definition CoqCatT: Category := CoqCat Type.
Program Definition CoqCatS: Category := CoqCat Set.
Program Definition CoqCatP: Category := CoqCat Prop. *)

(* Class NaturalIsomorphism {C D: Category} (F G: Functor C D) : Type := {
  ntiso: NaturalTransformation F G;
  obiso: @Isomorphism (FunctorCategory C D) F G ntiso
}. *)

Class IsomorphismA {C: Category} (x y : @obj C) : Type := 
{
  to   : arrow y x;
  from : arrow x y;

  iso_to_from : to o from = @identity C y;
  iso_from_to : from o to = @identity C x
}.

Arguments to {_ _ _} _. 
Arguments from {_ _ _} _.

Lemma IsoEql: forall {C: Category} (X Y: @obj C), @IsomorphismA C X Y -> @Isomorphic C X Y.
Proof. intros C X Y (t, f, ob1, ob2).
       unshelve econstructor.
       - exact t.
       - unshelve econstructor.
         + exact f.
         + rewrite ob1. reflexivity.
         + rewrite ob2. reflexivity.
Qed.

Lemma IsoEqr: forall {C: Category} (X Y: @obj C), @Isomorphic C X Y -> @IsomorphismA C X Y.
Proof. intros C X Y (t, (f, ob1, ob2)).
       unshelve econstructor.
       - exact t.
       - exact f.
       - rewrite ob1. reflexivity.
       - rewrite ob2. reflexivity.
Qed.

Lemma IsoEq: forall {C: Category} (X Y: @obj C), iffT (@IsomorphismA C X Y) (@Isomorphic C X Y).
Proof. intros. 
       split.
       - apply IsoEql.
       - apply IsoEqr.
Qed.

Fixpoint opL {A B: Type} (f: A -> B) (op: B -> B -> B) (l: list A) (e: B): B :=
  match l with
    | nil       => e
    | cons x xs => (op (f x) (opL f op xs e))
  end.

Lemma IsoFreeMonoid: forall (S: Set) (M: Monoid), 
  @IsomorphismA TypeCat (@arrow SetCat (fobj Forgetful1 M) S)
                        (@arrow Mon M (fobj FreeMonoidFunctor S)).
Proof. intros S (M, e, op, ob1, ob2, ob3).
       simpl.
       unshelve econstructor.
       - simpl. intro f.
         unshelve econstructor.
         + simpl. intro l. exact (@opL S M f op l e).
         + simpl. reflexivity.
         + simpl. intro l.
           induction l; intros.
           ++ simpl. rewrite ob2. reflexivity.
           ++ simpl. rewrite IHl. rewrite ob1. reflexivity.
       - simpl. intros (g, mm1, mm2) s.
         simpl in *.
         exact (g (eta s)).
       - apply functional_extensionality.
         intros (f, mm1, mm2).
         simpl in *.
         apply MonoidMapEq. simpl.
         extensionality l.
         induction l; intros.
         ++ simpl. rewrite mm1. reflexivity.
         ++ simpl in *. rewrite IHl.
            rewrite <- mm2.
            unfold eta. simpl.
            reflexivity.
       - simpl.
         apply functional_extensionality.
         intros g.
         apply functional_extensionality.
         intro s.
         rewrite ob3.
         reflexivity.
Qed.

Lemma IsoBinaryProduct: forall {C: Category} {hp: hasProducts C} (X Y Z: @obj C),
  @IsomorphismA TypeCat 
                (@arrow (ProductCategory C C) (X, Y) (Z, Z))
                (@arrow C (@pobj C hp X Y) Z).
Proof. intros C (hp, P) X Y Z.
       unshelve econstructor.
       - simpl. intros (f, g).
         exact (@prod_f C X Y (hp X Y) (P X Y) Z f g).
       - simpl. intro h.
         split.
         + exact ((@pi1 C X Y (hp X Y) (P X Y)) o h).
         + exact ((@pi2 C X Y (hp X Y) (P X Y)) o h).
       - simpl.
         apply functional_extensionality.
         intro f. 
         destruct (P X Y).
         simpl in *.
         apply prod_f_uni with (f := (pi1 o f)) (g := (pi2 o f)).
         + reflexivity.
         + reflexivity.
       - simpl.
         apply functional_extensionality.
         intros (f, g).
         destruct (P X Y).
         simpl in *.
         rewrite <- prod_f_c1.
         rewrite <- prod_f_c2. 
         reflexivity.
Qed.

Lemma IsoExponential: forall {C: Category} {hp: hasProducts C} {he: hasExponentials C hp} (X Y Z: @obj C),
  @IsomorphismA TypeCat 
                (@arrow C Y (@pobj C hp Z X))
                (@arrow C (@eobj C hp he X Y) Z).
Proof. intros C hp (he, E) X Y Z.
       unshelve econstructor.
       - simpl. intro f.
         exact (@cur C hp X Y (he X Y) (E X Y) Z f).
       - simpl. intro g.
         exact (@app C hp X Y (he X Y) (E X Y) o (fprod g (identity X))).
       - simpl.
         apply functional_extensionality.
         intro f.
         destruct (E X Y).
         simpl in *.
         apply curuni.
         reflexivity.
       - simpl.
         apply functional_extensionality.
         intro f.
         destruct (E X Y).
         simpl in *.
         rewrite curcomm.
         reflexivity.
Qed.

(** 
- proof obligations:
-- natural transformations to be introduced:
 eta_A: A   -> GFA
 eps_A: FGA -> A
-- diagrams to commute:
 1. eps_FA   o F(eta_A) = id_FA
 2. G(eps_A) o eta_GA   = id_GA
*)
Class Adjunction {C D: Category}
                 (F  : @Functor C D)
                 (G  : @Functor D C): Type :=
  mk_Adj
  {
      unit  : (NaturalTransformation (@IdFunctor C) (Compose_Functors F G));
      counit: (NaturalTransformation (Compose_Functors G F) (@IdFunctor D));

      ob1   : forall a, (trans counit (fobj F a)) o (fmap F (trans unit a)) 
                        = @identity D (fobj F a);
      ob2   : forall a, (fmap G (trans counit a)) o (trans unit (fobj G a)) 
                        = @identity C (fobj G a)
}.

Arguments Adjunction {_} {_} _ _.

Definition HomFunctor (C: Category): Functor (ProductCategory (DualCategory C) C) TypeCat.
Proof. unshelve econstructor.
       - intros (X, Y).
         exact (@arrow C Y X).
       - intros a b f.
         destruct a as (X, Y).
         destruct b as (X', Y').
         destruct f as (f, g).
         intro h.
         exact (g o h o f).
       - repeat intro. now subst.
       - simpl. intros (X, Y).
         apply functional_extensionality.
         intro f.
         rewrite f_identity, identity_f.
         reflexivity.
       - intros (X, Y) (Z, T) (U, W) (f, g) (h, i).
         simpl.
         apply functional_extensionality.
         intro j.
         rewrite !assoc.
         reflexivity.
Defined.

Class HomAdjunction {C D: Category} (F: Functor C D) (G: Functor D C): Type :=
  mk_Homadj
  {
     theta: @IsomorphismA (FunctorCategory (ProductCategory (DualCategory C) D) TypeCat)
                          (Compose_Functors (ProductFunctor (@Id (DualCategory C)) G) (HomFunctor C)) 
                          (Compose_Functors (ProductFunctor (DualFunctor F) (@Id D)) (HomFunctor D)) 
  }.
Check HomAdjunction.

Definition BiHomFunctorC {C D: Category} (F: Functor D C): Functor (ProductCategory (DualCategory C) D) TypeCat.
Proof. unshelve econstructor.
       - intros (X, Y) .
         exact (@arrow C (fobj F Y) X).
       - intros (a1, a2) (b1, b2) (f, g) h.
         exact ((fmap F g) o h o f).
       - repeat intro. now subst.
       - intros (a1, a2).
         simpl.
         extensionality f.
         now rewrite f_identity, preserve_id, identity_f.
       - intros (a1, a2) (b1, b2) (c1, c2) (f, g) (h, i).
         simpl.
         extensionality j.
         rewrite preserve_comp.
         now do 3 rewrite assoc.
Defined.

Definition BiHomFunctorD {C D: Category} (G: Functor C D): Functor (ProductCategory (DualCategory C) D) TypeCat.
Proof. unshelve econstructor.
       - intros (X, Y).
         exact (@arrow D Y (fobj G X)).
       - intros (a1, a2) (b1, b2) (f, g) h.
         exact (g o h o (fmap G f)).
       - repeat intro. now subst.
       - intros (a1, a2).
         simpl.
         extensionality f.
         now rewrite identity_f, preserve_id, f_identity.
       - intros (a1, a2) (b1, b2) (c1, c2) (f, g) (h, i).
         simpl.
         extensionality j.
         rewrite preserve_comp.
         now do 3 rewrite assoc.
Defined.

Class NatAdjunction {C D: Category} (F: Functor C D) (G: Functor D C): Type :=
  mk_Natadj
  {
     ob: @IsomorphismA (FunctorCategory (ProductCategory (DualCategory C) D) TypeCat) (BiHomFunctorC G) (BiHomFunctorD F)
  }.
Check NatAdjunction.

Lemma HomNat_eql: forall {C D: Category} (F: Functor C D) (G: Functor D C), NatAdjunction F G -> HomAdjunction F G.
Proof. intros C D F G (theta).
       destruct theta as (to, from, ob1, ob2).
       destruct to as (eta, obeta).
       destruct from as (eps, obeps).
       unshelve econstructor.
       - unshelve econstructor.
         + simpl.
           unshelve econstructor.
           ++ simpl.
              intros (a, b).
              intro f.
              simpl in eta.
              clear obeta ob1 ob2.
              specialize (eta (a, b)).
              simpl in eta. apply eta. exact f.
           ++ intros (a, b) (c, d) (f, g). simpl.
              apply functional_extensionality.
              intros h. simpl in obeta.
              clear ob1 ob2.
              specialize (obeta (a, b) (c, d) (f, g)).
              simpl in obeta.
              pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl obeta) as H';
              cbn beta in H'.
              rewrite H'. reflexivity.
         + simpl.
           unshelve econstructor.
           ++ simpl.
              intros (a, b).
              intro f.
              simpl in eps.
              clear obeps ob1 ob2.
              specialize (eps (a, b)).
              simpl in eps. apply eps. exact f.
           ++ intros (a, b) (c, d) (f, g). simpl.
              apply functional_extensionality.
              intros h. simpl in obeps.
              clear ob1 ob2.
              specialize (obeps (a, b) (c, d) (f, g)).
              simpl in obeps.
              pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl obeps) as H';
              cbn beta in H'.
              rewrite H'. reflexivity.
         + simpl. apply Nt_split.
           simpl.
           extensionality a.
           destruct a as (a, b).
           apply functional_extensionality.
           intros f.
           simpl in ob1.
           rewrite identity_f, preserve_id, f_identity.
           apply Nt_split in ob1.
           simpl in ob1.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob1) as H';
           cbn beta in H'.
           specialize (H' (a, b)).
           simpl in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl H') as H'';
           cbn beta in H''.
           rewrite H''.
           rewrite identity_f, preserve_id, f_identity.
           reflexivity.
         + simpl. apply Nt_split.
           simpl.
           extensionality a.
           destruct a as (a, b).
           apply functional_extensionality.
           intros f.
           simpl in ob2.
           rewrite preserve_id, f_identity, identity_f.
           apply Nt_split in ob2.
           simpl in ob2.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob2) as H';
           cbn beta in H'.
           specialize (H' (a, b)).
           simpl in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl H') as H'';
           cbn beta in H''.
           rewrite H''.
           rewrite preserve_id, f_identity, identity_f.
           reflexivity.
Qed.

Lemma HomNat_eqr: forall {C D: Category} (F: Functor C D) (G: Functor D C), HomAdjunction F G -> NatAdjunction F G.
Proof. intros C D F G (theta).
       destruct theta as (to, from, ob1, ob2).
       destruct to as (eta, obeta).
       destruct from as (eps, obeps).
       unshelve econstructor.
       - unshelve econstructor.
         + simpl.
           unshelve econstructor.
           ++ simpl.
              intros (a, b).
              intro f.
              simpl in eta.
              clear obeta ob1 ob2.
              specialize (eta (a, b)).
              simpl in eta. apply eta. exact f.
            ++ intros (a, b) (c, d) (f, g). simpl.
              apply functional_extensionality.
              intros h. simpl in obeta.
              clear ob1 ob2.
              specialize (obeta (a, b) (c, d) (f, g)).
              simpl in obeta.
              pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl obeta) as H';
              cbn beta in H'.
              rewrite H'. reflexivity.
         + simpl.
           unshelve econstructor.
           ++ simpl.
              intros (a, b).
              intro f.
              simpl in eps.
              clear obeps ob1 ob2.
              specialize (eps (a, b)).
              simpl in eps. apply eps. exact f.
           ++ intros (a, b) (c, d) (f, g). simpl.
              apply functional_extensionality.
              intros h. simpl in obeps.
              clear ob1 ob2.
              specialize (obeps (a, b) (c, d) (f, g)).
              simpl in obeps.
              pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl obeps) as H';
              cbn beta in H'.
              rewrite H'. reflexivity.
         + simpl. apply Nt_split.
           simpl.
           extensionality a.
           destruct a as (a, b).
           apply functional_extensionality.
           intros f.
           simpl in ob1.
           rewrite identity_f, preserve_id, f_identity.
           apply Nt_split in ob1.
           simpl in ob1.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob1) as H';
           cbn beta in H'.
           specialize (H' (a, b)).
           simpl in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl H') as H'';
           cbn beta in H''.
           rewrite H''.
           rewrite identity_f, preserve_id, f_identity.
           reflexivity.
         + simpl. apply Nt_split.
           simpl.
           extensionality a.
           destruct a as (a, b).
           apply functional_extensionality.
           intros f.
           simpl in ob2.
           rewrite preserve_id, f_identity, identity_f.
           apply Nt_split in ob2.
           simpl in ob2.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob2) as H';
           cbn beta in H'.
           specialize (H' (a, b)).
           simpl in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl H') as H'';
           cbn beta in H''.
           rewrite H''.
           rewrite preserve_id, f_identity, identity_f.
           reflexivity.
Qed.

Theorem HomNat_eq: forall {C D: Category} (F: Functor C D) (G: Functor D C), iffT (HomAdjunction F G) (NatAdjunction F G).
Proof. intros.
       split.
       - apply HomNat_eqr.
       - apply HomNat_eql.
Qed.

Theorem rcancel:  forall {C: Category} {a b c: @obj C}
                         (f g: arrow c b) (h: arrow b a), 
                          f = g -> f o h = g o h.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem lcancel:  forall {C: Category} {a b c: @obj C}
                         (f g: arrow b a) (h: arrow c b), 
                         f = g -> h o f  = h o g.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma NatAdj_eqr (C D: Category) (F: Functor C D) (U: Functor D C): Adjunction F U -> NatAdjunction F U.
Proof. intro A.
       unshelve econstructor.
       - unshelve econstructor.
         + cbn in *.
           unshelve econstructor.
           ++ intros. cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              intros. destruct a as (a, b).
              unfold id in *.
              clear comm_diag0 ob3 ob4.
              specialize (trans0 b).
              exact (trans0 o (fmap _ _ X)).
           ++ intros.  cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              intros.
              destruct a as (a0, a1).
              destruct b as (b0, b1).
              destruct f as (f, g).
              extensionality a. cbn in *.
              rewrite preserve_comp.
              specialize (@comm_diag b0 a0 f).
              repeat rewrite <- assoc.
              rewrite assoc.
              rewrite preserve_comp.
              repeat rewrite assoc.
              apply rcancel. apply rcancel.
              specialize (@comm_diag0 a1 b1 g). easy.
         + cbn in *.
           unshelve econstructor.
           ++ intros. cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              destruct a as (a, b).
              intros.
              clear comm_diag ob3 ob4.
              specialize (trans a).
              exact ((fmap0 _ _ X) o trans).
           ++ intros.  cbn in *.
              destruct A, F, U, unit0, counit0.
              cbn in *.
              intros.
              destruct a as (a0, a1).
              destruct b as (b0, b1).
              destruct f as (f, g).
              extensionality a. cbn in *.
              rewrite preserve_comp0.
              specialize (@comm_diag b0 a0 f).
              repeat rewrite <- assoc.
              rewrite assoc.
              rewrite preserve_comp0.
              apply lcancel. easy.
         + cbn in *.
           apply Nt_split. cbn in *.
           destruct A, F, U, unit0, counit0.
           cbn in *.
           extensionality a.
           extensionality b.
           destruct a as (a0, a1).
           cbn in *. rewrite preserve_id, identity_f, f_identity.
           rewrite preserve_comp. unfold id in *.
           specialize (@comm_diag0 _ _ b).
           rewrite assoc. rewrite <- comm_diag0.
           specialize (ob3 a0). rewrite <- assoc. rewrite ob3.
           now rewrite f_identity.
         + cbn in *.
           apply Nt_split. cbn in *.
           destruct A, F, U, unit0, counit0.
           cbn in *.
           extensionality a.
           extensionality b.
           destruct a as (a0, a1).
           cbn in *. rewrite preserve_id0, f_identity, identity_f.
           rewrite preserve_comp0. unfold id in *.
           specialize (@comm_diag _ _ b).
           rewrite <- assoc. rewrite comm_diag.
           specialize (ob4 a1). rewrite assoc. rewrite ob4.
           now rewrite identity_f.
Qed.

Lemma NatAdj_eql (C D: Category) (F: Functor C D) (U: Functor D C): NatAdjunction F U -> Adjunction F U.
Proof. intro A.
       unshelve econstructor.
       - unshelve econstructor.
         + intros. cbn in *.
           destruct A, ob0, to0, from0. cbn in *.
           clear comm_diag0 iso_to_from0 comm_diag0 iso_from_to0.
           specialize (trans0 (a, (fobj F a))).
           cbn in *. apply trans0.
           exact (identity (fobj F a)).
         + cbn in *. intros.
           destruct A, ob0, to0, from0. cbn in *.
           clear iso_to_from0 iso_from_to0.
           pose proof comm_diag0 as comm_diag00.
           specialize (comm_diag0 (a, (fobj F a))). cbn in *.
           specialize (comm_diag0 (a, (fobj F b))). cbn in *.
           specialize (comm_diag0 ((identity a), (fmap F f))).
           cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diag0) as H';
           cbv beta in H'.
           specialize (H'  (identity (fobj F a))).
           rewrite !preserve_id, !f_identity in H'.

           assert (trans0 (a, fobj F b) (fmap F f) = trans0 (b, fobj F b) (identity (fobj F b)) o f).
           { specialize (comm_diag00 (b, (fobj F b))). cbn in *.
             specialize (comm_diag00 (a, (fobj F b))). cbn in *.
             specialize (comm_diag00 (f, (identity (fobj F b))) ).
             cbn in *. 
             pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diag00) as H'';
             cbv beta in H''.
             specialize (H''  (identity (fobj F b))).
             rewrite !preserve_id, !f_identity, !identity_f in H''. easy. } 
             rewrite H in H'. easy.
       - unshelve econstructor.
         + intros. cbn in *.
           destruct A, ob0, to0, from0. cbn in *.
           clear comm_diag0 iso_to_from0 comm_diag0 iso_from_to0 comm_diag.
           specialize (trans ((fobj U a), a)).
           cbn in *. apply trans.
           exact (identity (fobj U a)).
         + cbn in *. intros.
           destruct A, ob0, to0, from0. cbn in *.
           clear iso_to_from0 iso_from_to0.
           pose proof comm_diag as comm_diagg.
           specialize (comm_diag ((fobj U a), a)). cbn in *.
           specialize (comm_diag ((fobj U a), b)). cbn in *.
           specialize (comm_diag ((identity (fobj U a)), f)).
           cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diag) as H';
           cbv beta in H'.
           specialize (H'  (identity (fobj U a))).
           rewrite !preserve_id, !f_identity in H'.

           assert (trans (fobj U a, b) (fmap U f) = trans (fobj U b, b) (identity (fobj U b)) o fmap F (fmap U f)).
           {
            specialize (comm_diagg ((fobj U b), b)). cbn in *.
            specialize (comm_diagg ((fobj U a), b)). cbn in *.
            specialize (comm_diagg ((fmap U f), (identity b))).
            cbn in *. 
            pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diagg) as H'';
            cbv beta in H''.
            specialize (H''  (identity (fobj U b))).
            rewrite !preserve_id, !f_identity, !identity_f in H''. easy. } 
           rewrite H in H'. easy.

       - cbn in *. intros.
         destruct A, ob0, to0, from0. cbn in *.
         pose proof comm_diag as comm_diagg.

         specialize (comm_diagg ((fobj U (fobj F a)), (fobj F a))). cbn in *.
         specialize (comm_diagg (a, (fobj F a))). cbn in *.
         specialize (comm_diagg (trans0 (a, fobj F a) (identity (fobj F a)), (identity (fobj F a)))).
         cbn in *. 
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diagg) as H'';
         cbv beta in H''.
         specialize (H''  (identity (fobj U (fobj F a)))).
         rewrite !preserve_id, !f_identity, !identity_f in H''.
         assert (trans (a, fobj F a) (trans0 (a, fobj F a) (identity (fobj F a))) = identity (fobj F a)).
         { 
           apply Nt_split in iso_to_from0. cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl iso_to_from0) as H';
           cbv beta in H'.
           specialize (H' (a, (fobj F a))). cbn in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H') as H0;
           cbv beta in H0.
           specialize (H0 (identity (fobj F a))).
           rewrite !identity_f, preserve_id in H0. easy.
          }
         rewrite H in H''. easy.

       - cbn in *. intros.
         destruct A, ob0, to0, from0. cbn in *.
         pose proof comm_diag0 as comm_diagg.

         specialize (comm_diagg ((fobj U a), (fobj F (fobj U a)))). cbn in *.
         specialize (comm_diagg ((fobj U a), a)). cbn in *.
         specialize (comm_diagg ((identity (fobj U a)), (trans (fobj U a, a) (identity (fobj U a))))).
         cbn in *.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl comm_diagg) as H'';
         cbv beta in H''.
         specialize (H''  (identity (fobj F (fobj U a)))).
         rewrite  !preserve_id, !f_identity in H''.
         assert (trans0 (fobj U a, a) (trans (fobj U a, a) (identity (fobj U a))) = identity (fobj U a)).
         { 
           apply Nt_split in iso_from_to0. cbn in *.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl  iso_from_to0) as H';
           cbv beta in H'.
           specialize (H' ((fobj U a), a)). cbn in H'.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H') as H0;
           cbv beta in H0.
           specialize (H0 (identity (fobj U a))).
           rewrite !f_identity, preserve_id in H0. easy.
          }
         rewrite H in H''. easy.
Qed.

Lemma NatAdj_eq (C D: Category) (F: Functor C D) (U: Functor D C): iffT (Adjunction F U) (NatAdjunction F U).
Proof. split.
       - apply NatAdj_eqr.
       - apply NatAdj_eql.
Qed.

Lemma HomAdj_eq (C D: Category) (F: Functor C D) (U: Functor D C): iffT (Adjunction F U) (HomAdjunction F U).
Proof. split.
       - intro A. apply HomNat_eq.
         apply NatAdj_eq. exact A.
       - intro A. apply NatAdj_eq.
         apply HomNat_eq. exact A.
Qed.


Lemma ISOAt: forall (C: Category) (X Y: @obj C) (I: @IsomorphismA C X Y), @Isomorphism C X Y (to I).
Proof. intros C X Y I.
       destruct I. simpl.
       unshelve econstructor.
       - exact from0.
       - easy.
       - easy.
Qed.

Lemma ISOAf: forall (C: Category) (X Y: @obj C) (I: @IsomorphismA C X Y), @Isomorphism C Y X (from I).
Proof. intros C X Y I.
       destruct I. simpl.
       unshelve econstructor.
       - exact to0.
       - easy.
       - easy.
Qed.

Lemma bijisorFC: forall (C: Category) (X Y: @obj C) (F: @obj (FunctorCategory C TypeCat)) 
                        (f: @arrow TypeCat (fobj F Y) (fobj F X)), 
                        Isomorphism TypeCat f -> bijection f.
Proof. intros C X Y F f (finv, ax1, ax2). simpl in *.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl ax1) as ax1';
       cbv beta in ax1'.
       pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl ax2) as ax2';
       cbv beta in ax2'.
       unshelve econstructor.
       - unfold injective.
         intros x y H.
         pose proof ax2' as ax2''.
         specialize (ax2' x).
         rewrite H in ax2'.
         rewrite ax2'' in ax2'. easy.
       - unfold surjective.
         intro y.
         exists (finv y).
         rewrite ax1'. easy.
Qed.

Class monoNT {C D: Category} {F G: Functor C D} (eta: NaturalTransformation F G): Type :=
{
  etalc: forall {X: @obj C} {Y: @obj D} (f g: arrow (fobj F X) Y), (trans eta X) o f = (trans eta X) o g -> f = g
}.

Class epiNT {C D: Category} {F G: Functor C D} (eta: NaturalTransformation F G): Type :=
{
  etarc: forall {X: @obj C} {Y: @obj D} (f g: arrow Y (fobj G X)), f o (trans eta X) = g o (trans eta X) -> f = g
}.

Class monoNTF {C D: Category} {F G: Functor C D} (eta: NaturalTransformation F G): Type :=
{
  etalcF: forall {H: Functor C D}
                 (nt1 nt2: NaturalTransformation H F), 
                 @comp (FunctorCategory C D) _ _ _ eta nt1 = @comp (FunctorCategory C D) _ _ _ eta nt2 -> nt1 = nt2
}.

Lemma Iso_monoNTF: forall (C D: Category) (F G: Functor C D) (eta: NaturalTransformation F G),
  Isomorphism (FunctorCategory C D) eta -> monoNTF eta.
Proof. intros C D F G (to, cct) ((from, ccf), ob1, ob2).
       unshelve econstructor.
       - simpl.
         intros H (nt1, ccnt1) (nt2, ccnt2) Hb.
         apply Nt_split.
         simpl.
         apply Nt_split in Hb, ob1, ob2.
         simpl in Hb, ob1, ob2.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl Hb) as Hb';
         cbn beta in Hb'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob1) as ob1';
         cbn beta in ob1'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob2) as ob2';
         cbn beta in ob2'.
         extensionality x.
         assert (from x o to x o nt1 x = from x o to x o nt2 x).
         { do 2 rewrite <- assoc.
           rewrite Hb'.
           reflexivity.
         }
         rewrite ob2' in H0.
         rewrite preserve_id, !identity_f in H0.
         exact H0.
Qed.

Lemma Iso_monoNT: forall (C D: Category) (F G: Functor C D) (eta: NaturalTransformation F G),
  Isomorphism (FunctorCategory C D) eta -> monoNT eta.
Proof. intros C D F G (to, cct) ((from, ccf), ob1, ob2).
       simpl in *.
       unshelve econstructor.
       - intros X Y f g.
         simpl.
         intro H.
         apply Nt_split in ob1, ob2.
         simpl in ob1, ob2.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob2) as H';
         cbn beta in H'.
         assert (from X o to X o f = from X o to X o g).
         { rewrite <- assoc. 
           rewrite H.
           rewrite assoc.
           reflexivity.
         }
         rewrite H' in H0.
         rewrite preserve_id, !identity_f in H0.
         exact H0.
Defined.

Lemma Iso_monoNTC: forall (C: Category) (X: @obj C) (F G: Functor C TypeCat) (eta: NaturalTransformation F G),
  Isomorphism (FunctorCategory C TypeCat) eta -> bijection (trans eta X).
Proof. intros C X F G eta I.
       apply bijisorT.
       destruct I as (from, ob1, ob2).
       simpl in *.
       unshelve econstructor.
       - simpl. exact (trans from X).
       - simpl. 
         apply functional_extensionality.
         intro gx.
         apply Nt_split in ob1.
         simpl in ob1.
         pose proof (fun x y => eq_ind_r (fun f => f x y = _ x y) eq_refl ob1) as H';
         cbn beta in H'.
         rewrite H'.
         rewrite preserve_id.
         simpl.
         reflexivity.
       - simpl. 
         apply functional_extensionality.
         intro fx.
         apply Nt_split in ob2.
         simpl in ob2.
         pose proof (fun x y => eq_ind_r (fun f => f x y = _ x y) eq_refl ob2) as H';
         cbn beta in H'.
         rewrite H'. 
         rewrite preserve_id.
         simpl.
         reflexivity.
Qed.

Lemma Iso_epiNT: forall (C D: Category) (F G: Functor C D) (eta: NaturalTransformation F G),
  Isomorphism (FunctorCategory C D) eta -> epiNT eta.
Proof. intros C D F G (to, cct) ((from, ccf), ob1, ob2).
       simpl in *.
       unshelve econstructor.
       - intros X Y f g.
         simpl.
         intro H.
         apply Nt_split in ob1, ob2.
         simpl in ob1, ob2.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl ob1) as H';
         cbn beta in H'.
         assert (f o to X o from X = g o to X o from X).
         { rewrite H.
           reflexivity.
         }
         do 2 rewrite <- assoc in H0.
         rewrite H' in H0.
         rewrite preserve_id, !f_identity in H0.
         exact H0.
Qed.


Lemma UPl: forall (C D: Category) (F: Functor C D),
  { G: Functor D C & HomAdjunction F G } ->
  (forall (Y: @obj D), { GY: @obj C &
                       { eps: arrow Y (fobj F GY) &
  (forall (X: @obj C) (g: arrow Y (fobj F X)), 
    { g': arrow GY X | eps o (fmap F g') = g /\ (forall f: arrow GY X, eps o (fmap F f) = g -> f = g') } ) } } ).
Proof. intros C D F (G, (theta)) Y.
       specialize (ISOAt _ _ _ theta); intro TI.

       destruct theta as (to, from, ob1, ob2).
       simpl in *.

       exists (fobj G Y).

       destruct to as (tot, H).
       simpl in tot.
       unfold id in tot.

       exists (tot (fobj G Y, Y) (identity (fobj G Y))).

       intros.

       specialize (Iso_monoNTC (ProductCategory (DualCategory C) D) (X, Y) _ _ _ TI); intro HC.
       destruct HC.
       unfold surjective in fsurj.
       specialize (fsurj g).
       destruct fsurj as (fS, fsurj).
       clear TI.
       exists fS.

       split.
       - simpl in finj, fsurj.
         clear ob1 ob2.
         specialize (H (fobj G Y, Y) (X, Y) (fS, identity Y)). 
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl H) as H';
         cbv beta in H'.
         specialize (H' (identity (fobj G Y))).
         simpl in H'.
         rewrite f_identity, identity_f, preserve_id in H'.

         unfold id in H'.
         rewrite H'.

         unfold surjective in fsurj.
         rewrite identity_f, fsurj.
         reflexivity.
       - intros f Hf.
         simpl in finj, fsurj.
         unfold injective in finj.

         apply finj.
         cbn in fS.
         rewrite fsurj.
         rewrite <- Hf.

         simpl in H.
         clear ob1 ob2.
         specialize (H (fobj G Y, Y) (X, Y) (f, identity Y)).
         simpl in H.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl H) as H';
         cbv beta in H'.
         specialize (H' (identity (fobj G Y))).
         rewrite !f_identity, !identity_f, preserve_id in H'.
         unfold id in H'.
         rewrite H'.
         rewrite identity_f.
         reflexivity.
Qed.

Lemma UPr: forall (C D: Category) (F: Functor C D),
  (forall (Y: @obj D), { GY: @obj C &
                       { eps: arrow Y (fobj F GY) &
  (forall (X: @obj C) (g: arrow Y (fobj F X)), 
    { g': arrow GY X | eps o (fmap F g') = g /\ (forall h: arrow GY X, eps o (fmap F h) = g -> h = g') } ) } } ) ->
  { G: Functor D C & HomAdjunction F G }.
Proof. intros C D F H.
       unshelve econstructor.
       - unshelve econstructor.
         + intro Y.
           specialize (H Y).
           destruct H as (GY, H).
           exact GY.
         + intros Y' Y g. simpl in *.
           destruct (H Y) as (GY, (epsY, HY)).
           destruct (H Y') as (GY', (epsY', HY')).
           simpl in *.
           specialize (HY GY' (g o epsY')).
           destruct HY.
           exact x.
         + repeat intro. now subst.
         + simpl.
           intro X.
           destruct (H X) as (GX, (epsX, HX)).
           destruct (HX GX (identity X o epsX)).
           destruct a as (Ha, Hb).
           specialize (Hb (identity GX)).
           symmetry.
           apply Hb.
           rewrite preserve_id, f_identity, identity_f.
           reflexivity.
         + simpl.
           intros X Y Z g f.
           destruct (H X) as (GX, (epsX, HX)).
           destruct (H Y) as (GY, (epsY, HY)).
           destruct (H Z) as (GZ, (epsZ, HZ)).
           simpl in *.
           destruct (HZ GX (g o f o epsX)) as (a, (Ha1, Ha2)).
           destruct (HZ GY (g o epsY)) as (b, (Hb1, Hb2)).
           destruct (HY GX (f o epsX)) as (c, (Hc1, Hc2)).
           specialize (Ha2 (b o c)).
           rewrite preserve_comp, assoc, Hb1, <- assoc, Hc1, assoc in Ha2.
           symmetry.
           apply Ha2.
           reflexivity.
       - unshelve econstructor.
         + unshelve econstructor.
           ++ unshelve econstructor.
              +++ simpl.
                  intros (X, Y).
                  destruct (H Y) as (GY, (epsY, HY)).
                  intro f.
                  exact (epsY o fmap F f).
              +++ simpl.
                  intros (X, Y) (X', Y') (f, g).
                  simpl.
                  destruct (H Y) as (GY, (epsY, HY)).
                  destruct (H Y') as (GY', (epsY', HY')).
                  destruct (HY' GY (g o epsY)) as (a, (Ha1, Ha2)).
                  extensionality Z.
                  rewrite !preserve_comp.
                  do 3 rewrite assoc.
                  rewrite Ha1.
                  reflexivity.
           ++ simpl.
              unshelve econstructor.
              +++ simpl.
                  intros (X, Y).
                  destruct (H Y) as (GY, (epsY, HY)).
                  intro f.
                  specialize (HY X f).
                  destruct HY.
                  exact x.
              +++ simpl. 
                  intros (X, Y) (X', Y') (f, g).
                  simpl.
                  extensionality Z.
                  destruct (H Y) as (GY, (epsY, HY)).
                  destruct (H Y') as (GY', (epsY', HY')).
                  destruct (HY' GY (g o epsY)) as (a, (Ha1, Ha2)).
                  destruct (HY X Z) as (b, (Hb1, Hb2)).
                  unfold id in *.
                  destruct (HY' X' (g o Z o fmap F f)) as (c, (Hc1, Hc2)).
                  specialize (Hc2 (a o b o f)).
                  rewrite Hc2.
                  * reflexivity.
                  * rewrite !preserve_comp.
                    do 2 rewrite assoc.
                    rewrite Ha1.
                    do 2 rewrite <- assoc.
                    setoid_rewrite assoc at 2.
                    rewrite Hb1.
                    rewrite assoc.
                    reflexivity.
           ++ simpl.
              apply Nt_split.
              simpl.
              extensionality X.
              destruct X as (X, Y).
              extensionality f.
              destruct (H Y) as (GY, (epsY, HY)).
              destruct (HY X f) as (a, (Ha1, Ha2)).
              rewrite preserve_id, identity_f, f_identity.
              unfold id in *.
              rewrite Ha1.
              reflexivity.
           ++ apply Nt_split.
              simpl.
              extensionality X.
              destruct X as (X, Y).
              extensionality f.
              destruct (H Y) as (GY, (epsY, HY)).
              destruct (HY X (epsY o fmap F f)) as (a, (Ha1, Ha2)).
              destruct (HY GY (identity Y o epsY)) as (b, (Hb1, Hb2)).
              rewrite f_identity.
              specialize (Ha2 (b o f)).
              rewrite Ha2.
              * reflexivity.
              * rewrite preserve_comp, assoc, Hb1, identity_f.
                reflexivity.
Qed.

Lemma UP: forall (C D: Category) (F: Functor C D),
  iffT
  (forall (Y: @obj D), { GY: @obj C &
                       { eps: arrow Y (fobj F GY) &
  (forall (X: @obj C) (g: arrow Y (fobj F X)), 
    { g': arrow GY X | eps o (fmap F g') = g /\ (forall h: arrow GY X, eps o (fmap F h) = g -> h = g') } ) } } ) 
  { G: Functor D C & HomAdjunction F G }.
Proof. intros.
       split.
       - apply UPr.
       - apply UPl.
Qed.

Definition DiagonalFunctor (C: Category): Functor C (ProductCategory C C).
Proof. unshelve econstructor.
       - simpl. intro X. exact (X, X).
       - simpl. intros X Y f. exact (f, f).
       - repeat intro. now subst.
       - simpl. easy.
       - simpl. easy.
Defined.

(** iProdFunctor C X hp -- slides #105 *)

Theorem UP_Instance_Product_L: forall (C: Category), 
  hasProducts C -> { G: Functor (ProductCategory C C) C & HomAdjunction (DiagonalFunctor C) G }.
Proof. intros C hp.
       apply UPr.
       intros (X, Y). simpl in *.
       exists (@pobj C hp X Y).
       destruct hp as (P, hp).
       exists ((@pi1 C X Y (P X Y) (hp X Y)), (@pi2 C X Y (P X Y) (hp X Y))).
       intros Z (f, g).
       simpl.
       destruct (hp X Y). simpl in *.
       exists (prod_f Z f g).
       split.
       - specialize (prod_f_c1 Z f g).
         rewrite prod_f_c1 at 3.
         specialize (prod_f_c2 Z f g).
         rewrite prod_f_c2 at 4.
         reflexivity.
       - intros h H.
         specialize (prod_f_uni Z f g h).
         rewrite prod_f_uni.
         + reflexivity.
         + inversion H. reflexivity.
         + inversion H. reflexivity.
Qed.

Theorem UP_Instance_Product_R: forall (C: Category), 
 { G: Functor (ProductCategory C C) C & HomAdjunction (DiagonalFunctor C) G } -> hasProducts C.
Proof. intros C H.
       specialize (UPl _ _ _ H); intro Ha.
       unshelve econstructor.
       - intros X Y.
         specialize (Ha (X, Y)).
         destruct Ha as (P, r).
         exact P.
       - simpl. intros X Y.
         destruct Ha as (P, ((pi1, pi2), r)).
         simpl in pi1, pi2.
         unshelve econstructor.
         + exact pi1.
         + exact pi2.
         + intros Z f g.
           specialize (r Z (f, g)).
           simpl in r.
           destruct r as (g', r).
           exact g'.
         + intros Z f g.
           simpl.
           destruct (r Z (f, g)) as (a, (Ha1, Ha2)).
           simpl in Ha1, Ha2.
           inversion Ha1.
           reflexivity.
         + intros Z f g.
           simpl.
           destruct (r Z (f, g)) as (a, (Ha1, Ha2)).
           simpl in Ha1, Ha2.
           inversion Ha1.
           reflexivity.
         + intros Z f g p1 Hp1 Hp2.
           simpl in r.
           simpl.
           destruct r as (g', (r1, r2)).
           rewrite <- (r2 p1).
           * reflexivity.
           * rewrite Hp1, Hp2.
             reflexivity.
Qed.

Theorem UP_Instance_Product: forall (C: Category), 
 iffT { G: Functor (ProductCategory C C) C & HomAdjunction (DiagonalFunctor C) G } (hasProducts C).
Proof. intro C.
       split.
       - apply UP_Instance_Product_R.
       - apply UP_Instance_Product_L.
Qed.

(** iProdFunctor C X hp -- slides #105 *)

Theorem UP_Instance_Exponential_L: forall (C: Category) (hp: hasProducts C), 
  hasExponentials C hp -> (forall X, { G: Functor C C & HomAdjunction (iProdFunctor C X hp) G }).
Proof. intros C hp he X.
       apply UPr.
       intros Y.
       exists (@eobj C hp he X Y).
       exists (@app C hp X Y (@eobj C hp he X Y) (@hase C hp he X Y)).
       simpl in *.
       intros Z g.
       exists (@cur C hp X Y (@eobj C hp he X Y) (@hase C hp he X Y) Z g).
       split.
       - destruct he as (E, he).
         destruct hp as (P, hp).
         simpl in *.
         destruct (he X Y).
         destruct (hp (E X Y) X).
         simpl in *.
         specialize (curcomm Z g).
         destruct (hp Z X) in *.
         rewrite curcomm.
         reflexivity.
       - intros h H.
         destruct he as (E, he).
         destruct hp as (P, hp).
         simpl in *.
         destruct (he X Y).
         destruct (hp (E X Y) X).
         simpl in *.
         specialize (curuni Z g h).
         symmetry.
         apply curuni.
         exact H.
Qed.

Theorem UP_Instance_Exponential_R: forall (C: Category) (hp: hasProducts C), 
  (forall X, { G: Functor C C & HomAdjunction (iProdFunctor C X hp) G }) -> hasExponentials C hp.
Proof. intros C hp H.
       unshelve econstructor.
       - intros Y Z.
         specialize (H Y).
         specialize (UPl _ _ _ H); intro Ha.
         simpl in *.
         specialize (Ha Z).
         destruct Ha as (E, (app, r)).
         exact E.
       - simpl. intros Y Z.
         destruct (UPl C C (iProdFunctor C Y hp) (H Y) Z) as (E, (app, r)).
         simpl in *. 
         unshelve econstructor.
         + simpl in *.
           exact app.
         + intros X g.
           specialize (r X g).
           destruct r as (curg, r).
           exact curg.
         + intros X g.
           simpl.
           destruct (r X g) as (curg, (Ha1, Ha2)).
           rewrite Ha1. 
           reflexivity.
         + intros X g g' Hg'.
           simpl.
           destruct (r X g) as (curg, (Ha1, Ha2)).
           symmetry.
           apply Ha2.
           rewrite Hg'.
           reflexivity.
Qed.

Theorem UP_Instance_Exponential: forall (C: Category) (hp: hasProducts C), 
  iffT (forall X, { G: Functor C C & HomAdjunction (iProdFunctor C X hp) G }) (hasExponentials C hp).
Proof. intros C hp.
       split.
       - apply UP_Instance_Exponential_R.
       - apply UP_Instance_Exponential_L.
Qed.


