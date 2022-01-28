From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor
NaturalTransformation Adjunction ParamKleisliTriple Monad Presheaf Yoneda IndexedCategories.

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

Lemma adj_unique_map: forall (C D: Category) (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
       (forall (a: @obj C) (b: @obj D) (f: @arrow C (fobj G b) a) (g h: @arrow D b (fobj F a)),
         f = fmap G g o (trans (@unit C D F G A) a) -> 
         f = fmap G h o (trans (@unit C D F G A) a) -> g = h).
Proof. intros C D F G A a b f g h Hg Hh.
       destruct A as (eta, eps, cc1, cc2).
       rewrite Hg in Hh.
       apply (f_equal (fmap F)), (f_equal (fun w => comp((trans eps) _ ) w)) in Hh.
       destruct eps. cbn in *. unfold id in *.
       rewrite !preserve_comp in Hh.
       rewrite !assoc, <- !comm_diag in Hh.
       rewrite <- !assoc in Hh.
       now rewrite !cc1, !f_identity in Hh.
Qed.

(** the comparison functor L *)
Definition L: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A     : Adjunction F G),
               let M  := (adj_mon F G A) in
               let CM := (adj_comon F G A) in
               let CK := (Monad.Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (Monad.FTK (Compose_Functors F G) M) in
               let GT := (Monad.GTK (Compose_Functors F G) M) in Functor CK D.
Proof. intros C D F G A M CM CK FTK GTK.
       unshelve econstructor.
       - exact (fobj F).
       - intros a b f.
         destruct CM as (eps, delta, cc1, cc2, cc3, cc4).
         exact (trans eps (fobj F b) o fmap F f).
       - repeat intro. now subst.
       - intros. destruct A, unit, counit.
         cbn in *. now rewrite <- ob1.
       - intros. cbn in *.
         destruct A, unit, counit. cbn in *.
         rewrite preserve_comp.
         do 2 rewrite assoc.
         apply rcancel.
         rewrite <- preserve_comp.
         now rewrite <- comm_diag0.
Defined.

(** the functor L makes the diagram in the theorem statement 
commutative at both directions *)
Lemma commL: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A    : Adjunction F G),
               let M  := (@adj_mon   C D F G A) in
               let CK := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FTK (Compose_Functors F G) M) in
               let GT := (GTK (Compose_Functors F G) M) in
                 (Compose_Functors FT (L F G A)) = F /\ (Compose_Functors (L F G A) G) = GT.
Proof. intros C D F G A1 M CK FT GT; split.
       - apply F_split. 
         + simpl.  easy.
         + apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, eq_existT_uncurried. 
           cbn in *. unfold id in *.
           unfold eq_rect.
           exists (@eq_refl _ (forall a b : obj, arrow b a -> 
                               arrow (fobj F b) (fobj F a))).
           extensionality a.
           extensionality b.
           extensionality f.
           destruct M, A1, unit. cbn in *.
           rewrite preserve_comp.
           assert ( fmap F f = identity (fobj F b)  o  fmap F f).
           { now rewrite identity_f. }
           rewrite H at 2. rewrite assoc. 
           apply rcancel.
           apply ob1.
       - apply F_split.
         + easy.
         + apply eq_dep_id_JMeq. 
           apply EqdepFacts.eq_sigT_iff_eq_dep.
           apply eq_existT_uncurried. 
           cbn in *. unfold id in *.
           exists (@eq_refl _ (forall a b : obj, arrow (fobj G (fobj F b)) a -> 
                               arrow (fobj G (fobj F b)) (fobj G (fobj F a)))).
           unfold eq_rect.
           extensionality a.
           extensionality b.
           extensionality f.
           destruct M, A1, unit. cbn in *.
           now rewrite preserve_comp.
Qed.


(** uniqueness of the comparison functor L *)
Lemma uniqueL: forall
                   {C D: Category}
                   (F: Functor C D)
                   (G: Functor D C)
                   (A1: Adjunction F G),
                   let  M := (adj_mon   F G A1) in
                   let CK := (Kleisli_Category C (Compose_Functors F G) M) in
                   let FT := (FTK (Compose_Functors F G) M) in
                   let GT := (GTK (Compose_Functors F G) M) in
                   let A2 := (mon_kladj F G M) in
                     forall R : CK → D, Compose_Functors FT R = F /\ Compose_Functors R G = GT -> (L F G A1) = R.
Proof. intros C D F G A1 M CK FT GT A2 R H.
       assert (H1: Compose_Functors FT (L F G A1) = F /\ Compose_Functors (L F G A1) G = GT).
       specialize (commL F G A1); intros. apply H0.
       destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       apply F_split.
       - rewrite <- H1a in Ha.
         assert (fobj (Compose_Functors FT R) = fobj (Compose_Functors FT (L F G A1))).
         rewrite Ha. easy.
         easy.
       - cbn in *.
         rewrite <- H1a in Ha.
         assert (fobj (Compose_Functors FT R) = fobj (Compose_Functors FT (L F G A1))).
         rewrite Ha. easy.
         assert (fobj (Compose_Functors FT R) = fobj R).
         cbn. easy.
         assert (fobj (Compose_Functors FT R) = fobj (L F G A1)).
         cbn in *. easy.
         rewrite H0 in H1.
         apply eq_dep_id_JMeq. cbn in *.
         apply EqdepFacts.eq_sigT_iff_eq_dep. cbn in *.
         apply eq_existT_uncurried.
         assert (p: (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj F b) (fobj F a)) =
                    (forall a b : obj, arrow (fobj G (fobj F b)) a -> arrow (fobj R b) (fobj R a))).
         { rewrite H1. easy. }
         exists p.
         unfold eq_rect.
         destruct R. cbn in *.
         subst fobj.
         assert (p = eq_refl).
         {  apply UIP. }
         rewrite H1.
         extensionality a. extensionality b. extensionality f.
         apply (adj_unique_map _ _ _ _ A1) with (f := f).

         rewrite !Functor.preserve_comp, <- !assoc.
         destruct A1, unit. cbn in *. unfold id in *.
         rewrite comm_diag.
         rewrite !assoc.
         now rewrite ob2, identity_f.
         assert (Functor.fmap G (fmap a b f) = Functor.fmap GT f).
         { unfold Compose_Functors, GT, adj_mon in Hb. cbn in Hb. 
           inversion Hb.
           apply inj_pair2 in H3.
           pose proof (fun x y z => eq_ind_r (fun f => f x y z = _ x y z) eq_refl H3) as H3';
           cbv beta in H3'.
           now specialize (H3' _ _ f).
         }
         rewrite H2.
         destruct A1, unit. cbn in *. unfold id in *.
         rewrite <- assoc, comm_diag.
         now rewrite assoc, ob2, identity_f.
Qed.

(** Mac Lane's comparison theorem for the Kleisli Construction *)
Theorem ComparisonMacLane: forall
               {C D   : Category}
               (F     : Functor C D)
               (G     : Functor D C) 
               (A1    : Adjunction F G),
               let M  := (@adj_mon   C D F G A1) in
               let CT := (Kleisli_Category C (Compose_Functors F G) M) in
               let FT := (FTK (Compose_Functors F G) M) in
               let GT := (GTK (Compose_Functors F G) M) in
               let A2 := (mon_kladj F G M) in
               exists !L, (Compose_Functors FT L) = F /\ (Compose_Functors L G) = GT.
Proof. intros C D F G A1 M CT FT GT A2.
       exists (L F G A1). split.
       - apply commL.
       - apply uniqueL.
Qed.
Check ComparisonMacLane.
