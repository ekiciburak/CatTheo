From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple Monad Presheaf Yoneda IndexedCategories ComparisonK EilenbergMoore.
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

Arguments eta {_ _} _.
Arguments mu  {_ _} _.

Arguments unit {_ _ _ _} _.
Arguments counit {_ _ _ _} _.


Definition KT: ∏ {C D: Category} (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
                let M   := adj_mon F G A in
                let EMC := EilenbergMooreCategory M in Functor D EMC.
Proof. intros.
       unshelve econstructor.
       - intro X.
         exists (fobj G X).
         exists (fmap G (trans (counit A) X)).
         split.
         + now rewrite (@ob2 _ _ _ _ A).
         + cbn in *.
           rewrite <- !preserve_comp. f_equal.
           specialize (@comm_diag _ _ _ _ (counit A) _ _ (trans (counit A) X)); intro H.
           cbn in *. unfold id in *. now rewrite <- H.
       - intros X Y f. 
         exists (fmap G f).
         cbn in *.
         rewrite <- !preserve_comp. f_equal.
         specialize (@comm_diag _ _ _ _ (counit A) _ _ f); intro H.
         cbn in *. unfold id in *. now rewrite <- H.
       - repeat intro. now subst.
       - intro X.
         apply eqTAM. cbn in *.
         now rewrite preserve_id.
       - intros X Y Z g f.
         apply eqTAM.
         cbn in *.
         now rewrite preserve_comp.
Defined.


Lemma commKT: ∏ {C D: Category} (F: Functor C D) (G: Functor D C) (A: Adjunction F G),
               let M   := (adj_mon F G A) in
               let EMC := (EilenbergMooreCategory M) in
                 (Compose_Functors (KT F G A) (GT M)) = G /\ (Compose_Functors F (KT F G A)) = (FT M).
Proof. intros C D F G A M EMC; split. 
       - apply F_split.
         + easy.
         + apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, eq_existT_uncurried.
           cbn. unfold eq_rect.
           exists eq_refl. easy.
       - apply F_split.
         + cbn. unfold id in *.
           extensionality a.
           apply f_equal.
           apply eqTA; easy.
         + assert (H: fobj (Compose_Functors F (KT F G A)) = fobj (FT M)).
           cbn. unfold id in *.
           extensionality a.
           apply f_equal.
           apply eqTA; easy.

           apply eq_dep_id_JMeq.
           apply EqdepFacts.eq_sigT_iff_eq_dep.
           apply eq_existT_uncurried.

           assert ((∏ a b : obj,
           arrow b a -> arrow (fobj (Compose_Functors F (KT F G A)) b) 
            (fobj (Compose_Functors F (KT F G A)) a)) =
            (∏ a b : obj, arrow b a -> arrow (fobj (FT M) b) (fobj (FT M) a)) ).
           { now rewrite H. }

           exists H0.
           unfold eq_rect.
           assert (H0 = eq_refl).
           { specialize (UIP_refl _  
               (∏ a b : obj, arrow b a -> arrow (fobj (FT M) b) (fobj (FT M) a))); intros.
             now specialize (H1 H0).
           }
           rewrite H1.
           cbn.

           extensionality x.
           extensionality y.
           extensionality f.
           now apply subset_eq_compat.
Qed.

Arguments fmap {_} {_} _ _ _ _.
Arguments fobj {_} {_} _ _.

(** sameness of Functors, inspired by Amin Timany *)
Lemma F_split2: forall
               (C D  : Category)
               (F G  : Functor C D)
               (ObjEq: (fobj F) = (fobj G)),
               ((fun a b => 
                   match ObjEq in _ = V return ((arrow b a) -> (arrow (V b) (V a))) with
                    | eq_refl => (fmap F a b)
                   end) = fmap G) -> F = G.
Proof.
    destruct F; destruct G; simpl; intros; subst; f_equal.
    now destruct (proof_irrelevance _ fmapP0 fmapP).
    now destruct (proof_irrelevance _ preserve_id0 preserve_id).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp).
Defined.

Lemma K_unique: forall
               {C D    : Category}
               (F      : Functor C D)
               (G      : Functor D C) 
               (A1     : Adjunction F G),
               let M   := (adj_mon F G A1) in
               let EMC := (EilenbergMooreCategory M) in
               let A2  := (mon_emadj M) in
                 forall R : Functor D EMC, Compose_Functors R (GT M) = G /\
                                           Compose_Functors F R = (FT M) -> (KT F G A1) = R.
Proof. intros C D F G A1 M CK A2 R H.
       assert (H1: (Compose_Functors (KT F G A1) (GT M)) = G /\ (Compose_Functors F (KT F G A1)) = (FT M)).
       specialize (commKT F G A1); intros cKT. apply cKT.
       destruct H as (Ha, Hb).
       destruct H1 as (H1a, H1b).
       assert (fobj (KT F G A1) = fobj R).
       { extensionality a.
         apply EMOeq.
         split.
         + simpl.
           rewrite <- H1b in Hb.
           assert (H2: fobj (Compose_Functors F R) = fobj (Compose_Functors F (KT F G A1))).
           rewrite Hb. easy.
           rewrite <- H1a in Ha.
           assert (H3: fobj (Compose_Functors R (GT M)) = fobj (Compose_Functors (KT F G A1) (GT M))).
           rewrite Ha. easy.
           cbn in H3.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H3) as H3';
           cbv beta in H3'.
           specialize (H3' a).
           rewrite <- H3'.
           reflexivity.
         + apply eq_dep_id_JMeq.
           apply EqdepFacts.eq_sigT_iff_eq_dep.
           apply eq_existT_uncurried.
           simpl.
           assert (fobj G a = projT1 (fobj R a)).
           {
           rewrite <- H1b in Hb.
           assert (H2: fobj (Compose_Functors F R) = fobj (Compose_Functors F (KT F G A1))).
           rewrite Hb. easy.
           rewrite <- H1a in Ha.
           assert (H3: fobj (Compose_Functors R (GT M)) = fobj (Compose_Functors (KT F G A1) (GT M))).
           rewrite Ha. easy.
           cbn in H3.
           pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H3) as H3';
           cbv beta in H3'.
           specialize (H3' a).
           rewrite <- H3'.
           reflexivity.
           }
           cbn in *.
           unfold eq_rect.
           destruct (fobj R a).
           simpl.
           simpl in H.
           subst.
           exists eq_refl.
           destruct t as (f, (tob1, tob2)).
           simpl in *.

           destruct A1 as ((unit, obun), (counit, obcoun), ob1, ob2).
           simpl in *.
           rewrite <- ob2 in tob1.
           admit.
       }
       apply F_split2 with (ObjEq := H).
       extensionality a.
       extensionality b.
       extensionality f.
       apply eqTAM.
       f_equal.
       destruct R.
       simpl in *.
       subst fobj.
       rewrite sig_eta.
       Search exist.
       apply subset_eq_compat.
       simpl.
       destruct G.
       simpl in *.
Admitted.


