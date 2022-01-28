From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple Monad Presheaf.
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

Definition YonedaFunctor (C: Category): Functor C (PresheafCat C).
Proof. unshelve econstructor.
       - intro X.
         unshelve econstructor.
         + simpl. intro Z.
           exact (@arrow C X Z).
         + simpl. intros Y Z f g.
           exact (g o f).
         + simpl. repeat intro. now subst.
         + simpl. intro Y.
           apply functional_extensionality.
           intro f. 
           rewrite f_identity.
           reflexivity.
         + simpl. intros Y Z W f g.
           apply functional_extensionality.
           intro h.
           rewrite assoc.
           reflexivity.
       - simpl. intros Y X f.
         unshelve econstructor.
           ++ intros Z g.
              exact (f o g).
           ++ simpl. intros Z W g.
              apply functional_extensionality.
              intro h.
              rewrite assoc.
              reflexivity.
       - repeat intro. now subst.
       - simpl. intro X.
         unfold IdNt.
         apply Nt_split.
         simpl.
         extensionality Z.
         apply functional_extensionality.
         intro h.
         rewrite f_identity, identity_f.
         reflexivity.
       - simpl. intros X Y Z g f.
         unfold IdNt.
         apply Nt_split.
         simpl.
         extensionality W.
         apply functional_extensionality.
         intro h.
         rewrite assoc.
         reflexivity.
Defined.

Lemma YonedaEmbedding (C: Category) (X: @obj C) (F: @obj (PresheafCat C)):
  @IsomorphismA TypeCat (@arrow (PresheafCat C) F (fobj (YonedaFunctor C) X))
                        (fobj F X).
Proof. unshelve econstructor.
       - simpl. intros (phi, cc).
         simpl in *.
         exact (phi X (identity X)).
       - simpl. intro fx.
         unshelve econstructor.
         + simpl. intros Y f.
           exact ((fmap F f) fx).
         + simpl. intros Y Z f.
           apply functional_extensionality.
           intro g.
           unfold PresheafCat in F.
           specialize (@preserve_comp (DualCategory C) TypeCat F _ _ _ f g); intro H.
           simpl in H.
           rewrite H.
           reflexivity.
       - simpl.
         apply functional_extensionality.
         intro fx.
         specialize (@preserve_id (DualCategory C) TypeCat F); intro H.
         rewrite H.
         simpl.
         reflexivity.
       - simpl.
         apply functional_extensionality.
         intros (eta, cc).
         simpl in *.
         apply Nt_split.
         simpl.
         extensionality Y.
         apply functional_extensionality.
         intro f.
         specialize (cc X Y f).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl cc) as H';
         cbn beta in H'.
         specialize (H' (identity X)).
         rewrite identity_f in H'.
         rewrite H'.
         reflexivity.
Defined.

Lemma YEIsomorphic: forall (C: Category) (X: @obj C) (F: @obj (PresheafCat C)),
  @Isomorphic TypeCat (@arrow (PresheafCat C) F (fobj (YonedaFunctor C) X))
                      (fobj F X).
Proof. intros.
       specialize (YonedaEmbedding C X F); intros YE.
       unfold Isomorphic.
       apply IsoEql.
       exact YE.
Qed.

Lemma YEBijection: forall (C: Category) (X: @obj C) (F: @obj (PresheafCat C)),
  @Bijective (@arrow (PresheafCat C) F (fobj (YonedaFunctor C) X))
             (fobj F X).
Proof. intros.
       specialize (YEIsomorphic C X F); intros (f, I).
       unfold Bijective.
       exists f.
       apply @bijisorT. 
       exact I.
Qed.

Definition phistar (C: Category) (F G: @obj (PresheafCat C)) (phi: NaturalTransformation F G) (X: @obj C):
  @arrow TypeCat (@arrow (PresheafCat C) G (fobj (YonedaFunctor C) X)) (@arrow (PresheafCat C) F (fobj (YonedaFunctor C) X)).
Proof. simpl.
       intros (theta, cc1).
       destruct phi as (phi, cc2).
       simpl in *.
       unshelve econstructor.
       - simpl. intros Y f.
         exact (phi Y (theta Y f)).
       - simpl. intros Y Z f.
         apply functional_extensionality.
         intro h.
         specialize (cc2 Y Z f).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl cc2) as H';
         cbn beta in H'.
         specialize (H' (theta Y h)).
         rewrite H'.
         specialize (cc1 Y Z f).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl cc1) as H'';
         cbn beta in H''.
         specialize (H'' h).
         rewrite H''.
         reflexivity.
Defined.

Definition phistar2 (C: Category) (F: @obj (PresheafCat C)) (X Y: @obj C) (f: arrow X Y):
  @arrow TypeCat (@arrow (PresheafCat C) F (fobj (YonedaFunctor C) Y)) (@arrow (PresheafCat C) F (fobj (YonedaFunctor C) X)).
Proof. simpl.
       intros (theta, cc1).
       simpl in *.
       unshelve econstructor.
       - simpl. intros Z g.
         exact (theta Z (f o g)).
       - simpl. intros Z W g.
         apply functional_extensionality.
         intro h.
         specialize (cc1 Z W g).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl cc1) as H'';
         cbn beta in H''.
         specialize (H'' (f o h)).
         rewrite H''.
         rewrite assoc.
         reflexivity.
Defined.

Lemma YonedaLemma_naturality_in_F (C: Category) (X: @obj C) (F G: @obj (PresheafCat C)) (phi: NaturalTransformation F G):
                (trans phi X) o to (YonedaEmbedding C X F) = to (YonedaEmbedding C X G) o phistar C F G phi X.
Proof. simpl.
       extensionality theta.
       destruct theta as (theta, cct).
       destruct phi as (phi, ccp).
       simpl in *.
       reflexivity.
Qed.

Lemma YonedaLemma_naturality_in_X (C: Category) (X Y: @obj C) (f: arrow X Y) (F: @obj (PresheafCat C)):
                fmap F f o (to (YonedaEmbedding C X F)) = (to (YonedaEmbedding C Y F)) o (phistar2 C F X Y f).
Proof. simpl.
       extensionality theta.
       destruct theta as (theta, cct).
       simpl in *.
       specialize (cct X Y f).
       pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl cct) as H';
       cbn beta in H'.
       specialize (H' (identity X)).
       rewrite H'.
       rewrite f_identity, identity_f.
       reflexivity.
Qed.

Corollary YFFaithfulC: forall (C: Category), Faithful (YonedaFunctor C).
Proof. intro C.
       unshelve econstructor.
       - intros X Y f g Ha.
         specialize (ISOAf _ _ _ (YonedaEmbedding C X ((fobj (YonedaFunctor C) Y)))); intro I.
         assert (forall X Y f, (from (YonedaEmbedding C X ((fobj (YonedaFunctor C) Y))) f) = fmap (YonedaFunctor C) f).
         { simpl.
           intros.
           apply Nt_split.
           simpl.
           extensionality Z.
           extensionality h.
           reflexivity.
         }
         apply bijisorT in I.
         destruct I.
         unfold injective in finj.
         pose proof H as HH.
         specialize (H X Y f).
         specialize (HH X Y g).
         rewrite Ha, <- HH in H.
         specialize (finj f g H).
         rewrite finj.
         reflexivity.
Qed.

Corollary YFFullC: forall (C: Category), Full (YonedaFunctor C).
Proof. intro C.
       unshelve econstructor.
       - intros X Y f g.
         specialize (ISOAf _ _ _ (YonedaEmbedding C X ((fobj (YonedaFunctor C) Y)))); intro I.
         assert (forall X Y f, (from (YonedaEmbedding C X ((fobj (YonedaFunctor C) Y))) f) = fmap (YonedaFunctor C) f).
         { simpl.
           intros.
           apply Nt_split.
           simpl.
           extensionality Z.
           extensionality h.
           reflexivity.
         }
         apply bijisorT in I.
         destruct I.
         unfold surjective in fsurj.
         specialize (fsurj g).
         destruct fsurj as (h, fsurj).
         simpl in h.
         exists h.
         specialize (H X Y h).
         rewrite fsurj in H.
         rewrite H.
         reflexivity.
Qed.

(** not as an implication of the Yoneda Lemma but in a type theoretic way --
    this one is possible due to the way fmap implemented *)
Lemma YFFaithful: forall (C: Category), Faithful (YonedaFunctor C).
Proof. intro C.
       unshelve econstructor.
       - simpl.
         intros X Y f g H.
         apply Nt_split in H.
         simpl in H.
         pose proof (fun x y => eq_ind_r (fun f => f x y = _ x y) eq_refl H) as H';
         cbn beta in H'.
         specialize (H' X (identity X)).
         rewrite !f_identity in H'.
         exact H'.
Qed.

Lemma YFFull: forall (C: Category), Full (YonedaFunctor C).
Proof. intro C.
       unshelve econstructor.
       - simpl.
         intros X Y f (eta, cc).
         simpl in *.
         exists (eta X (identity X)).
         apply Nt_split.
         simpl.
         extensionality Z.
         extensionality g.
         specialize (cc X Z g).
         pose proof (fun x => eq_ind_r (fun f => f x = _ x) eq_refl cc) as H';
         cbn beta in H'.
         specialize (H' (identity X)).
         rewrite identity_f in H'.
         exact H'.
Qed.




























 