From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple Monad Presheaf Yoneda IndexedCategories ComparisonK.
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

Definition TAlgebra {C: Category} {T: Functor C C} (M: Monad C T) (a: @obj C) :=
  { alg_map: arrow a (fobj T a) |
                alg_map o (trans (@eta C T M) a) = (@identity C a) /\ 
                alg_map o (fmap T (alg_map)) = alg_map o (trans (@mu C T M) a) }.


(** eqTA with JMeq *)
Lemma eqTA: ∏
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a      : @obj C)
                  (TA1 TA2: TAlgebra M a), 
                  (proj1_sig TA1) = (proj1_sig TA2) <-> TA1 = TA2.
Proof. split.
       - intros.
         destruct TA1, TA2. cbn in *. subst. f_equal.
         now destruct (proof_irrelevance _ a0 a1).
       - intro H. rewrite H. easy.
Qed.

Lemma eqTAT: ∏
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b     : @obj C),
                  a = b -> TAlgebra M a = TAlgebra M b.
Proof. intros. subst. easy. Defined.

Definition TAlgebraMap {C: Category} {T: Functor C C}{M: Monad C T} {a b: @obj C}
                       (TA1: TAlgebra M a) (TA2: TAlgebra M b) :=
  { tf: @arrow C b a | tf o (proj1_sig TA1) = (proj1_sig TA2) o fmap T tf }.

Definition idTAlg {C: Category} {T: Functor C C} {M: Monad C T} {X: @obj C}
                  (TA: TAlgebra M X): TAlgebraMap TA TA.
Proof. exists (identity X).
       now rewrite preserve_id, f_identity, identity_f.
Defined.

Proposition TAlgebraMapCompose {C: Category} {T: Functor C C}{M: Monad C T} {a b c: @obj C}
                               {TA: TAlgebra M a} {TB: TAlgebra M b} {TC: TAlgebra M c}
                               (Tf: TAlgebraMap TA TB) (Tg: TAlgebraMap TB TC): TAlgebraMap TA TC.
Proof. exists ((proj1_sig Tg) o (proj1_sig Tf)).
       destruct Tf as (f, ccf).
       destruct Tg as (g, ccg). cbn in *.
       now rewrite preserve_comp, <- assoc, ccf, assoc, ccg, assoc.
Defined.

Lemma eqTAM: ∏
                  (C      : Category)
                  (T      : Functor C C)
                  (M      : Monad C T)
                  (a b    : @obj C)
                  (TA1    : TAlgebra M a)
                  (TA2    : TAlgebra M b)
                  (ta1 ta2: TAlgebraMap TA1 TA2),
                  (proj1_sig ta1) = (proj1_sig ta2) <-> ta1 = ta2.
Proof. split.
       - intros. 
         destruct ta1, ta2, TA1, TA2, T, M. cbn in *.
         subst. f_equal.
         destruct (proof_irrelevance _ e e0).
         easy.
       - intros.
         subst.
         easy.
Qed.

Definition EilenbergMooreCategory {C: Category} {T: Functor C C} (M: Monad C T): Category.
Proof. unshelve econstructor.
       - exact {a: @obj C & TAlgebra M a}.
       - intros TB TA. exact (TAlgebraMap (projT2 TA) (projT2 TB)).
       - intros (a, TA). exact (idTAlg TA).
       - intros TA TB TC Tg Tf. exact (TAlgebraMapCompose Tf Tg).
       - repeat intro. now subst.
       - intros. apply eqTAM. cbn. now rewrite assoc.
       - intros. apply eqTAM. cbn in *.
         destruct a as (a, alpha).
         destruct b as (b, beta). cbn in *.
         now rewrite identity_f.
       - intros. apply eqTAM. cbn in *.
         destruct a as (a, alpha).
         destruct b as (b, beta). cbn in *.
         now rewrite f_identity.
Defined.


Lemma EMOeq: forall {C: Category} {T: Functor C C} (M: Monad C T) (a b: @obj (EilenbergMooreCategory M)),
  (projT1 a = projT1 b /\ JMeq (proj1_sig (projT2 a)) (proj1_sig (projT2 b))) <-> a = b.
Proof. split.
       - intros (Ha, Hb).
         simpl in *.
         destruct a, b.
         simpl in *.
         subst.
         f_equal.
         apply JMeq_eq in Hb.
         apply eqTA.
         simpl.
         rewrite Hb.
         reflexivity.
       - intro H. subst. easy.
Qed.

(* Lemma EMMeq: forall {C: Category} {T: Functor C C} (M: Monad C T) (a b: @obj (EilenbergMooreCategory M))
  (f g: arrow b a), JMeq (projT2 a) (projT2 b) -> JMeq f g.
Proof. intros. subst. simpl in *.
       apply JMeq_eq in H. easy. Qed. *)


Definition FT {C: Category} {T: Functor C C} (M: Monad C T)
              (EMC := (EilenbergMooreCategory M)): Functor C EMC.
Proof. unshelve econstructor.
       - intro X.
         exists (fobj T X).
         exists (trans (mu M) X).
         split.
         + now specialize (comm_diagram2_b2 X).
         + now specialize (comm_diagram1 X).
       - intros X Y f. simpl.
         unshelve econstructor.
         + exact (fmap T f).
         + specialize (@comm_diag _ _ _ _ (mu M) _ _ f); intro H.
           cbn in *. now rewrite H.
       - repeat intro. now subst.
       - intro a.
         apply eqTAM. cbn.
         now rewrite !preserve_id.
       - intros a b c g f.
         apply eqTAM. cbn.
         now rewrite !preserve_comp.
Defined.
Check FT.

(** right adjoint functor that acts as G_T *)
Definition GT {C  : Category}{T  : Functor C C}(M  : Monad C T)
              (EMC:= (EilenbergMooreCategory M)): Functor EMC C.
Proof. unshelve econstructor.
       - intro X. exact (projT1 X).
       - intros TA TB Tf. exact (proj1_sig Tf).
       - repeat intro. now subst.
       - intros (X, alpha). easy.
       - intros a b c g f. easy.
Defined.
Check GT.

Theorem mon_emadj: ∏
                   {C  : Category}
                   {T  : Functor C C}
                   (M  : Monad C T), Adjunction (FT M) (GT M).
Proof. intros.
       unshelve econstructor.
       - unshelve econstructor.
         + intro X. exact (trans (eta M) X).
         + intros X Y f.
           specialize (@comm_diag _ _ _ _ (eta M) _ _ f); intro H.
           cbn in H. exact H.
       - unshelve econstructor.
         + intro TA. cbn in TA.
           unshelve econstructor.
           ++ exact (proj1_sig (projT2 TA)).
           ++ destruct TA as (X, (tf, (cc0, cc1))). cbn in *.
              now rewrite <- cc1.
         + intros a b f. destruct a, b, f.
           apply eqTAM. cbn in *.
           easy.
       - intro a.
         apply eqTAM. cbn.
         specialize (@comm_diagram2_b1 _ _ M a); intro H.
         cbn in *. unfold id in *. now rewrite H.
       - intro a. cbn.
         destruct a, t. now cbn in *.
Defined.


