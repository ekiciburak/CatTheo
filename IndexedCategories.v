From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC Functor 
NaturalTransformation Adjunction ParamKleisliTriple Monad Presheaf Yoneda.
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

Definition CategoryInd (I: @obj TypeCat): Category.
Proof. unshelve econstructor.
       - exact (forall i: I,  @obj TypeCat).
       - simpl. intros X Y.
         exact (forall i, X i -> Y i).
       - simpl. intros X i.
         intro a.
         exact a.
       - simpl. intros X Y Z f g i.
         intro z.
         exact (g i (f i z)).
       - repeat intro. now subst.
       - simpl.
         intros X Y Z W f g h.
         easy.
       - simpl. intros X Y f.
         easy.
       - simpl. intros X Y f.
         easy.
Defined.


Definition FunctorInd (I J: @obj TypeCat) (p: @arrow TypeCat J I): 
  Functor (CategoryInd J) (CategoryInd I).
Proof. unshelve econstructor.
       - simpl in *.
         intros f i.
         exact (f (p i)).
       - simpl in *.
         intros a b f i d.
         exact (f (p i) d). 
       - repeat intro. now subst.
       - simpl in *.
         intro a.
         easy.
       - simpl in *.
         intros a b c g f.
         easy.
Defined.

Lemma TypeCatProd: forall A B: @obj TypeCat, Product TypeCat A B (prod A B).
Proof. intros.
       unshelve econstructor.
       - simpl. intros (a, b). exact a.
       - simpl. intros (a, b). exact b.
       - simpl. intros Z f g z. exact (f z, g z).
       - simpl. intros Z f g. easy.
       - simpl. intros Z f g. easy.
       - simpl. intros Z f g p1 H1 H2.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H1) as Hax1';
         cbv beta in Hax1'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H2) as Hax2';
         cbv beta in Hax2'.
(*          pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H3) as Hax3';
         cbv beta in Hax3'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H4) as Hax4';
         cbv beta in Hax4'. *)
         apply functional_extensionality.
         intro z.
         specialize (Hax1' z).
         specialize (Hax2' z).
         destruct (p1 z).
         rewrite <- Hax1', <- Hax2'.
         reflexivity.
Defined.


Lemma TypeCathasProd: hasProducts TypeCat.
Proof. unshelve econstructor.
       - intros a b.
         exact (prod a b).
       - intros. exact (TypeCatProd A B).
Defined.

Definition pi1Ind (I J: @obj TypeCat): 
  Functor (CategoryInd I) (CategoryInd (@pobj TypeCat TypeCathasProd I J)).
Proof. unshelve econstructor.
       - simpl in *.
         intros f (i, j).
         exact (f i).
       - simpl in *.
         intros a b f (i, j) p.
         exact (f i p).
       - repeat intro. now subst.
       - simpl in *.
         intros a.
         apply functional_extensionality_dep.
         intros (i, j).
         easy.
       - simpl in *.
         intros a b c f g.
         apply functional_extensionality_dep.
         intros (i, j).
         easy.
Defined.


Lemma pi1IndLA: forall (I J: @obj TypeCat),
  { G: Functor (CategoryInd (@pobj TypeCat TypeCathasProd I J)) (CategoryInd I) & HomAdjunction (pi1Ind I J) G }.
Proof. intros.
       specialize (UP (CategoryInd I) 
                      (CategoryInd (@pobj TypeCat TypeCathasProd I J))
                      (pi1Ind I J)
                  ); intros H.
       destruct H as (HL, HR).
       apply HL.
       clear HL HR.
       intro E.
       simpl in *.
       unshelve econstructor.
       - intro i.
         exact {j: J & E (i, j)}.
       - simpl.
         unshelve econstructor.
         + intros (i, j) y.
           exists j.
           exact y.
         + simpl in *.
           intros X g.
           unshelve econstructor.
           ++ intros i (j, Hj).
              exact (g (i, j) Hj).
           ++ cbn in *.
              split.
              * apply functional_extensionality_dep.
                intros (i, j).
                easy.
              * intros.
                apply functional_extensionality_dep.
                intro i.
                apply functional_extensionality_dep.
                intros (j, Hj).
                rewrite <- H.
                easy.
Qed.

