From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism 
Terminal Dual Initial Product CoProduct Exponential CCC IPL STLC.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Coq.Lists.List.
Require Import JMeq.
Require Import Coq.Program.Equality.
Set Universe Polymorphism.
Local Open Scope list_scope.

Class Functor (C D: Category): Type :=
  mk_Functor
  {
    fobj            : @obj C -> @obj D;
    fmap            : forall {a b: @obj C} (f: arrow b a), arrow (fobj b) (fobj a);
    fmapP           :> forall x y, Proper (eq ==> eq) (@fmap x y);
    preserve_id     : forall {a: @obj C}, fmap (@identity C a) = (@identity D (fobj a));
    preserve_comp   : forall {a b c: @obj C} (g : @arrow C c b) (f: @arrow C b a),
                        fmap (g o f) = (fmap g) o (fmap f)
  }.
Check Functor.

Notation " C → D " := (Functor C D) (at level 40, left associativity).

Arguments fmap {_} {_} _ _ _ _.
Arguments fobj {_} {_} _ _.

(** sameness of Functors using heterogenous (John Major's) equality *)
Lemma F_split: forall (C D: Category) (F G: Functor C D),
                 fobj F = fobj G -> JMeq (fmap F) (fmap G) -> F = G.
Proof.
    destruct F; destruct G; cbn; intros; subst. f_equal.
    now destruct (proof_irrelevance _ fmapP0 fmapP1).
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.

(** sameness of Functors, inspired by Amin Timany *)
Lemma F_splitA: forall
                (C D  : Category)
                (F G  : Functor C D)
                (ObjEq: (fobj F) = (fobj G)),
                ((fun a b => 
                    match ObjEq in _ = V return ((arrow b a) -> (arrow (V b) (V a))) with
                     | eq_refl => (fmap F a b)
                    end) = fmap G) -> F = G.
Proof.
    destruct F; destruct G; simpl; intros; subst; f_equal.
    now destruct (proof_irrelevance _ fmapP0 fmapP1).
    now destruct (proof_irrelevance _ preserve_id0 preserve_id1).
    now destruct (proof_irrelevance _ preserve_comp0 preserve_comp1).
Defined.

(** sameness of Functors using heterogenous (John Major's) equality *)
Lemma F_splitR: forall (C D: Category) (F G: Functor C D),
                 F = G -> fobj F = fobj G /\ JMeq (fmap F) (fmap G).
Proof. intros. subst. easy. Qed.

Definition Forgetful1: Functor Mon SetCat.
Proof. unshelve econstructor.
       - intros (M, e, Mf, Mob1, Mob2, Mob3).
         exact M.
       - simpl.
         intros (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         intros (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         intros (f, fax1, fax2).
         exact f.
       - simpl. repeat intro. now subst.
       - simpl.
         intros (M, e, Mf, Mob1, Mob2, Mob3).
         simpl. reflexivity.
       - simpl.
         intros (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         intros (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         intros (M3, e3, M3f, M3ob1, M3ob2, M3ob3).
         intros (f, fax1, fax2).
         intros (g, gax1, gax2).
         reflexivity.
Defined.

Definition Forgetful2: Functor PreOrderCat SetCat.
Proof. unshelve econstructor.
       - intros (pos, le, r, t).
         exact pos.
       - intros (pos1, le1, r1, t1) (pos2, le2, r2, t2).
         intros (f, fax).
         simpl in *. exact f.
       - simpl. repeat intro. now subst.
       - intros (pos, le, r, t).
         simpl. reflexivity.
       - intros (pos1, le1, r1, t1) (pos2, le2, r2, t2) (pos3, le3, r3, t3) (f, fax) (g, gax).
         simpl. reflexivity.
Defined.

Definition FreeMonoidPar (A: Set): Monoid.
Proof. unshelve econstructor.
       - exact (list A).
       - exact nil.
       - intros xs ys. exact (xs ++ ys).
       - intros. simpl. rewrite app_assoc. reflexivity.
       - simpl. intro xs. reflexivity.
       - simpl. intro xs. rewrite app_nil_r. reflexivity.
Defined.

Definition FreeMonoidFunctor: Functor SetCat Mon.
Proof. unshelve econstructor.
       - intro A. simpl in *.
         exact (FreeMonoidPar A).
       - simpl. intros A B f.
         unshelve econstructor.
         + simpl. intro l. 
           exact (map f l).
         + simpl. reflexivity.
         + simpl. intros x y.
           rewrite map_app.
           reflexivity.
       - simpl. repeat intro. now subst.
       - simpl. intro A.
         apply MonoidMapEq.
         simpl.
         apply functional_extensionality.
         intro l.
         rewrite map_id.
         reflexivity.
       - simpl. intros A B C g f.
         apply MonoidMapEq.
         simpl.
         apply functional_extensionality.
         intro l.
         rewrite map_map.
         reflexivity.
Defined.

Definition Compose_Functors (C D E: Category) 
                            (F    : Functor C D) 
                            (G    : Functor D E): (Functor C E).
Proof. unshelve econstructor.
       - exact (fun a => fobj G (fobj F a)).
       - intros. exact ((((@fmap D E G _ _
                               (@fmap C D F a b f))))).
       - repeat intro. subst. easy.
       - intros. simpl.  
         now rewrite (@preserve_id C D F), (@preserve_id D E G).
       - intros. simpl.
         now rewrite (@preserve_comp C D F), (@preserve_comp D E G).
Defined.

Arguments Compose_Functors {_} {_} {_} _ _.

Definition IdFunctor {C: Category}: Functor C C.
Proof. unshelve econstructor.
       - exact id.
       - unfold id. intros. exact f.
       - repeat intro. easy.
       - intros. now destruct C.
       - intros. now destruct C.
Defined.

Definition Id {C: Category}: @Functor C C.
Proof. refine (@mk_Functor C C id (fun a b f => f) _ _ _);
       intros; now unfold id.
Defined.


Definition iProdFunctor: forall (C: Category) (X: @obj C) (hp: hasProducts C), Functor C C.
Proof. intros C X hp.
       unshelve econstructor.
       - intro A.
         exact (@pobj C hp A X).
       - simpl. intros A B f.
         exact (@fprod C hp A X B X f (identity X)).
       - repeat intro. now subst.
       - simpl. intro A.
         unfold fprod. simpl.
         rewrite !identity_f.
         unfold prod_f.
         destruct (hasp A X).
         simpl.
         specialize (prod_f_uni (pobj A X) pi1 pi2 (identity (pobj A X))).
         apply prod_f_uni.
         + rewrite f_identity. reflexivity.

         + rewrite f_identity. reflexivity.
       - simpl. intros a b c g f.
         specialize (@fprod_distr C hp b c X X a X g (identity X) f (identity X)); intro H.
         destruct hp as (pobj, hasp).
         rewrite f_identity in H.
         rewrite <- H. reflexivity.
Defined.

Definition iExpFunctor: forall (C: Category) (X: @obj C) (hp: hasProducts C) (he: hasExponentials C hp), Functor C C.
Proof. intros C X hp he.
       unshelve econstructor.
       - intro A.
         destruct hp as (pobj, hasp).
         destruct he as (eobj, hase).
         exact (eobj X A).
       - simpl. intros A B f.
         specialize (@fExp C hp he A B X f); intro fX.
         destruct he as (eobj, hase).
(*       specialize (@Exponential.app C hp X A (eobj X A) (hase X A)); intro app.
         specialize (@Exponential.cur C hp X B (eobj X B) (hase X B) (eobj X A) ); intro fx. *)
         destruct hp as (pobj, hasp).
         simpl in *.
         exact fX.
       - simpl. repeat intro. now subst.
       - simpl. intro A.
         destruct hp as (pobj, hasp).
         destruct he as (eobj, hase).
         unfold fExp.
         simpl. rewrite identity_f.
         destruct ( hase X A ).
         simpl in *.
         specialize (curuni (eobj X A) app (identity (eobj X A))).
         rewrite curuni.
         + reflexivity.
         + rewrite fprod_id, f_identity. reflexivity.
       - simpl. intros a b c g f.
         specialize (@fExpDistributes C hp he a b c X f g); intro H.
         destruct hp as (pobj, hasp).
         destruct he as (eobj, hase).
         destruct ( hase X c ).
         destruct ( hase X b ).
         destruct ( hase X a ).
         simpl in *.
         exact H.
Defined.

Definition ContravariantFunctor (C D: Category) := Functor (DualCategory C) D.

Definition iExpContravariantFunctor: forall (C: Category) (X: @obj C) (hp: hasProducts C) (he: hasExponentials C hp), ContravariantFunctor C C.
Proof. intros C X hp he.
       unshelve econstructor.
       - intro A.
         destruct hp as (pobj, hasp).
         destruct he as (eobj, hase).
         exact (eobj A X).
       - simpl. intros A B f.
         specialize (@Expf C hp he B A X f); intro fX.
         destruct he as (eobj, hase).
(*       specialize (@Exponential.app C hp X A (eobj X A) (hase X A)); intro app.
         specialize (@Exponential.cur C hp X B (eobj X B) (hase X B) (eobj X A) ); intro fx. *)
         destruct hp as (pobj, hasp).
         simpl in *.
         exact fX.
       - simpl. repeat intro. now subst.
       - simpl. unfold Expf, fprod. intro A.
         specialize (prod_f_id C (eobj A X) A  (pobj (eobj A X) A) (hasp (eobj A X) A) ); intro h.
         destruct hp as (pobj, hasp).
         destruct he as (eobj, hase).
         simpl in *.
         destruct ( hase A X ).
         simpl in *.
         destruct ( hasp (eobj A X) A ).
         simpl in *.
         specialize (curuni (eobj A X) (app o prod_f (pobj (eobj A X) A) (identity (eobj A X) o pi1) (identity A o pi2)) 
                                       (identity (eobj A X))).
         rewrite curuni.
         + reflexivity.
         + rewrite fprod_id, f_identity, !identity_f.
           unfold fprod in curcomm.
           simpl in *.
           rewrite h, f_identity. reflexivity.
       - simpl. intros a b c g f.
         specialize (@ExpfDistributes C hp he c b a X g f); intro H.
         destruct hp as (pobj, hasp).
         destruct he as (eobj, hase).
         destruct ( hase X c ).
         destruct ( hase X b ).
         destruct ( hase X a ).
         simpl in *.
         exact H.
Defined.

Module ME.

Context (S: @obj SetCat).

Definition FunctorF: Functor SetCat SetCat.
Proof. specialize (hasProductsSetCat); intros (pobj, H).
       unshelve econstructor.
       - simpl. intro X.
         exact (prod S X).
       - simpl. intros X Y f.
         exact (@fprod SetCat hasProductsSetCat _ _ _ _ (identity S) f); intro h.
       - repeat intro. now subst.
       - simpl. intros X.
         unfold fprod.
         simpl.
         apply functional_extensionality.
         intros (s, x).
         reflexivity.
       - simpl. intros X Y Z g f.
         unfold fprod.
         simpl.
         apply functional_extensionality.
         intros (s, x).
         reflexivity.
Defined.

Definition FunctorG: Functor SetCat SetCat.
Proof. specialize (hasProductsSetCat); intros (pobj, H).
       unshelve econstructor.
       - simpl. intro X.
         exact (prod X S).
       - simpl. intros X Y f.
         exact (@fprod SetCat hasProductsSetCat _ _ _ _ f (identity S)); intro h.
       - repeat intro. now subst.
       - simpl. intros X.
         unfold fprod.
         simpl.
         apply functional_extensionality.
         intros (x, s).
         reflexivity.
       - simpl. intros X Y Z g f.
         unfold fprod.
         simpl.
         apply functional_extensionality.
         intros (x, s).
         reflexivity.
Defined.

Lemma IsoFXGX: forall (X: @obj SetCat), @Isomorphic SetCat (@fobj SetCat SetCat FunctorF X) (@fobj SetCat SetCat FunctorG X).
Proof. intro X.
       unshelve econstructor.
       - simpl. intros (s, x).
         exact (x, s).
       - unshelve econstructor.
         + simpl. intros (x, s).
           exact (s, x).
         + simpl. apply functional_extensionality.
           intros (x, s).
           reflexivity.
         + simpl. apply functional_extensionality.
           intros (s, x).
           reflexivity.
Qed.

End ME.

(** Associativity of functor composition *)
Lemma FunctorCompositionAssoc: forall {D C B A : Category} 
  (F : Functor C D) (G : Functor B C) (H : Functor A B),
  Compose_Functors H (Compose_Functors G F) = Compose_Functors (Compose_Functors H G) F.
Proof. intros.
       apply F_split.
       - easy.
       - apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
         eq_existT_uncurried; cbn.
         now exists (eq_refl 
         (forall a b : obj, arrow b a ->
           arrow (fobj F (fobj G (fobj H b))) (fobj F (fobj G (fobj H a))))).
Defined.

(** Identity functors cancels on the right *)
Lemma ComposeIdr: forall {C D: Category} (F: Functor C D),
  Compose_Functors F IdFunctor = F.
Proof. intros.
       apply F_split.
       - easy.
       - apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
         eq_existT_uncurried; cbn.
       unfold id in *.
       now exists (eq_refl 
       (forall a b : obj, arrow b a -> arrow (fobj F b) (fobj F a))).
Defined.

(** Identity functors cancels on the left *)
Lemma ComposeIdl: forall {C D: Category} (F: Functor C D),
  Compose_Functors IdFunctor F = F.
Proof. intros.
       apply F_split.
       - easy.
       - apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
         eq_existT_uncurried; cbn.
       unfold id in *.
       now exists (eq_refl 
       (forall a b : obj, arrow b a -> arrow (fobj F b) (fobj F a))).
Defined.

(** the 2-category Cat *)
Definition Cat: Category.
Proof. unshelve econstructor.
       - exact Category.
       - intros C D. exact (Functor D C).
       - intro C. cbn in *. exact (@IdFunctor C).
       - intros C D E F G. exact (Compose_Functors G F).
       - repeat intro. now subst.
       - intros A B C D F G H. cbn in *.
         symmetry. 
         exact (FunctorCompositionAssoc H G F).
       - intros C D F. exact (ComposeIdr F).
       - intros D C F. exact (ComposeIdl F).
Defined.

Definition sObjSetCat: @obj SetCat.
Proof. simpl. exact unit. Defined.

Definition sArrowSetCat: @arrow SetCat sObjSetCat sObjSetCat.
Proof. simpl. intro a. exact a. Defined.

Lemma SingletonCat: Category.
Proof. unshelve econstructor.
       - exact unit.
       - intros a b. exact unit.
       - simpl. intros. exact tt.
       - simpl. intros. exact tt.
       - repeat intro. now subst.
       - simpl. intros. reflexivity.
       - simpl. intros. destruct f. reflexivity.
       - simpl. intros. destruct f. reflexivity.
Defined.

Lemma hasTerminalCat: hasTerminal Cat.
Proof. unshelve econstructor.
       - simpl. exact SingletonCat.
       - unshelve econstructor.
         + simpl. intro C.
           unshelve econstructor.
           ++ simpl. intro a.
              exact tt.
           ++ simpl. intros. exact tt.
           ++ simpl. repeat intro. now subst.
           ++ simpl. intros. reflexivity.
           ++ simpl. intros. reflexivity. 
         + simpl. intro C.
           intros F G.
           apply F_split.
           ++ destruct F, G. simpl in *.
              extensionality x.
              destruct (fobj0 x), (fobj1 x).
              reflexivity.
           ++ destruct F, G. simpl in *.
              apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
              eq_existT_uncurried; cbn.
              exists eq_refl.
              simpl.
              extensionality a.
              extensionality b.
              extensionality f.
              destruct (fmap0 a b f), (fmap1 a b f).
              reflexivity.
Qed.

Definition ProductCategory (C D: Category): Category.
Proof. unshelve econstructor.
         + simpl in *. exact (@obj C * @obj D)%type.
         + simpl. intros (x, y) (x', y').
           exact ((@arrow C x x') * (@arrow D y y'))%type.
         + simpl. intros (x, y).
           exact ((identity x), (identity y)).
         + simpl. intros (a, b) (c, d) (i, j) (f1, f2) (g1, g2).
           split.
           ++ exact (f1 o g1).
           ++ exact (f2 o g2).
         + simpl. repeat intro. now subst.
         + simpl. intros (a, b) (c, d) (i, j) (f1, f2) (g1, g2) (h1, h2) (k1, k2).
           f_equal.
           ++ rewrite assoc. reflexivity.
           ++ rewrite assoc. reflexivity.
         + simpl. intros (a, b) (c, d) (f, g).
           f_equal.
           ++ rewrite identity_f. reflexivity.
           ++ rewrite identity_f. reflexivity.
         + simpl. intros (a, b) (c, d) (f, g).
           f_equal.
           ++ rewrite f_identity. reflexivity.
           ++ rewrite f_identity. reflexivity.
Defined.

Definition ProductFunctor {A B C D: Category} (F: Functor A B) (G: Functor C D):
 Functor (ProductCategory A C) (ProductCategory B D).
Proof. unshelve econstructor.
       - intros (a, c).
         exact (fobj F a, fobj G c).
       - intros (a, c) (b, d) (f, g).
         exact (fmap F a b f, fmap G c d g).
       - repeat intro. now subst.
       - intros (a, c). simpl.
         rewrite !preserve_id.
         reflexivity.
       - simpl. intros (a, d) (b, e) (c, f) (g1, g2) (f1, f2).
         rewrite !preserve_comp.
         reflexivity.
Defined.

Lemma Fpi1 (A B: Category): Functor (ProductCategory A B) A.
Proof. unshelve econstructor. 
            +++ intros (a, b). exact a.
            +++ intros (a, b) (c, d) (f, g). exact f.
            +++ repeat intro. now subst.
            +++ intros (a, b). reflexivity.
            +++ intros (a, b) (c, d) (i, j) (f1, f2) (g1, g2).
                reflexivity.
Defined.

Lemma Fpi2 (A B: Category): Functor (ProductCategory A B) B.
Proof.   unshelve econstructor. 
            +++ intros (a, b). exact b.
            +++ intros (a, b) (c, d) (f, g). exact g.
            +++ repeat intro. now subst.
            +++ intros (a, b). reflexivity.
            +++ intros (a, b) (c, d) (i, j) (f1, f2) (g1, g2).
                reflexivity.
Defined.

Definition DualFunctor {C D: Category} (F: Functor C D): Functor (DualCategory C) (DualCategory D).
Proof. unshelve econstructor.
       - intro a. exact (fobj F a).
       - intros a b f. simpl.
         exact (fmap F _ _ f).
       - repeat intro. now subst.
       - intros. simpl.
         now rewrite preserve_id.
       - intros. simpl.
         now rewrite preserve_comp.
Defined.

Class Full {C D: Category} (F : Functor C D): Type := 
{
  fmap_surj: forall {x y} (f g: arrow (fobj F y) (fobj F x)), 
    exists (f: arrow y x), fmap F _ _ f = g
}.

Class Faithful {C D: Category} (F : Functor C D): Type := 
{
  fmap_inj: forall {x y} (f g: arrow y x), fmap F _ _ f = fmap F _ _ g -> f = g
}.

Lemma PC1 (A B C: Category) (F: Functor C A) (G: Functor C B): Functor C (ProductCategory A B).
Proof.      destruct A, B, C, F, G.
            unshelve econstructor.
            +++ simpl in *.
                intro a.
                exact ((fobj0 a), (fobj1 a)).
            +++ simpl in *.
                intros a b f.
                exact ((fmap0 a b f), (fmap1 a b f)).
            +++ repeat intro. now subst.
            +++ simpl in *.
                intro a.
                rewrite preserve_id0, preserve_id1.
                reflexivity.
            +++ simpl in *. intros a b c f g.
                rewrite preserve_comp0, preserve_comp1.
                reflexivity.
Defined.

Definition pco (A B: Category) (a: @obj A) (b: @obj B): @obj (ProductCategory A B).
Proof. exact (a, b). Defined.

Definition pca (A B: Category) (a b: @obj A) (c d: @obj B) (f: arrow b a) (g: arrow d c): @arrow (ProductCategory A B) (b, d) (a, c).
Proof. exact (f, g). Defined.

Lemma Afst: forall (A B: Category) (a b: @obj A) (c d: @obj B) (f h: arrow b a) (g: arrow d c),
  fmap (Fpi1 A B) (a, c) (b, d) (f, g) = fmap (Fpi1 A B) (a, c) (b, d) (h, g) -> f = h.
Proof. unfold Fpi1.
       intros.
       simpl in H.
       easy.
Defined.

Lemma Fpi1_id: forall (A B: Category) (a b: @obj A) (c d: @obj B) (f h: arrow b a) (g: arrow d c),
  fmap (Fpi1 A B) (a, c) (b, d) (f, g) = f.
Proof. unfold Fpi1.
       intros.
       simpl.
       easy.
Defined.

Lemma fst_snd: forall (A B: Category) (a b: @obj A) (c d: @obj B)  (f h: @arrow (ProductCategory A B) (b, d) (a, c)),
  fmap (Fpi1 A B) (a, c) (b, d) f = fmap (Fpi1 A B) (a, c) (b, d) h ->
  fmap (Fpi2 A B) (a, c) (b, d) f = fmap (Fpi2 A B) (a, c) (b, d) h -> f = h.
Proof. unfold Fpi1, Fpi2.
       intros.
       simpl in *.
       simpl in H, H0.
       destruct f.
       destruct h.
       subst.
       easy.
Defined.

Arguments fmap {_} {_} _ {_} {_} _.
Lemma hasProductsCat: hasProducts Cat.
Proof. unshelve econstructor.
       - simpl. intros C D.
         exact (ProductCategory C D).
       - simpl. intros.
         unshelve econstructor.
         ++ simpl.
            exact (Fpi1 A B).
         ++ simpl.
            exact (Fpi2 A B).
         ++ simpl. intros C F G.
            exact (PC1 A B C F G).
         ++ simpl. intros C F G.
            destruct A, B, C, F, G.
            simpl in *.
            apply F_split.
            +++ simpl. reflexivity.
            +++ apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
                eq_existT_uncurried; cbn.
                exists eq_refl.
                simpl.
                reflexivity.
         ++ simpl. intros C F G.
            destruct A, B, C, F, G.
            apply F_split.
            +++ simpl. reflexivity.
            +++ apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, 
                eq_existT_uncurried; cbn.
                exists eq_refl.
                simpl. reflexivity.
         ++ simpl. intros C F G H K L.
Admitted.




