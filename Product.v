From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual Initial.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

Set Universe Polymorphism.

(** Binary Products *)

Class Product (C: Category) (A B prod: @obj C): Type :=
{
  pi1       : @arrow C A prod;
  pi2       : @arrow C B prod;  
  prod_f    : forall (Z: @obj C) (f: @arrow C A Z) (g: @arrow C B Z), @arrow C prod Z;
  prod_f_c1 : forall (Z: @obj C) (f: @arrow C A Z) (g: @arrow C B Z), f = pi1 o prod_f Z f g;
  prod_f_c2 : forall (Z: @obj C) (f: @arrow C A Z) (g: @arrow C B Z), g = pi2 o prod_f Z f g;
  prod_f_uni: forall (Z: @obj C) (f: @arrow C A Z) (g: @arrow C B Z) (p: @arrow C prod Z),
              f = pi1 o p -> g = pi2 o p-> (prod_f Z f g) = p
}.

Lemma prod_f_id: forall (C: Category) (A B AxB: @obj C) (p: Product C A B AxB) ,
  @prod_f C A B AxB p AxB (@pi1 C A B AxB p) (@pi2 C A B AxB p) = identity (AxB).
Proof. intros C A B AxB (pi1, pi2, prod, ob1, ob2, ob3).
       simpl in *.
       specialize (ob3 AxB pi1 pi2 (identity AxB)).
       apply ob3.
       - rewrite f_identity. reflexivity.
       - rewrite f_identity. reflexivity.
Qed.

Class hasProducts (C: Category): Type :=
{
  pobj: forall (A B: @obj C), @obj C;
  hasp: forall (A B: @obj C), Product C A B (pobj A B) 
}.

Lemma prod_assoc_iso: forall (C: Category) (hp: hasProducts C) (X Y Z: @obj C),
  Isomorphic (@pobj C hp X (@pobj C hp Y Z)) (@pobj C hp (@pobj C hp X Y) Z).
Proof. intros C (pobj, hasp) X Y Z.
       simpl in *.
       destruct (hasp (pobj X Y) Z) as (pi1, pi2, p, f, g, uniqp).
       destruct (hasp X (pobj Y Z)) as (pi3, pi4, q, h, i, uniqq).
       unshelve econstructor.
       - apply p.
         + destruct (hasp X Y) as (pi5, pi6, r, l, m, uniqr).
           destruct (hasp Y Z) as (pi7, pi8, k, u, v, uniqk).
           apply r.
           ++ exact (pi3).
           ++ exact (pi7 o pi4). 
         + destruct (hasp Y Z) as (pi7, pi8, k, u, v, uniqk).
           exact (pi8 o pi4).
       - unshelve econstructor.
         + apply q.
           ++ destruct (hasp X Y) as (pi5, pi6, r, l, m, uniqr).
              exact (pi5 o pi1).
           ++ destruct (hasp X Y) as (pi5, pi6, r, l, m, uniqr).
              destruct (hasp Y Z) as (pi7, pi8, k, u, v, uniqk).
              apply k.
              * exact (pi6 o pi1).
              * exact pi2.
         + simpl.
           destruct (hasp X Y) as (pi5, pi6, r, l, m, uniqr).
           destruct (hasp Y Z) as (pi7, pi8, k, u, v, uniqk).
           simpl in *.
           pose proof uniqp as uuniqp.
           specialize (uniqp (pobj (pobj X Y) Z) pi1 pi2 
                             (p (pobj X (pobj Y Z)) (r (pobj X (pobj Y Z)) pi3 (pi7 o pi4)) (pi8 o pi4)
                              o q (pobj (pobj X Y) Z) (pi5 o pi1) (k (pobj (pobj X Y) Z) (pi6 o pi1) pi2))).
           specialize (uuniqp (pobj (pobj X Y) Z) pi1 pi2 (identity (pobj (pobj X Y) Z))).
           rewrite <- uniqp, uuniqp.
           reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite assoc.
             rewrite <- f.
             pose proof uniqr as uuniqr.
             specialize (uniqr (pobj (pobj X Y) Z) (pi5 o pi1) (pi6 o pi1)
               (r (pobj X (pobj Y Z)) pi3 (pi7 o pi4) o q (pobj (pobj X Y) Z) 
               (pi5 o pi1) (k (pobj (pobj X Y) Z) (pi6 o pi1) pi2)) ).
             specialize (uuniqr (pobj (pobj X Y) Z)  (pi5 o pi1) (pi6 o pi1) pi1 ).
             rewrite <- uniqr, uuniqr.
             reflexivity.
             ** reflexivity.
             ** reflexivity.
             ** rewrite assoc.
                rewrite <- l.
                rewrite <- h.
                reflexivity.
             ** rewrite assoc.
                rewrite <- m.
                rewrite <- assoc.
                rewrite <- i.
                rewrite <- u.
                reflexivity.
           * rewrite assoc.
             rewrite <- g.
             rewrite <- assoc.
             rewrite <- i.
             rewrite <- v.
             reflexivity.
         + destruct (hasp X Y) as (pi5, pi6, r, l, m, uniqr).
           destruct (hasp Y Z) as (pi7, pi8, k, u, v, uniqk).
           simpl in *.
           pose proof uniqq as uuniqq.
           specialize (uniqq (pobj X (pobj Y Z)) pi3 pi4
              (q (pobj (pobj X Y) Z) (pi5 o pi1) (k (pobj (pobj X Y) Z) (pi6 o pi1) pi2)
               o p (pobj X (pobj Y Z)) (r (pobj X (pobj Y Z)) pi3 (pi7 o pi4)) (pi8 o pi4))).
           specialize (uuniqq (pobj X (pobj Y Z)) pi3 pi4 (identity (pobj X (pobj Y Z)))).
           rewrite <- uniqq, uuniqq.
           reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite assoc.
             rewrite <- h.
             rewrite <- assoc.
             rewrite <- f.
             rewrite <- l.
             reflexivity.
           * rewrite assoc.
             rewrite <- i.
             pose proof uniqk as uuniqk.
             specialize (uniqk (pobj X (pobj Y Z)) (pi7 o pi4) (pi8 o pi4)
               (k (pobj (pobj X Y) Z) (pi6 o pi1) pi2 o p (pobj X (pobj Y Z))
               (r (pobj X (pobj Y Z)) pi3 (pi7 o pi4)) (pi8 o pi4))).
             specialize (uuniqk (pobj X (pobj Y Z)) (pi7 o pi4) (pi8 o pi4) pi4).
             rewrite <- uniqk, uuniqk.
             reflexivity.
             ** reflexivity.
             ** reflexivity.
             ** rewrite assoc.
                rewrite <- u.
                rewrite <- assoc.
                rewrite <- f.
                rewrite <- m.
                reflexivity.
             ** rewrite assoc.
                rewrite <- v.
                rewrite <- g.
                reflexivity.
Qed.

Lemma prod_comm_iso: forall (C: Category) (hp: hasProducts C) (X Y: @obj C),
  Isomorphic (@pobj C hp X Y) (@pobj C hp Y X).
Proof. intros C (pobj, hasp) X Y .
       simpl in *.
       destruct (hasp X Y) as (pi1, pi2, p, pax1, pax2, uniqp).
       destruct (hasp Y X) as (pi3, pi4, q, qax1, qax2, uniqq).
       unshelve econstructor.
       - exact (q (pobj X Y) pi2 pi1).
       - unshelve econstructor.
         + exact (p (pobj Y X) pi4 pi3).
         + pose proof uniqq as uuniqq.
           specialize (uniqq (pobj Y X) pi3 pi4 (q (pobj X Y) pi2 pi1 o p (pobj Y X) pi4 pi3)).
           specialize (uuniqq (pobj Y X) pi3 pi4 (identity (pobj Y X))).
           rewrite <- uniqq, uuniqq.
           reflexivity.
           * rewrite f_identity. 
             reflexivity.
           * rewrite f_identity. 
             reflexivity.
           * rewrite assoc.
             rewrite <- (qax1 _ pi2 pi1).
             rewrite <- (pax2 _ pi4 pi3).
             reflexivity.
           * rewrite assoc.
             rewrite <- (qax2 _ pi2 pi1).
             rewrite <- (pax1 _ pi4 pi3).
             reflexivity.
         + pose proof uniqp as uuniqp.
           specialize (uniqp (pobj X Y) pi1 pi2 (p (pobj Y X) pi4 pi3 o q (pobj X Y) pi2 pi1)).
           specialize (uuniqp (pobj X Y) pi1 pi2 (identity (pobj X Y))).
           rewrite <- uniqp, uuniqp.
           reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite assoc.
             rewrite <- (pax1 _ pi4 pi3).
             rewrite <- (qax2 _ pi2 pi1).
             reflexivity.
           * rewrite assoc.
             rewrite <- (pax2 _ pi4 pi3).
             rewrite <- (qax1 _ pi2 pi1).
             reflexivity.
Qed.

Lemma prod_term_iso_l: forall (C: Category) (hp: hasProducts C) (ht: hasTerminal C) (X: @obj C),
  Isomorphic (@pobj C hp X (@tobj C ht)) X.
Proof. intros C (pobj, hasp) (tobj, (f, funiq)) X.
       simpl in *.
       destruct (hasp X tobj) as (pi1, pi2, p, pax1, pax2, uniqp).
       unshelve econstructor.
       - exact pi1.
       - unshelve econstructor.
         + exact (p X (identity X) (f X)).
         + rewrite <- (pax1 _ (identity X) (f X)).
           reflexivity.
         + pose proof uniqp as uuniqp.
           specialize (uniqp (pobj X tobj) pi1 pi2 (p X (identity X) (f X) o pi1)).
           specialize (uuniqp (pobj X tobj) pi1 pi2 (identity (pobj X tobj))).
           rewrite <- uniqp, uuniqp.
           reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite assoc.
             rewrite <- (pax1 _ (identity X) (f X)).
             rewrite identity_f.
             reflexivity.
           * rewrite assoc.
             rewrite <- (pax2 _ (identity X) (f X)).
             apply funiq.
Qed.

Lemma prod_term_iso_r: forall (C: Category) (hp: hasProducts C) (ht: hasTerminal C) (X: @obj C),
  Isomorphic (@pobj C hp (@tobj C ht) X) X.
Proof. intros C (pobj, hasp) (tobj, (f, funiq)) X.
       simpl in *.
       specialize (prod_comm_iso C); intro I.
       
       destruct (hasp tobj X) as (pi1, pi2, p, pax1, pax2, uniqp).
       unshelve econstructor.
       - exact pi2.
       - unshelve econstructor.
         + exact (p X (f X) (identity X)).
         + rewrite <- (pax2 _ (f X) (identity X)).
           reflexivity.
         + pose proof uniqp as uuniqp.
           specialize (uniqp (pobj tobj X) pi1 pi2 (p X (f X) (identity X) o pi2 )).
           specialize (uuniqp (pobj tobj X) pi1 pi2 (identity (pobj tobj X))).
           rewrite <- uniqp, uuniqp.
           reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite f_identity.
             reflexivity.
           * rewrite assoc.
             rewrite <- (pax1 _ (f X) (identity X)).
             apply funiq.
           * rewrite assoc.
             rewrite <- (pax2 _ (f X) (identity X)).
             rewrite identity_f.
             reflexivity.
Qed.

Class PCatObj (C: Category) (A B: @obj C) : Type :=
{
   Zob: @obj C;
   Zob_ax: (@arrow C A Zob * @arrow C B Zob)%type
}.

Require Import JMeq.

Lemma PCatObjEq (C: Category) (A B: @obj C) (x y: PCatObj C A B):
  @Zob C A B x = @Zob C A B  y ->
  JMeq (fst (@Zob_ax C A B x)) (fst (@Zob_ax C A B y)) ->
  JMeq (snd (@Zob_ax C A B x)) (snd (@Zob_ax C A B y)) -> x = y.
Proof. destruct x as (Z1, (f1, g1)).
       destruct y as (Z2, (f2, g2)).
       simpl.
       intros H1 H2 H3.
       subst. easy.
Qed.

Class PCatArrow (C: Category) (A B: @obj C) (x y: PCatObj C A B) : Type :=
{
   fgarr    : @arrow C (@Zob C A B y) (@Zob C A B x);
   fgarr_ax1: fst (@Zob_ax C A B x) = fst (@Zob_ax C A B y) o fgarr;
   fgarr_ax2: snd (@Zob_ax C A B x) = snd (@Zob_ax C A B y) o fgarr;
}.

Lemma PCatArrowEq (C: Category) (A B: @obj C) (x y: PCatObj C A B) (f g: PCatArrow C A B x y):
 @fgarr C A B x y f = @fgarr C A B x y g -> f = g.
Proof. destruct x as (Z1, (f1, g1)).
       destruct y as (Z2, (f2, g2)).
       destruct f as (f, fax1, fax2).
       destruct g as (g, gax1, gax2).
       simpl in *. intro H.
       subst.
       f_equal.
       specialize (UIP_refl _ _ gax1); intros. rewrite H. reflexivity.
       specialize (UIP_refl _ _ gax2); intros. rewrite H. reflexivity.
Qed.

Definition PCat (C: Category) (A B: @obj C): Category.
Proof. unshelve econstructor.
       - exact (PCatObj C A B).
       - intros f g. exact (PCatArrow C A B g f).
       - intros (Z, (f1, g1)). simpl in *.
         unshelve econstructor.
         + simpl. exact (@identity C Z).
         + simpl. rewrite !f_identity. reflexivity.
         + simpl. rewrite !f_identity. reflexivity.
       - intros (Z1, (f1, g1)) (Z2, (f2, g2)) (Z3, (f3, g3))
         (h1, h1eq1, h1eq2) (h2, h2eq1, h2eq2).
         unshelve econstructor.
         + exact (h1 o h2).
         + simpl in *. rewrite assoc.
           rewrite <- h1eq1, <- h2eq1. reflexivity.
         + simpl in *. rewrite assoc. rewrite <- h1eq2, <- h2eq2. reflexivity.
       - repeat intro. now subst.
       - intros a b c d F G H. apply PCatArrowEq.
         destruct a as (Z1, (f1, g1)).
         destruct b as (Z2, (f2, g2)).
         destruct c as (Z3, (f3, g3)).
         destruct d as (Z4, (f4, g4)).
         destruct F as (h1, h1eq1, h1eq2).
         destruct G as (h2, h2eq1, h2eq2). 
         destruct H as (h3, h3eq1, h3eq2).
         simpl. rewrite assoc. reflexivity.
       - intros a b F. apply PCatArrowEq.
         destruct a as (Z1, (f1, g1)).
         destruct b as (Z2, (f2, g2)).
         destruct F as (h1, h1eq1, h1eq2).
         simpl. rewrite identity_f. reflexivity.
       - intros a b F. apply PCatArrowEq.
         destruct a as (Z1, (f1, g1)).
         destruct b as (Z2, (f2, g2)).
         destruct F as (h1, h1eq1, h1eq2).
         simpl. rewrite f_identity. reflexivity.
Defined.

Definition terminalPCatObj (C: Category) (A B AxB: @obj C) (p: Product C A B AxB): PCatObj C A B.
Proof. destruct p as (pi1, pi2, h, hax1, hax2, huni).
       unshelve econstructor.
       - exact AxB.
       - exact (pi1, pi2).
Defined.

Definition tPCatObj (C: Category) (A B AxB: @obj C) (p: Product C A B AxB): Terminal (PCat C A B) (terminalPCatObj C A B AxB p).
Proof. destruct p as (pi1, pi2, h, hax1, hax2, huni).
       unshelve econstructor.
       - simpl.
         intros (Z, (f, g)).
         unshelve econstructor.
         + simpl. exact (h Z f g).
         + simpl. apply hax1.
         + simpl. apply hax2.
       - simpl.
         intros (Z1, (f1, g1)) (f3, f3ax1, f3ax2) (f4, fax1, f4ax2).
         simpl in *. apply PCatArrowEq. simpl.
         pose proof huni as hhuni.
         specialize (@huni Z1 f1 g1 f4).
         specialize (@hhuni Z1 f1 g1 f3).
         rewrite <- huni, <- hhuni; easy.
Defined.

Lemma productIso0: forall (C: Category) (A B P P': @obj C) (p: Product C A B P), @Isomorphic C P P' -> Product C A B P'.
Proof. intros C A B P P' (pi1, pi2, p, pax1, pax2, puniq) (h, (hinv, hax1, hax2)).
       unshelve econstructor.
       - exact (pi1 o hinv).
       - exact (pi2 o hinv).
       - intros X f g.
         exact (h o (p X f g)).
       - intros X f g. simpl. rewrite assoc. setoid_rewrite <- assoc at 2.
         rewrite hax2, f_identity. apply pax1.
       - intros X f g. simpl. rewrite assoc. setoid_rewrite <- assoc at 2.
         rewrite hax2, f_identity. apply pax2.
       - intros X f g p1 Ha Hb.
         rewrite <- assoc in Ha.
         rewrite <- assoc in Hb.
         simpl.
         specialize (puniq X f g (hinv o p1) Ha Hb).
         assert (HH: h o p X f g = h o hinv o p1).
         rewrite <- !assoc, puniq. reflexivity.
         rewrite hax1, !identity_f in HH.
         exact HH.
Qed. 

Lemma ProductIso: forall (C: Category) (A B P P': @obj C) (p: Product C A B P) (p': Product C A B P'), @Isomorphic C P P'.
Proof. intros C A B P P' (pi11, pi12, h1, h1ax1, h1ax2, h1uniq) (pi21, pi22, h2, h2ax1, h2ax2, h2uniq).
       unshelve econstructor.
       - exact (h2 P pi11 pi12).
       - unshelve econstructor.
         + exact (h1 P' pi21 pi22).
         + pose proof h2uniq as hh2uniq.
           specialize (h2uniq P' pi21 pi22 (h2 P pi11 pi12 o h1 P' pi21 pi22)).
           specialize (hh2uniq P' pi21 pi22 (identity P')).
           rewrite <- h2uniq, <- hh2uniq.
           reflexivity.
           ++ rewrite f_identity. easy.
           ++ rewrite f_identity. easy.
           ++ rewrite assoc.
              rewrite <- h2ax1, <- h1ax1.
              reflexivity.
           ++ rewrite assoc.
              rewrite <- h2ax2, <- h1ax2.
              reflexivity. 
         + pose proof h1uniq as hh1uniq.
           specialize (h1uniq P pi11 pi12 (h1 P' pi21 pi22 o h2 P pi11 pi12)).
           specialize (hh1uniq P pi11 pi12 (identity P)).
           rewrite <- h1uniq, <- hh1uniq.
           reflexivity.
           ++ rewrite f_identity. easy.
           ++ rewrite f_identity. easy.
           ++ rewrite assoc.
              rewrite <- h1ax1, <- h2ax1.
              reflexivity.
           ++ rewrite assoc.
              rewrite <- h1ax2, <- h2ax2.
              reflexivity. 
Qed.

Lemma ProductIsoUnique: forall (C: Category) (A B P P': @obj C) (p: Product C A B P) (p': Product C A B P'),
  { f: @arrow C P P' & Isomorphism C f ->
    forall g: @arrow C P P', (@pi1 C A B P p) o g = (@pi1 C A B P' p') -> 
                             (@pi2 C A B P p) o g = (@pi2 C A B P' p') -> Isomorphism C g -> f = g }.
Proof. intros C A B P P' (pi11, pi12, h1, h1ax1, h1ax2, h1uniq) (pi21, pi22, h2, h2ax1, h2ax2, h2uniq).
       simpl in *.
       exists (h1 P' pi21 pi22).
       intros (finv, fax1, fax2) g Hg1 Hg2 (ginv, gax1, gax2).
       symmetry.
       specialize (h1uniq P' pi21 pi22 g).
       rewrite h1uniq; easy.
Qed.

(* Require Import Coq.Init.Datatypes. *)

Lemma setProd: forall A B: @obj SetCat, Product SetCat A B (prod A B).
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

Definition preorderProdObj (P1 P2: PreOrder): @obj PreOrderCat.
Proof. destruct P1 as (P1, le1, r1, t1).
       destruct P2 as (P2, le2, r2, t2).
       simpl in *.
       unshelve econstructor.
       - exact (prod P1 P2).
       - intros (a, c) (b, d).
         exact ((le1 a b) && (le2 c d)).
       - intros (a, b).
         rewrite r1, r2. reflexivity.
       - intros (a, d) (b, e) (c, f) (H1, H2).
         apply andb_prop in H1, H2.
         destruct H1 as (Ha, Hb).
         destruct H2 as (Hc, Hd).
         assert (le1 a b = true /\ le1 b c = true) by easy.
         specialize (t1 _ _ _ H).
         assert (le2 d e = true /\ le2 e f = true) by easy.
         specialize (t2 _ _ _ H0).
         rewrite t1, t2. reflexivity.
Defined.

Lemma preorderProd: forall A B: @obj PreOrderCat, Product PreOrderCat A B (preorderProdObj A B).
Proof. intros (A, le1, r1, t1) (B, le2, r2, t2).
       unshelve econstructor.
       - simpl. unshelve econstructor.
         + simpl. intros (a, b). exact a.
         + simpl. intros (a, c) (b, d) H.
           apply andb_prop in H. easy.
       - simpl. unshelve econstructor.
         + simpl. intros (a, b). exact b.
         + simpl. intros (a, c) (b, d) H.
           apply andb_prop in H. easy.
       - simpl. intros (Z, le3, r3, t3) (f, fax) (g, gax).
         unshelve econstructor.
         + simpl in *. intro z. exact (f z, g z).
         + simpl in *. intros x y Hx. rewrite fax, gax. 
           easy. easy. easy. 
       - simpl. intros (Z, le3, r3, t3) (f, fax) (g, gax).
         apply PreOrderMapEq. simpl. easy.
       - simpl. intros (Z, le3, r3, t3) (f, fax) (g, gax).
         apply PreOrderMapEq. simpl. easy.
       - simpl. intros (Z, le3, r3, t3) (f, fax) (g, gax) (h, hax) H1 H2.
         apply PreOrderMapEq. simpl.
         inversion H1.
         inversion H2.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H0) as Hax1';
         cbv beta in Hax1'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H3) as Hax2';
         cbv beta in Hax2'.
         apply functional_extensionality.
         intro z.
         simpl in *.
         destruct (h z).
         reflexivity.
Defined.

Definition monoidProdObj (M1 M2: Monoid): @obj Mon.
Proof. destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
       destruct M2 as (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
       simpl in *.
       unshelve econstructor.
       - exact (prod M1 M2).
       - exact (e1, e2).
       - intros (a, c) (b, d).
         exact ((M1f a b), (M2f c d)).
       - intros (a, d) (b, e) (c, f).
         rewrite M1ob1, M2ob1. reflexivity.
       - simpl. intros (a, b).
         rewrite M1ob2, M2ob2. reflexivity.
       - simpl. intros (a, b).
         rewrite M1ob3, M2ob3. reflexivity.
Defined.

Lemma monoidProd: forall A B: @obj Mon, Product Mon A B (monoidProdObj A B).
Proof. destruct A as (A, e1, M1f, M1ob1, M1ob2, M1ob3).
       destruct B as (B, e2, M2f, M2ob1, M2ob2, M2ob3).
       simpl in *.
       unshelve econstructor.
       - simpl. unshelve econstructor.
         + simpl. intros (a, b). exact a.
         + simpl. reflexivity.
         + simpl. intros (a, c) (b, d). reflexivity.
       - simpl. unshelve econstructor.
         + simpl. intros (a, b). exact b.
         + simpl. reflexivity.
         + simpl. intros (a, c) (b, d). reflexivity.
       - simpl. intros (M3, e3, M3f, M3ob1, M3ob2, M3ob3) (f, fax1, fax2) (g, gax1, gax2).
         unshelve econstructor.
         + simpl in *. intro z. exact (f z, g z).
         + simpl in *. rewrite fax1, gax1. reflexivity.
         + simpl in *. intros x y. rewrite fax2, gax2. reflexivity.
       - simpl. intros (M3, e3, M3f, M3ob1, M3ob2, M3ob3) (f, fax1, fax2) (g, gax1, gax2).
         apply MonoidMapEq. simpl. easy.
       - simpl. intros (M3, e3, M3f, M3ob1, M3ob2, M3ob3) (f, fax1, fax2) (g, gax1, gax2).
         apply MonoidMapEq. simpl. easy.
       - simpl. intros (M3, e3, M3f, M3ob1, M3ob2, M3ob3) (f, fax1, fax2) 
                       (g, gax1, gax2) (h, hax1, hax2) H1 H2.
         apply MonoidMapEq. simpl.
         inversion H1.
         inversion H2.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H0) as Hax1';
         cbv beta in Hax1'.
         pose proof (fun x => eq_ind_r (fun f => f x = _ x ) eq_refl H3) as Hax2';
         cbv beta in Hax2'.
         apply functional_extensionality.
         intro z.
         specialize (Hax1' z).
         specialize (Hax2' z).
         destruct (h z).
         rewrite <- Hax1', <- Hax2'.
         reflexivity.
Defined.

Lemma lb: forall (P: PreOrder) (A B AxB: @obj (PreOrderDetCat P)), Product (PreOrderDetCat P) A B AxB ->
  @pohrel P AxB A = true /\ @pohrel P AxB B = true.
Proof. intros (P, le, r, t) A B AxB (pi1, pi2, h, hax1, hax2, huniq).
       split.
       - simpl in pi1.
         simpl. case_eq (le AxB A); intro H.
         + easy.
         + clear hax1 huniq. 
           unfold PreOrderICMap in *.
           simpl in pi1.
           rewrite H in pi1. easy.
       - simpl in pi2.
         simpl. case_eq (le AxB B); intro H.
         + easy.
         + clear hax2 huniq.
           unfold PreOrderICMap in *.
           simpl in pi2.
           rewrite H in pi2. easy.
Qed.

Class POBM (P: PreOrder) (p q: @pos P): Type :=
{
   pobm   : @pos P;
   pobmpi1: @pohrel P pobm p = true;
   pobmpi2: @pohrel P pobm q = true; 
   pobmuni: forall r, @pohrel P r pobm = true <-> @pohrel P r p = true /\ @pohrel P r q = true 
}.

Class hasPOBM (P: PreOrder): Type :=
{
  hpobm: forall p q, POBM P p q 
}.

Lemma binarymeet: forall (P: PreOrder) (p q: @obj (PreOrderDetCat P)) (h: POBM P p q),
  Product (PreOrderDetCat P) p q (@pobm P p q h).
Proof.
   simpl in *.
   unshelve econstructor.
   - simpl in *.
     unfold PreOrderICMap.
     destruct P as (P, le, r, t).
     destruct h as (l, pi1, pi2, uni). simpl in *. rewrite pi1. exact tt.
   - simpl in *.
     unfold PreOrderICMap.
     destruct P as (P, le, r, t).
     destruct h as (l, pi1, pi2, uni). simpl in *. rewrite pi2. exact tt.
   - simpl in *. intros.
     unfold PreOrderICMap in *.
     destruct P as (P, le, r, t).
     destruct h as (l, pi1, pi2, uni). simpl in *.
     specialize (uni Z). 
     destruct (le Z p).
     + destruct (le Z q).
       ++ assert (le Z l = true ). apply uni. easy.
          rewrite H. exact tt.
       ++ easy. 
     + easy.
   - cbn in *. intros z f g.
     apply PreOrderICMapEq.
   - cbn in *. intros z f g.
     apply PreOrderICMapEq.
   - cbn in *. intros z f g p1 Ha Hb.
     apply PreOrderICMapEq.
Defined.

Lemma hasProductsPreOrderDetCat (P: PreOrder) (h: hasPOBM P): hasProducts (PreOrderDetCat P).
Proof. unshelve econstructor.
       - simpl in *. intros p q.
         exact (@pobm P p q (@hpobm P h p q)).
       - simpl. intros p q. apply binarymeet.
Defined.

(* here (slide 58).... *)

(* Lemma glb: forall (P: PreOrder) (A B AxB: @obj (PreOrderDetCat P)), Product (PreOrderDetCat P) A B AxB ->
  forall R, @pohrel P R A = true /\ @pohrel P R B = true -> @pohrel P R AxB = true.
Proof. intros (P, le, refl, trans) p q pxq (pi1, pi2, h, hax1, hax2, huniq) r (Ha, Hb).
       simpl. simpl in Ha, Hb, pi1, pi2, r, h.
       clear hax1 hax2 huniq.
       specialize (h r).
       assert ((if le r pxq then unit else Empty_set) -> le r pxq = true).
       intro H. case_eq (le r pxq); intro H0. easy. rewrite H0 in H. easy.
       apply H.
       simpl in *.
       rewrite Ha, Hb in h. specialize (h tt tt). 
       destruct (le r pxq); exact h. 
Qed. *)

