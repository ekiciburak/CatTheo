From Cat Require Import Imports Category Preorder.
Require Import ProofIrrelevance.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Lists.List.


Check UIP_refl.

(** Monoids *)

Class Monoid: Type :=
{
  mons    : Set;
  mone    : mons;
  monrel  : mons -> mons -> mons;
  monassoc: forall x y z: mons, monrel x (monrel y z) = monrel (monrel x y) z;
  monunitl: forall x, monrel mone x = x;
  monunitr: forall x, monrel x mone = x 
}.

Print list_ind.
Print app.

Class PreOrderP: Type :=
{
   posP    : Set;
   pohrelP : posP -> posP -> Prop;
   poreflP : forall x: posP, pohrelP x x;
   potransP: forall x y z: posP, pohrelP x y /\ pohrelP y z -> pohrelP x z
}.

Lemma PreorderL: forall (P: PreOrder), PreOrderP.
Proof. intros (P, leq, ax1, ax2).
       unshelve econstructor.
       - exact P.
       - intros x y.
         exact (leq x y = true).
       - simpl. exact ax1.
       - simpl. exact ax2.
Qed.

Lemma PreMon: forall (M: Monoid), PreOrderP.
Proof. intros (M, e, op, ax1, ax2, ax3).
       unshelve econstructor.
       - exact M.
       - intros x y.
         exact (exists k: M, op x k = y).
       - simpl. intro x.
         exists e.
         exact (ax3 x).
       - simpl. 
         intros x y z ((k1, eq1), (k2, eq2)).
         exists (op k1 k2).
         rewrite ax1, eq1, eq2.
         reflexivity.
Qed.

Lemma app_assoc: forall A (x y z: list A), x ++ y ++ z = (x ++ y) ++ z.
Proof. intros A x.
       induction x.
       - intros y z. 
         simpl. reflexivity.
       - intros y z.
         simpl. rewrite IHx.
         reflexivity.
Qed.

Lemma app_nil: forall A (x : list A), x ++ nil = x.
Proof. intros A x.
       induction x.
       - simpl.
         reflexivity.
       - simpl.
         rewrite IHx.
         reflexivity.
Qed.

Example list_mon (sigma: Set): Monoid.
Proof. unshelve econstructor.
       - exact (list sigma).
       - exact nil.
       - intros l m.
         exact (l ++ m).
       - simpl.
         intros x y z.
         rewrite app_assoc.
         reflexivity.
       - simpl.
         intro x.
         reflexivity.
       - simpl.
         intro x.
         rewrite app_nil.
         reflexivity.
Qed.

Class MonoidMap (M1 M2: Monoid): Set :=
{
  monmap    : (@mons M1) -> (@mons M2);
  monrelmap1: monmap (@mone M1) = (@mone M2);
  monrelmap2: forall x y, monmap (@monrel M1 x y) = (@monrel M2 (monmap x) (monmap y))
}.

Lemma MonoidMapEq: forall (M1 M2: Monoid) (f g: MonoidMap M1 M2),
  @monmap M1 M2 f = @monmap M1 M2 g -> f = g.
Proof. intros.
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct M2 as (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         destruct f as (f, fax1, fax2).
         destruct g as (g, gax1, gax2).
         simpl in *. subst. f_equal.
         + specialize (UIP_refl _ _ gax1); intros. rewrite H. reflexivity.
         + specialize (proof_irrelevance _ fax2 gax2); intros. rewrite H. reflexivity.
Qed.

Definition IdMonoidMap (M: Monoid): MonoidMap M M.
Proof. destruct M as (M, e, mop, Mob1, Mob2, Mob3).
       unshelve econstructor.
       - simpl. intro a. exact a.
       - simpl. reflexivity.
       - simpl. intros x y.
         reflexivity.
Defined.

Definition MonoidMapComp {M1 M2 M3: Monoid} (F: MonoidMap M1 M2) (G: MonoidMap M2 M3): MonoidMap M1 M3.
Proof. destruct M1 as (M1, e1, m1bop, M1ob1, M1ob2, M1ob3).
       destruct M2 as (M2, e2, m2bop, M2ob1, M2ob2, M2ob3).
       destruct M3 as (M3, e3, m3bop, M3ob1, M3ob2, M3ob3).
       destruct F as (f, fax1, fax2).
       destruct G as (g, gax1, gax2).
       simpl in *.
       unshelve econstructor.
       - simpl. intro a. exact (g (f a)).
       - simpl. rewrite fax1, gax1.
         reflexivity.
       - simpl. intros x y.
         rewrite <- gax2, <- fax2.
         reflexivity.
Defined.

Lemma MonoidMapCompAssoc: forall (M1 M2 M3 M4: Monoid)
                                 (F: MonoidMap M1 M2)
                                 (G: MonoidMap M2 M3)
                                 (H: MonoidMap M3 M4),
                                 MonoidMapComp F (MonoidMapComp G H) =
                                 MonoidMapComp (MonoidMapComp F G) H.
Proof. intros.
       destruct M1 as (M1, e1, m1bop, M1ob1, M1ob2, M1ob3).
       destruct M2 as (M2, e2, m2bop, M2ob1, M2ob2, M2ob3).
       destruct M3 as (M3, e3, m3bop, M3ob1, M3ob2, M3ob3).
       destruct M4 as (M4, e4, m4bop, M4ob1, M4ob2, M4ob3).
       destruct F as (f, fax1, fax2).
       destruct G as (g, gax1, gax2).
       destruct H as (h, hax1, hax2).
       simpl in *.
       apply MonoidMapEq.
       simpl.
       reflexivity.
Qed.

Lemma MonoidMapIdL: forall (M1 M2: Monoid) (F: MonoidMap M1 M2),
                           MonoidMapComp (IdMonoidMap M1) F = F.
Proof. intros M1 M2 F.
       destruct M1 as (M1, e1, mop1, M1ob1, M1ob2, M1ob3).
       destruct M2 as (M2, e2, m2op, M2ob1, M2ob2, M2ob3).
       destruct F as (f, fax1, fax2).
       simpl in *.
       apply MonoidMapEq.
       simpl.
       reflexivity.
Qed.

Lemma MonoidMapIdR: forall (M1 M2: Monoid) (F: MonoidMap M1 M2),
                           MonoidMapComp F (IdMonoidMap M2) = F.
Proof. intros M1 M2 F.
       destruct M1 as (M1, e1, mop1, M1ob1, M1ob2, M1ob3).
       destruct M2 as (M2, e2, m2op, M2ob1, M2ob2, M2ob3).
       destruct F as (f, fax1, fax2).
       simpl in *.
       apply MonoidMapEq.
       simpl.
       reflexivity.
Qed.

Definition Mon: Category.
Proof. unshelve econstructor.
       - exact Monoid.
       - intros M1 M2. exact (MonoidMap M2 M1).
       - intro M.
         simpl.
         exact (IdMonoidMap M).
       - intros M1 M2 M3 G F.
         simpl in *.
         exact (MonoidMapComp F G).
       - repeat intro. now subst.
       - simpl. intros M1 M2 M3 M4 F G H.
         rewrite (MonoidMapCompAssoc M1 M2 M3 M4 F G H).
         reflexivity.
       - simpl. intros M1 M2 F.
         rewrite MonoidMapIdR.
         reflexivity.
       - simpl. intros M1 M2 F.
         rewrite MonoidMapIdL.
         reflexivity.
Defined.

Definition MonoidDetCatMorp (M: Monoid) (x y: unit): Type := @mons M.

Definition MonoidDetCatMorpId (M: Monoid) (x: unit): MonoidDetCatMorp M x x := (@mone M).

Definition MonoidDetCatMorpComp {M: Monoid} {a b c : unit} 
                                (f: MonoidDetCatMorp M a b) 
                                (g: MonoidDetCatMorp M b c): MonoidDetCatMorp M a c.
Proof. unfold MonoidDetCatMorp in *.
       destruct M as (M, e, op, Mob1, Mob2, Mob3).
       simpl in *.
       exact (op f g).
Defined.

Lemma MonoidDetCatMorpCompAssoc: forall {M: Monoid} {a b c d: unit} 
                                        (f : MonoidDetCatMorp M a b)
                                        (g : MonoidDetCatMorp M b c)
                                        (h : MonoidDetCatMorp M c d),
                                        MonoidDetCatMorpComp h (@MonoidDetCatMorpComp M a b c g f) =
                                        MonoidDetCatMorpComp (MonoidDetCatMorpComp h g) f.
Proof. intros.
       destruct M as (M, e, Mf, Mob1, Mob2, Mob3).
       unfold MonoidDetCatMorpComp in *.
       simpl in *.
       rewrite Mob1.
       reflexivity.
Qed.


Lemma MonoidDetCatMorpIdL: forall (M : Monoid) (a b : unit) (f : MonoidDetCatMorp M a b),
                                  @MonoidDetCatMorpComp M b b a (MonoidDetCatMorpId M b) f = f.
Proof. intros.
       destruct M as (M, e, Mf, Mob1, Mob2, Mob3).
       simpl in *.
       rewrite Mob2.
       reflexivity.
Qed.

Lemma MonoidDetCatMorpIdR: forall (M : Monoid) (a b : unit) (f : MonoidDetCatMorp M a b),
                                  @MonoidDetCatMorpComp M b a a f (MonoidDetCatMorpId M a) = f.
Proof. intros.
       destruct M as (M, e, Mf, Mob1, Mob2, Mob3).
       simpl in *.
       rewrite Mob3.
       reflexivity.
Qed.

Definition MonoidDetCat (M: Monoid): Category.
Proof. unshelve econstructor.
       - exact unit.
       - intros x y.
         exact (MonoidDetCatMorp M x y).
       - simpl.
         intro x.
         exact (MonoidDetCatMorpId M x).
       - simpl. intros x y z g f.
         exact (MonoidDetCatMorpComp g f).
       - repeat intro. now subst.
       - intros a b c d f g h.
         simpl in *.
         rewrite <- MonoidDetCatMorpCompAssoc.
         reflexivity.
       - intros a b f.
         simpl in *.
         rewrite (MonoidDetCatMorpIdL M a b).
         reflexivity.
       - intros a b f.
         simpl in *.
         rewrite (MonoidDetCatMorpIdR M a b).
         reflexivity.
Defined.

