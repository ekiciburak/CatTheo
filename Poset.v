From Cat Require Import Imports Category Preorder Monoid.
Require Import ProofIrrelevance.

(** Posets *)

Class PoSet: Type :=
{
   poset    : PreOrder;
   posetanti: forall x y, @pohrel poset x y = true /\ @pohrel poset y x = true -> x = y
}.

Class PoSetMap (P1 P2: PoSet): Set :=
{
  posetmap: PreOrderMap (@poset P1) (@poset P2)
}.

Definition idPoSet (P: PoSet): PoSetMap P P.
Proof. destruct P as ((A, le, r, t), a).
       unshelve econstructor.
       - unshelve econstructor.
         + intro x. exact x.
         + intros x x' g. simpl. exact g.
Defined.

Definition compPoSet (P1 P2 P3: PoSet) (f: PoSetMap P1 P2) (g: PoSetMap P2 P3): PoSetMap P1 P3.
Proof. destruct P1 as ((A1, le1, r1, t1), a1).
       destruct P2 as ((A2, le2, r2, t2), a2).
       destruct P3 as ((A3, le3, r3, t3), a3).
       destruct f as (f). destruct f as (f, fax).
       destruct g as (g). destruct g as (g, gax).
       simpl in *.
       unshelve econstructor.
       - unshelve econstructor.
         + intro x. exact (g (f x)).
         + intros x x' h. simpl in *. rewrite gax. reflexivity.
           rewrite fax. reflexivity. exact h.
Defined.


Lemma PoSetMapEq: forall (P1 P2: PoSet) (PM1 PM2: PoSetMap P1 P2),
  @posetmap P1 P2 PM1 = @posetmap P1 P2 PM2 -> PM1 = PM2.
Proof. intros.
       destruct P1 as ((pos1, le1, r1, t1), as1).
       destruct P2 as ((pos2, le2, r2, t2), as2).
       destruct PM1 as (f). destruct f as (f, Hf).
       destruct PM2 as (g). destruct g as (g, Hg).
       simpl in *. inversion H. subst.
       f_equal. f_equal.
       now destruct (proof_irrelevance _ Hf Hg).
Qed.

Definition Poset: Category.
Proof. unshelve econstructor.
       - exact PoSet.
       - intros P1 P2. exact (PoSetMap P2 P1).
       - simpl. intro P. exact (idPoSet P).
       - intros P1 P2 P3 f g. exact (compPoSet P1 P2 P3 g f).
       - repeat intro. now subst.
       - simpl. intros P1 P2 P3 P4 f g h.
         apply PoSetMapEq, PreOrderMapEq.
         destruct P1 as ((A1, le1, r1, t1), a1).
         destruct P2 as ((A2, le2, r2, t2), a2).
         destruct P3 as ((A3, le3, r3, t3), a3).
         destruct P4 as ((A4, le4, r4, t4), a4).
         destruct f as (f). destruct f as (f, Hf).
         destruct g as (g). destruct g as (g, Hg).
         destruct h as (h). destruct h as (h, Hh).
         simpl in *. reflexivity.
       - intros P1 P2 f.
         simpl.
         apply PoSetMapEq, PreOrderMapEq.
         destruct P1 as ((A1, le1, r1, t1), a1).
         destruct P2 as ((A2, le2, r2, t2), a2).
         destruct f as (f). destruct f as (f, Hf).
         simpl. reflexivity.
       - intros P1 P2 f.
         simpl.
         apply PoSetMapEq, PreOrderMapEq.
         destruct P1 as ((A1, le1, r1, t1), a1).
         destruct P2 as ((A2, le2, r2, t2), a2).
         destruct f as (f). destruct f as (f, Hf).
         simpl. reflexivity.
Defined.

Definition PoSetICMap (P: PoSet) (x y: @pos (@poset P)): Set.
Proof. destruct P as ((A, le, r, t), a).
       destruct (le x y).
       - exact unit.
       - exact Empty_set.
Defined.

Lemma PoSetICMapEq: forall (P: PoSet) (x y: @pos (@poset P)) (f g: PoSetICMap P x y), f = g.
Proof. intros.
       destruct P as ((P, le, r, t), a).
       simpl in *.
       clear r t.
       destruct (le x y), f, g. easy.
Qed.

Definition PoSetICid (P: PoSet) (x: @pos (@poset P)): PoSetICMap P x x.
Proof. destruct P as ((A, le, r, t), a). simpl.
       rewrite r. exact tt.
Defined.

Definition PoSetICcomp (P: PoSet) (x y z: @pos (@poset P)) 
  (f: PoSetICMap P z y) (g: PoSetICMap P y x): PoSetICMap P z x.
Proof. destruct P as ((A, le, r, t), a). simpl in *.
       case_eq (le z y); intro Ha.
       - case_eq (le y x); intro Hb.
         + specialize (t z y x). rewrite t. exact tt.
           split. exact Ha. exact Hb.
         + rewrite Hb in g. easy.
       - rewrite Ha in f. easy.
Defined.

Definition PoSetDetCat (P: PoSet): Category.
Proof. unshelve econstructor.
       - exact (@pos (@poset P)).
       - intros x y. exact (PoSetICMap P x y).
       - intro x. exact (PoSetICid P x).
       - simpl. intros a b c f g. exact (PoSetICcomp P a b c f g).
       - repeat intro. now subst.
       - simpl. intros a b c d f g h. apply PoSetICMapEq.
       - simpl. intros a b f. apply PoSetICMapEq.
       - simpl. intros a b f. apply PoSetICMapEq.
Defined.

