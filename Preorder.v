From Cat Require Import Imports Category.
Require Import ProofIrrelevance.


(** Preorders *)

Class PreOrder: Type :=
{
   pos    : Set;
   pohrel : pos -> pos -> bool;
   porefl : forall x: pos, pohrel x x = true;
   potrans: forall x y z: pos, pohrel x y = true /\ pohrel y z = true -> pohrel x z = true
}.

Print Nat.leb.

Lemma natleb_refl: forall a: nat, Nat.leb a a = true.
Proof. intro a.
       induction a.
       - simpl. reflexivity.
       - simpl. exact IHa.
Qed.


Lemma natleb_trans: forall x y z : nat, Nat.leb x y = true /\ Nat.leb y z = true ->
                                        Nat.leb x z = true.
Proof. intro x.
       induction x.
       - intros y z (Ha, Hb).
         simpl. reflexivity.
       - intros y z (Ha, Hb).
         simpl.
         simpl in Ha.
         case_eq y.
         + intro Hy.
           rewrite Hy in Ha.
           contradict Ha.
           easy.
         + intros k Hy.
           rewrite Hy in Ha.
           case_eq z.
           ++ intros Hz.
              rewrite Hy, Hz in Hb.
              simpl in Hb.
              contradict Hb.
              easy.
           ++ intros l Hz.
              rewrite Hy, Hz in Hb.
              simpl in Hb.
              specialize (IHx k l (conj Ha Hb)).
              exact IHx.
Qed.

Example NatPreOrder: PreOrder.
Proof. unshelve econstructor.
       - exact nat.
       - exact Nat.leb.
       - intro x.
         rewrite natleb_refl.
         reflexivity.
       - intros x y z (Ha, Hb).
         rewrite natleb_trans with (y := y).
         + reflexivity.
         + split.
           ++ exact Ha.
           ++ exact Hb.
Qed.

Class PreOrderMap (P1 P2: PreOrder): Set :=
{
   posmap   : (@pos P1) -> (@pos P2);
   pohrelmap: forall x x', (@pohrel P1) x x' = true -> (@pohrel P2) (posmap x) (posmap x') = true
}.

Lemma PreOrderMapEq: forall (P1 P2: PreOrder) (F G: PreOrderMap P1 P2),
  @posmap P1 P2 F = @posmap P1 P2 G -> F = G.
Proof. intros.
       destruct P1 as (P1, le1, r1, t1).
       destruct P2 as (P2, le2, r2, t2).
       destruct F as (f, Hf).
       destruct G as (g, Hg).
       simpl in *. subst.
       f_equal.
       now destruct (proof_irrelevance _ Hf Hg).
Qed.

Definition IdPreOrderMap (P: PreOrder): PreOrderMap P P.
Proof. destruct P as (P, le, r, t).
       unshelve econstructor.
       - simpl. intro a. exact a.
       - intros x y H. simpl in *.
         exact H.
Defined.

Definition PreOrderMapComp {P1 P2 P3: PreOrder} (F: PreOrderMap P1 P2) (G: PreOrderMap P2 P3): PreOrderMap P1 P3.
Proof. destruct P1 as (P1, le1, r1, t1).
       destruct P2 as (P2, le2, r2, t2).
       destruct P3 as (P3, le3, r3, t3).
       destruct F as (f, fax).
       simpl in *.
       destruct G as (g, gax).
       simpl in *.
       unshelve econstructor; simpl.
       - intro a. exact (g (f a)).
       - simpl. intros x y H.
         specialize (gax (f x) (f y)).
         apply gax.
         specialize (fax x y).
         apply fax.
         exact H.
Defined.

Lemma PreOrderMapCompAssoc: forall (P1 P2 P3 P4: PreOrder) 
                                   (F: PreOrderMap P1 P2) 
                                   (G: PreOrderMap P2 P3) 
                                   (H: PreOrderMap P3 P4),
                                   PreOrderMapComp (PreOrderMapComp F G) H = 
                                   PreOrderMapComp F (PreOrderMapComp G H).
Proof. intros P1 P2 P3 P4 F G H.
       destruct P1 as (P1, le1, r1, t1).
       destruct P2 as (P2, le2, r2, t2).
       destruct P3 as (P3, le3, r3, t3).
       destruct P4 as (P4, le4, r4, t4).
       destruct F as (f, fax).
       destruct G as (g, gax).
       destruct H as (h, hax).
       simpl in *.
       apply PreOrderMapEq.
       simpl.
       reflexivity.
Qed.

Lemma PreOrderMapIdL: forall (P1 P2: PreOrder) (F: PreOrderMap P1 P2),
                              PreOrderMapComp (IdPreOrderMap P1) F = F.
Proof. intros P1 P2 F.
       destruct P1 as (P1, le1, r1, t1).
       destruct P2 as (P2, le2, r2, t2).
       destruct F as (f, fax).
       simpl in *.
       apply PreOrderMapEq.
       simpl.
       reflexivity.
Qed.

Lemma PreOrderMapIdR: forall (P1 P2: PreOrder) (F: PreOrderMap P1 P2),
                              PreOrderMapComp F (IdPreOrderMap P2) = F.
Proof. intros P1 P2 F.
       destruct P1 as (P1, le1, r1, t1).
       destruct P2 as (P2, le2, r2, t2).
       destruct F as (f, fax).
       apply PreOrderMapEq.
       simpl.
       reflexivity.
Qed.

Definition PreOrderCat: Category.
Proof. unshelve econstructor.
       - exact PreOrder.
       - intros P1 P2. exact (PreOrderMap P2 P1).
       - intro P. simpl. exact (IdPreOrderMap P).
       - intros P1 P2 P3 G F. simpl in *.
         exact (PreOrderMapComp F G).
       - repeat intro. now subst.
       - simpl. intros P1 P2 P3 P4 F G H.
         apply PreOrderMapCompAssoc.
       - simpl. intros P1 P2 F.
         rewrite PreOrderMapIdR.
         reflexivity.
       - simpl. intros P1 P2 F.
         rewrite PreOrderMapIdL.
         reflexivity.
Defined.

(* Lemma PreOrderHRelEq: forall (P: PreOrder) (a b c d: @pos P),
 (@pohrel P b a = true) /\ (@pohrel P c b = true) /\ (@pohrel P d c = true) ->
 (@pohrel P b a && @pohrel P d b) = (@pohrel P c a && @pohrel P d c).
Proof. intros P a b c d (H1, (H2, H3)).
       destruct P as (P, le, r, t).
       cbn in *. rewrite H1, H3. simpl.
       pose proof t as tt.
       specialize (t c b a). rewrite t.
       specialize (tt d c b). rewrite tt. easy.
       easy. easy.
Qed.
 *)

Check @pohrel.

Definition PreOrderICMap (P: PreOrder) (x y: @pos P): Type :=
  if (@pohrel P x y) then unit else Empty_set.

(* Definition PreOrderICMap (P: PreOrder) (x y: @pos P): Type.
Proof. destruct P as (P, le, r, t).
       simpl in *.
       clear r t.
       destruct (le x y).
       - exact unit.
       - exact Empty_set.
Defined. *)

Lemma PreOrderICMapEq: forall (P: PreOrder) (x y: @pos P) (f g: PreOrderICMap P x y), f = g.
Proof. intros P x y.
       destruct P as (P, le, r, t).
       unfold PreOrderICMap.
       simpl in *.
       destruct (le x y).
       - intros f g.
         destruct f, g.
         reflexivity.
       - intros f g.
         destruct f, g.
Qed.

Definition PreOrderICid (P: PreOrder) (x: @pos P): PreOrderICMap P x x.
Proof. destruct P as (P, le, r, t).
       unfold PreOrderICMap.
       simpl in *.
       rewrite r.
       exact tt.
Defined.

Definition PreOrderICcomp (P: PreOrder) (x y z: @pos P) 
  (f: PreOrderICMap P z y) (g: PreOrderICMap P y x): PreOrderICMap P z x.
Proof. destruct P as (A, le, r, t).
       unfold PreOrderICMap in *.
       simpl in *.
       specialize (t z y x).
       case_eq (le z y).
       - intro le1.
         case_eq (le y x).
         + intro le2.
           rewrite le1, le2 in t.
           rewrite t.
           ++ exact tt.
           ++ split.
              * reflexivity.
              * reflexivity.
         + intro le2.
           rewrite le2 in g.
           destruct g.
       - intro le1.
         rewrite le1 in f.
         destruct f.
Defined.

Definition PreOrderDetCat (P: PreOrder): Category.
Proof. unshelve econstructor.
       - exact (@pos P).
       - intros x y. exact (PreOrderICMap P y x).
       - intro x. exact (PreOrderICid P x).
       - simpl. intros z y x g f. exact (PreOrderICcomp P x y z f g).
       - repeat intro. now subst.
       - simpl. intros x y z w f g h. apply PreOrderICMapEq.
       - simpl. intros x y f. apply PreOrderICMapEq.
       - simpl. intros x y f. apply PreOrderICMapEq.
Defined.


Lemma MonoPDC: forall (P: PreOrder) (C := PreOrderDetCat P) (X Y Z: @obj C) (h: arrow Z Y),
  forall (f g: arrow Y X), h o f = h o g -> f = g.
Proof. intros (P, leq, ax1, ax2) C X Y Z h f g e.
       apply PreOrderICMapEq.
Qed.

Lemma EpiPDC: forall (P: PreOrder) (C := PreOrderDetCat P) (X Y Z: @obj C) (h: arrow Y X),
  forall (f g: arrow Z Y), f o h = g o h -> f = g.
Proof. intros (P, leq, ax1, ax2) C X Y Z h f g e.
       apply PreOrderICMapEq.
Qed.





