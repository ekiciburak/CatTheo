From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Set Universe Polymorphism.
(** Category theoretic properties *)

(** Terminal Object *)

Class Terminal (C: Category) (tobj: @obj C): Type :=
{
  tmorph : forall X, @arrow C tobj X; 
  tmorphu: forall X (f g: @arrow C tobj X), f = g
}.

(* Terminal Object Exercise*)

Class Triple: Type :=
{
  us: Set;
  xo: us;
  xs: us -> us
}.

Class TripleMap (T1 T2: Triple): Type :=
{
  um   : @us T1 -> @us T2;
  umax1: um (@xo T1) = @xo T2;
  umax2: forall x, um (@xs T1 x) = (@xs T2) (um x)
}. 

Lemma TripleMapEq: forall {T1 T2: Triple} (F G: TripleMap T1 T2), 
  @um T1 T2 F = @um T1 T2 G -> F = G.
Proof. intros (T1, xo1, xs1) (T2, xo2, xs2) (f, fax1, fax2) (g, gax1, gax2) H.
       simpl in *.
       subst.
       destruct (proof_irrelevance _ fax2 gax2).
       f_equal.
       apply (@UIP _ _ _ eq_refl gax1).
Qed.

Definition TripleCategory: Category.
Proof. unshelve econstructor.
       - exact Triple.
       - intros T1 T2. exact (TripleMap T2 T1).
       - simpl. intro T.
         unshelve econstructor.
         + intro a. exact a.
         + simpl. reflexivity.
         + simpl. intro a. reflexivity.
       - intros (X, x0, xS) (Y, y0, yS) (Z, z0, ZS) (g, gax1, gax2) (f, fax1, fax2).
         unshelve econstructor.
         + simpl in *. intro a. exact (g (f a)).
         + simpl in *. rewrite fax1, gax1.
           reflexivity.
         + simpl in *. intro x.
           rewrite fax2, gax2.
           reflexivity.
       - repeat intro. now subst.
       - simpl. intros.
         apply TripleMapEq.
         destruct a as (X, x0, xS).
         destruct b as (Y, y0, yS).
         destruct c as (Z, z0, zS).
         destruct d as (W, w0, wS).
         destruct f as (f, fax1, fax2).
         destruct g as (g, gax1, gax2).
         destruct h as (h, hax1, hax2).
         simpl in *. 
         reflexivity.
       - simpl. intros.
         apply TripleMapEq.
         destruct a as (X, x0, xS).
         destruct b as (Y, y0, yS).
         destruct f as (f, fax1, fax2).
         simpl in *.
         reflexivity.
       - simpl. intros.
         apply TripleMapEq.
         destruct a as (X, x0, xS).
         destruct b as (Y, y0, yS).
         destruct f as (f, fax1, fax2).
         simpl in *.
         reflexivity.
Defined.

Class hasTerminal (C: Category): Type :=
{
  tobj: @obj C;
  hast: Terminal C tobj 
}.

Lemma hasTerminalTripleCategory: hasTerminal TripleCategory.
Proof. unshelve econstructor.
       - unshelve econstructor.
         + exact unit.
         + exact tt.
         + exact (id).
       - unshelve econstructor.
         + simpl. intros (X, x0, xS).
           unshelve econstructor.
           ++ simpl. intro x. exact tt.
           ++ simpl. reflexivity.
           ++ simpl. intro x. reflexivity.
         + simpl. intros (X, x0, xS).
           intros (f, fax1, fax2) (g, gax1, gax2).
           simpl in *.
           apply TripleMapEq.
           simpl.
           apply functional_extensionality.
           intro x.
           destruct (f x).
           destruct (g x).
           reflexivity.
Qed.

Definition tunit: Terminal SetCat unit.
Proof. unshelve econstructor.
       - simpl. intros X x. exact tt.
       - simpl. intros X f g.
         apply functional_extensionality.
         intro x.
         destruct (f x).
         destruct (g x).
         reflexivity.
Defined.

Lemma hasTerminalSetCat: hasTerminal SetCat.
Proof. unshelve econstructor.
       - exact unit.
       - apply tunit.
Defined.

Definition unit_eqb (a b: unit) := true.
(*   match a, b with
    | tt, tt => true
  end. *)

Definition UPreOrder: PreOrder.
Proof. unshelve econstructor.
       - exact unit.
       - intros a b. exact (unit_eqb a b).
       - simpl. intro x. unfold unit_eqb. reflexivity.
       - simpl. intros. unfold unit_eqb. reflexivity.
Defined.

Lemma umapeq: forall A (f g: A -> unit), f = g.
Proof. intros.
       apply functional_extensionality.
       intro a.
       destruct (f a).
       destruct (g a).
       reflexivity.
Defined.


Definition tunitPre: Terminal PreOrderCat UPreOrder.
Proof. unshelve econstructor.
       - simpl.
         intros (A, le, r, t).
         unshelve econstructor.
         + simpl. intro a.
           exact tt.
         + simpl. intros. reflexivity.
       - simpl. intros A F G.
         apply PreOrderMapEq.
         destruct F as (f, fax).
         destruct G as (g, gax).
         simpl in *.
         apply umapeq.
Defined.

Definition hasTerminalPreOrderCat: hasTerminal PreOrderCat.
Proof. unshelve econstructor.
       - exact UPreOrder.
       - exact tunitPre.
Defined.

Definition UPoset: PoSet.
Proof. unshelve econstructor.
       - exact UPreOrder.
       - simpl. intros.
         destruct x, y. 
         reflexivity.
Defined.

Definition tunitPoset: Terminal Poset UPoset.
Proof. unshelve econstructor.
       - simpl.
         intros ((A, le, r, t), ant).
         unshelve econstructor.
         + simpl.
           unshelve econstructor.
           ++ simpl. intro a.
              exact tt.
           ++ simpl. intros. reflexivity.
       - simpl. intros A f g.
         destruct A as ((A, le, r, t), a).
         destruct f, g.
         simpl in *.
         destruct posetmap, posetmap0.
         simpl in *.
         specialize (umapeq A posmap posmap0); intro.
         subst.
         f_equal. f_equal.
         destruct (proof_irrelevance _ pohrelmap pohrelmap0).
         reflexivity.
Defined.

Definition UMonoid: Monoid.
Proof. unshelve econstructor.
       - exact unit.
       - exact tt.
       - intros a b. exact tt.
       - simpl. intros x y z. reflexivity.
       - simpl. intros.
         destruct x.
         simpl. reflexivity.
       - simpl. intros.
         destruct x. reflexivity.
Defined.


Definition tunitMon: Terminal Mon UMonoid.
Proof. unshelve econstructor.
       - simpl. intro M1.
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         unshelve econstructor.
         + simpl. intro a.
           exact tt.
         + simpl. reflexivity.
         + intros x y. simpl. reflexivity.
       - simpl. intros A F G.
         apply MonoidMapEq.
         destruct A as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct F as (f, fax1, fax2).
         destruct G as (g, gax1, gax2).
         simpl in *.
         apply functional_extensionality.
         intro x.
         destruct (f x).
         destruct (g x).
         reflexivity.
Defined.

Class top (P: PreOrder): Type :=
{
   ptop : @pos P; 
   potob: forall (x: @pos P), (@pohrel P x ptop) = true
}.

Lemma tPreOrderDetCat: forall (P: PreOrder) (t: top P), 
  Terminal (PreOrderDetCat P) (@ptop P t).
Proof. intros (P, le, r, t) (u, ax1).
       unshelve econstructor.
       - intro y. simpl in *.
         unfold PreOrderICMap.
         simpl.
         rewrite ax1. exact tt.
       - simpl in *.
         intros.
         unfold PreOrderICMap in *.
         simpl in *.
         destruct (le X u).
         destruct f, g. easy.
         destruct f, g.
Defined.

Lemma hasTerminalPreOrderDetCat (P: PreOrder) (t: top P): hasTerminal (PreOrderDetCat P).
Proof. unshelve econstructor.
       - exact (@ptop P t).
       - apply tPreOrderDetCat.
Defined.

Class MonoidSingl: Type :=
{
   msingl  : Monoid;
   msinglob: @mons msingl = unit
}.

Lemma SingletonMonoid: Monoid.
Proof. unshelve econstructor.
       - exact unit.
       - exact tt.
       - intros a b. exact tt.
       - simpl. intros a b c. reflexivity.
       - simpl. intro x. destruct x. reflexivity.
       - simpl. intro x. destruct x. reflexivity.
Defined.

Class SingletonList (A: Type) (a: A): Type :=
{
  sl  : list A;
  obsl: (cons a nil) = sl
}.

Lemma SingletonListMonoid: Monoid.
Proof. unshelve econstructor.
       - exact (SingletonList unit tt).
       - unshelve econstructor.
         + exact (cons tt nil).
         + intros. easy.
       - intros (l1, a) (l2, b).
         unshelve econstructor.
         + exact (cons tt nil).
         + easy.
       - simpl. intros (l1, a) (l2, b) (l3, c).  reflexivity.
       - simpl. intros (l, x). subst. reflexivity.
       - simpl. intros (l, x). subst. reflexivity.
Defined.

Lemma MonoidDetCat_SingletonMonoid_Terminal: Terminal (MonoidDetCat SingletonMonoid) tt.
Proof. unshelve econstructor.
       - simpl in *. intro t. exact tt.
       - simpl in *. intros t f g. destruct f, g. easy.
Defined. 

Lemma tMonoidDetCat: forall (M: MonoidSingl), Terminal (MonoidDetCat (@msingl M)) tt.
Proof. intros ((M, e, ob, a, ax1, ax2), ax3).
       unshelve econstructor.
       - simpl in *. intro t. subst. exact tt.
       - simpl in *. intros t f g. subst. destruct f, g. easy.
Defined.


Lemma TerminalIso0: forall (C: Category) (T T': @obj C) (t: Terminal C T), @Isomorphic C T T' -> Terminal C T'.
Proof. intros C T T' (Tax1, Tax2) (f, (finv, fax1, fax2)).
       simpl in *.
       unshelve econstructor.
       - simpl. intro a.
         exact (f o Tax1 a).
       - simpl. intros a g h.
         specialize (Tax2 a (finv o g) (finv o h)).
         assert (f o finv o g = f o finv o h).
         { rewrite <- assoc. rewrite Tax2. rewrite assoc. easy. }
         rewrite fax1, !identity_f in H. easy.
Qed.

Lemma TerminalIso: forall (C: Category) (T T': @obj C) (t: Terminal C T) (t': Terminal C T'), @Isomorphic C T T'.
Proof. intros C T T' (tax1, tax2) (rax1, rax2).
       simpl in *.
       unshelve econstructor.
       - exact (rax1 T).
       - unshelve econstructor.
         + exact (tax1 T').
         + apply rax2.
         + apply tax2.
Qed.

Lemma TerminalIsoUnique: forall (C: Category) (T T': @obj C) (t: Terminal C T) (t': Terminal C T'),
  { f: @arrow C T T' & 
    Isomorphism C f -> (forall g: @arrow C T T', Isomorphism C g -> f = g) }.
Proof. intros C T T' (tax1, tax2) (rax1, rax2).
       simpl in *.
       exists (tax1 T').
       intros (finv, fax1, fax2) g (ginv, gax1, gax2).
       apply tax2.
Qed.

Lemma TerminalIsoUniqueA: forall (C: Category) (T T': @obj C) (t: Terminal C T) (t': Terminal C T') 
  (f g: @arrow C T T'), Isomorphism C f -> Isomorphism C g -> f = g.
Proof. intros C T T' (tax1, tax2) (rax1, rax2) f g
       (finv, fax1, fax2) (ginv, gax1, gax2).
       simpl in *.
       apply tax2.
Qed.

Lemma TerminalIsoUniqueAlt: forall (C: Category) (T T': @obj C) (t: Terminal C T) (t': Terminal C T') 
  (f g: @arrow C T T') (i j:Isomorphism C f), i = j.
Proof. intros C T T' (tax1, tax2) (rax1, rax2) f g
       (finv, fax1, fax2) (ginv, gax1, gax2).
       simpl in *.
       apply IsomorphismEq.
       simpl.
       apply rax2.
Qed.

