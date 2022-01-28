From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Set Universe Polymorphism.

Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import Coq.Lists.List.

Local Open Scope list_scope.
Local Open Scope char_scope.

(** Initial Object *)

Class Initial (C: Category) (iobj: @obj C): Type :=
{
  imorph : forall X, @arrow C X iobj; 
  imorphu: forall X (f g: @arrow C X iobj), f = g
}.

Class hasInitial (C: Category): Type :=
{
  iobj: @obj C;
  hasi: Initial C iobj 
}.

Lemma ter_ini: forall (C: Category) (T: @obj C) (t: Terminal C T), Initial (DualCategory C) T.
Proof. intros C T (Tax1, Tax2).
       unshelve econstructor.
       - simpl. exact Tax1.
       - simpl. exact Tax2.
Qed.

Lemma ini_ter: forall (C: Category) (I: @obj C) (i: Initial C I), Terminal (DualCategory C) I.
Proof. intros C I (Iax1, Iax2).
       unshelve econstructor.
       - simpl. exact Iax1.
       - simpl. exact Iax2.
Qed.

Lemma initialIso0: forall (C: Category) (I I': @obj C) (i: Initial C I), @Isomorphic C I I' -> Initial C I'.
Proof. intros C I I' (Iax1, Iax2) (f, (finv, fax1, fax2)).
       simpl in *.
       unshelve econstructor.
       - simpl. intro a.
         exact (Iax1 a o finv).
       - simpl. intros a g h.
         specialize (Iax2 a (g o f) (h o f)).
         assert (g o f o finv = h o f o finv).
         { rewrite Iax2. easy.  }
         rewrite <- assoc, fax1, <- assoc, fax1, !f_identity in H.
         easy.
Qed.

Lemma InitialIso: forall (C: Category) (I I': @obj C) (i: Initial C I) (i': Initial C I'), @Isomorphic C I I'.
Proof. intros C I I' (iax1, iax2) (jax1, jax2).
       simpl in *.
       unshelve econstructor.
       - exact (iax1 I').
       - unshelve econstructor.
         + exact (jax1 I).
         + apply jax2.
         + apply iax2.
Qed.

Lemma InitialIsoUnique: forall (C: Category) (I I': @obj C) (i: Initial C I) (i': Initial C I'),
  { f: @arrow C I I' & Isomorphism C f ->
    forall g: @arrow C I I', Isomorphism C g -> f = g }.
Proof. intros C I I' (iax1, iax2) (jax1, jax2).
       simpl in *.
       exists (jax1 I).
       intros (finv, fax1, fax2) g (ginv, gax1, gax2).
       apply jax2.
Qed.

Definition iEmpty: Initial SetCat Empty_set.
Proof. unshelve econstructor.
       - simpl. intros X x. easy.
       - simpl. intros X f g.
         apply functional_extensionality.
         intro x. easy.
Defined.

Definition iunitMon: Initial Mon UMonoid.
Proof. unshelve econstructor.
       - simpl. intro M1.
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         unshelve econstructor.
         + simpl. intro a. exact e1.
         + simpl. reflexivity.
         + simpl. intros. rewrite M1ob2. reflexivity.
       - simpl. intros A f g.
         apply MonoidMapEq.
         destruct A as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct f, g.
         simpl in *.
         apply functional_extensionality.
         intro x. destruct x. 
         rewrite monrelmap1, monrelmap0.
         reflexivity.
Defined.

Class PreOrderBot : Type :=
{
   pob  : PreOrder;
   pbot : @pos pob; 
   pobob: forall (x: @pos pob), (@pohrel pob pbot x) = true
}.

Lemma iPreOrderDetCat: forall (P: PreOrderBot), Initial (PreOrderDetCat (@pob P)) (@pbot P).
Proof. intros ((P, le, r, t), u, ax).
       unshelve econstructor.
       - simpl in *.
         intro y.
         unfold PreOrderICMap.
         rewrite ax. exact tt.
       - simpl in *.
         intros.
         unfold PreOrderICMap in *.
         simpl in *. 
         destruct (le u X).
         destruct f, g. easy.
         destruct f, g. 
Defined.

Definition FreeMonoid: Monoid.
Proof. unshelve econstructor.
       - exact (list ascii).
       - exact nil.
       - intros xs ys. exact (xs ++ ys).
       - intros. simpl. rewrite app_assoc. reflexivity.
       - simpl. intro xs. reflexivity.
       - simpl. intro xs. rewrite app_nil_r. reflexivity.
Defined.

Definition ListMonoid: Monoid.
Proof. unshelve econstructor.
       - exact (list unit).
       - exact nil.
       - intros xs ys. exact (xs ++ ys).
       - intros. simpl. rewrite app_assoc. reflexivity.
       - simpl. intro xs. reflexivity.
       - simpl. intro xs. rewrite app_nil_r. reflexivity.
Defined.

Definition eta {A: Set} (a: A): list A.
Proof. exact (a :: nil). Defined.

Fixpoint fP (A B: Set) (f: A -> A -> A) (g: B -> A) (l: list B) (a: A): A :=
  match l with
    | nil      => a
    | y :: ys  => f (g y) (fP A B f g ys a)
  end.

Definition fBar: forall (M: Monoid) (f: ascii -> (@mons M)), MonoidMap FreeMonoid M.
Proof. intros (M, e, ob, a, ax1, ax2) f.
       simpl in *.
       unshelve econstructor.
       - simpl. intro l. exact (fP _ _ ob f l e).
       - simpl. reflexivity.
       - simpl. intros x.
         induction x; intros.
         + simpl. rewrite ax1. reflexivity.
         + case_eq y; intros.
           ++ simpl. rewrite app_nil_r. rewrite ax2. reflexivity.
           ++ simpl. rewrite IHx. simpl. rewrite a. reflexivity.
Defined.

Theorem fBarUniEx: forall (M: Monoid) (f: ascii -> (@mons M)),
  { fM: MonoidMap FreeMonoid M & f = @comp SetCat _ _ _ (@monmap FreeMonoid M fM) (eta) /\ 
    forall gM: MonoidMap FreeMonoid M, f = @comp SetCat _ _ _ (@monmap FreeMonoid M gM) (eta) -> fM = gM }.
Proof. intros.
       exists (fBar M f).
       simpl.
       destruct M as (M, e, ob, a, ax1, ax2).
       split. simpl.
       apply functional_extensionality. intro b. rewrite ax2. reflexivity.
       intros Hg Hf.
       destruct Hg as (g, Hg1, Hg2).
       apply MonoidMapEq.
       simpl.
       apply functional_extensionality.
       intro l.
       induction l; intros.
       + simpl in *. rewrite Hg1. reflexivity.
       + simpl in *. rewrite IHl. rewrite Hf.
         rewrite <- Hg2. unfold eta. simpl. reflexivity.
Qed.

(** Slice Category *)

Definition SliceCat (C: Category) (s: @obj C): Category.
Proof. unshelve econstructor.
       - exact ({ a & @arrow C s a }).
       - intros (a, f) (b, g).
         exact ({ m: @arrow C b a & f = g o m }).
       - simpl. intros (a, f).
         exists (@identity C a).
         rewrite f_identity. reflexivity.
       - simpl. intros (a, f) (b, g) (c, h) (i, Hi) (k, Hk).
         exists (k o i). rewrite assoc, <- Hk, Hi. reflexivity.
       - repeat intro. now subst.
       - intros (a, f) (b, g) (c, h) (i, Hi) (k, Hk) (j, Hj) (n, Hn).
       Search subsetT_eq_compat.
         apply subsetT_eq_compat. rewrite assoc. reflexivity.
       - intros (a, f) (b, g) (c, h).
         apply subsetT_eq_compat. rewrite f_identity. reflexivity.
       - intros (a, f) (b, g) (c, h).
         apply subsetT_eq_compat. rewrite identity_f. reflexivity.
Defined.

Definition CoSliceCat (C: Category) (s: @obj C): Category.
Proof. unshelve econstructor.
       - exact ({ a & @arrow C a s }).
       - intros (a, f) (b, g).
         exact ({ m: @arrow C b a | g = m o f }).
       - simpl. intros (a, f).
         exists (@identity C a).
         rewrite identity_f. reflexivity.
       - simpl. intros (a, f) (b, g) (c, h) (i, Hi) (k, Hk).
         exists (k o i). rewrite <- assoc, <- Hi, Hk. reflexivity.
       - repeat intro. now subst.
       - intros (a, f) (b, g) (c, h) (i, Hi) (k, Hk) (j, Hj) (n, Hn).
         apply subset_eq_compat. rewrite assoc. reflexivity.
       - intros (a, f) (b, g) (c, h).
         apply subset_eq_compat. rewrite f_identity. reflexivity.
       - intros (a, f) (b, g) (c, h).
         apply subset_eq_compat. rewrite identity_f. reflexivity.
Defined.

Definition PCoSliceCat: Category.
Proof. unshelve econstructor.
       simpl in *.
       - (* exact (@obj Mon * (forall M, @arrow Mon M FreeMonoid))%type. *)
         exact ({ M: @obj Mon & @arrow SetCat (@mons M) ascii })%type.
       - intros (M1, f1) (M2, f2).
         simpl in *.
         exact { f: MonoidMap M2 M1 | (@comp SetCat _ _ _ (@monmap M2 M1 f) f2) = f1 }.
       - simpl. intros (M1, f).
         unshelve econstructor.
         + unshelve econstructor.
           ++ intro A. exact A.
           ++ simpl. reflexivity.
           ++ simpl. reflexivity.
         + simpl. easy.
       - simpl. intros (M1, f1) (M2, f2) (M3, f3) (f, fax) (g, gax).
         exists (@comp Mon _ _ _ f g). rewrite <- fax, <- gax.
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct M2 as (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         destruct M3 as (M3, e3, M3f, M3ob1, M3ob2, M3ob3).
         destruct f as (f, fax1, fax2).
         destruct g as (g, gax1, gax2).
         apply functional_extensionality.
         intro x. simpl in *. reflexivity.
       - repeat intro. now subst.
       - simpl. intros (M1, f1) (M2, f2) (M3, f3) (M4, f4) (f, fax) (g, gax) (h, hax).
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct M2 as (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         destruct M3 as (M3, e3, M3f, M3ob1, M3ob2, M3ob3).
         destruct M4 as (M4, e4, M4f, M4ob1, M4ob2, M4ob3).
         destruct f as (f, fax1, fax2).
         destruct g as (g, gax1, gax2).
         destruct h as (h, hax1, hax2).
         apply subset_eq_compat. apply MonoidMapEq. simpl. reflexivity.
       - simpl. intros (M1, f1) (M2, f2) (f, fax).
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct M2 as (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         destruct f as (f, fax1, fax2).
         apply subset_eq_compat. apply MonoidMapEq. simpl. reflexivity.
       - simpl. intros (M1, f1) (M2, f2) (f, fax).
         destruct M1 as (M1, e1, M1f, M1ob1, M1ob2, M1ob3).
         destruct M2 as (M2, e2, M2f, M2ob1, M2ob2, M2ob3).
         destruct f as (f, fax1, fax2).
         apply subset_eq_compat. apply MonoidMapEq. simpl. reflexivity.
Defined.

Definition fm_eta: @obj PCoSliceCat.
Proof. simpl. exists FreeMonoid. exact eta. Defined.

Definition csiMon: Initial PCoSliceCat fm_eta.
Proof. unshelve econstructor.
       - simpl. intros (M, f).
         specialize (fBarUniEx M f); intro H; unfold unique in H.
         destruct H as (fM, H).
         exists fM. simpl in *. easy.
       - simpl. intros (M1, f) (M2, g) (M3, h).
         specialize (fBarUniEx M1 f); intro H; unfold unique in H.
         destruct H as (fM, (H1, H2)).
         apply subset_eq_compat.
         pose proof H2 as H22.
         simpl in *.
         specialize (H2 M2).
         specialize (H22 M3).
         rewrite <- H2, <- H22. reflexivity.
         easy. easy.
Defined.

