From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual Initial Product CoProduct Exponential CCC.


Local Open Scope list_scope.

Inductive IPL: Type :=
 | pi   : IPL
 | truth: IPL
 | conju: IPL -> IPL -> IPL
 | impli: IPL -> IPL -> IPL.

Definition ctx := list (IPL)%type.

Definition extend (c: ctx) (x: IPL) := x :: c.

Fixpoint recI (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2) (l: list IPL) (M: IPL -> (@obj (@uc (PreOrderDetCatisCCC P h1 h2 h3)))): 
  (@obj (@uc (PreOrderDetCatisCCC P h1 h2 h3))) := 
  match l with
    | nil     => @tobj (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                       (@hasT (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                       (@uobs (PreOrderDetCatisCCC P h1 h2 h3)))
    | x :: xs => @pobj (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                       (@hasP (@uc (PreOrderDetCatisCCC P h1 h2 h3)) (@uobs (PreOrderDetCatisCCC P h1 h2 h3))) 
                       (M x) (recI P h1 h2 h3 xs M)
   end.

Class interp (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2): Type :=
{
   M : IPL -> (@obj (@uc (PreOrderDetCatisCCC P h1 h2 h3)));
   i1: { p: (@obj (@uc (PreOrderDetCatisCCC P h1 h2 h3))) | M pi = p };
   i2: M truth = @tobj (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                       (@hasT (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                       (@uobs (PreOrderDetCatisCCC P h1 h2 h3)));
   i3: forall p q, M (conju p q) = @pobj (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                                         (@hasP (@uc (PreOrderDetCatisCCC P h1 h2 h3)) (@uobs (PreOrderDetCatisCCC P h1 h2 h3))) (M p) (M q);
   i4: forall p q, M (impli p q) = @eobj (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                                         (@hasP (@uc (PreOrderDetCatisCCC P h1 h2 h3)) (@uobs (PreOrderDetCatisCCC P h1 h2 h3)))
                                         (@hasE (@uc (PreOrderDetCatisCCC P h1 h2 h3)) (@uobs (PreOrderDetCatisCCC P h1 h2 h3))) (M p) (M q);
   ML: ctx -> (@obj (@uc (PreOrderDetCatisCCC P h1 h2 h3)));
   i5: forall (l: ctx), ML l = recI P h1 h2 h3 l M
}.

Lemma listc: forall (c: ctx) (x: IPL) (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2) (i: interp P h1 h2 h3),
 ((@ML P h1 h2 h3 i) (x :: c)) = @pobj (@uc (PreOrderDetCatisCCC P h1 h2 h3)) 
                                       (@hasP (@uc (PreOrderDetCatisCCC P h1 h2 h3)) (@uobs (PreOrderDetCatisCCC P h1 h2 h3))) 
                                       ((@M P h1 h2 h3 i) x) ((@ML P h1 h2 h3 i) c) .
Proof. intro c.
       induction c; intros.
       - destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h1.
         compute. rewrite !i10.
         simpl. compute. easy.
       - rewrite IHc.
         destruct i.
         destruct h2 as (h2).
         destruct h3 as (h3).
         destruct h1.
         simpl in *.
         rewrite !i10. easy.
Qed.

(** one can decude the IPL formula x in the context [x]; namely [x] |- x *)
Lemma soundR: forall (x: IPL) (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2) (i: interp P h1 h2 h3),
  @pohrel P ((@ML P h1 h2 h3 i) (x :: nil))  ((@M P h1 h2 h3 i) x) = true.
Proof. intros.
       simpl.
       destruct i.
       simpl in *. 
       specialize (i10 (x :: nil)).
       rewrite i10. 
       destruct h2 as (h2).
       destruct h1.
       simpl in *.
       destruct (h2 (M0 x) ptop).
       simpl.
       clear i10.
       exact pobmpi1.
Qed.

Lemma soundRc: forall (c: ctx) (x: IPL) (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2) (i: interp P h1 h2 h3),
  @pohrel P ((@ML P h1 h2 h3 i) (x :: c))  ((@M P h1 h2 h3 i) x) = true.
Proof. intro c.
       induction c; intros.
       - apply soundR.
       - simpl in *.
         rewrite listc.
         simpl.
         specialize (IHc x P h1 h2 h3 i).
         destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h1.
         destruct P.
         simpl in *.
         compute.
         destruct (h2 (M0 x) (ML0 (a :: c))).
         exact pobmpi1.
Qed.

Lemma soundR2: forall (x y: IPL) (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2) (i: interp P h1 h2 h3),
  @pohrel P ((@ML P h1 h2 h3 i) (x :: y :: nil)) ((@M P h1 h2 h3 i) x) = true.
Proof. intros.
       apply soundRc.
Qed.

Inductive IPLE: ctx -> IPL -> Prop :=
  | ax1: forall (c: ctx) (p: IPL), IPLE (p :: c) p
  | ax2: forall (c: ctx) (p q: IPL), IPLE c p -> IPLE (q :: c) p
  | ax3: forall (c: ctx) (p q: IPL), IPLE c p -> IPLE (p :: c) q -> IPLE c q
  | ax4: forall (c: ctx), IPLE c truth
  | ax5: forall (c: ctx) (p q: IPL), IPLE c p -> IPLE c q -> IPLE c (conju p q)
  | ax6: forall (c: ctx) (p q: IPL), IPLE (p :: c) q -> IPLE c (impli p q) 
  | ax7: forall (c: ctx) (p q: IPL), IPLE c (conju p q) -> IPLE c p
  | ax8: forall (c: ctx) (p q: IPL), IPLE c (conju p q) -> IPLE c q
  | ax9: forall (c: ctx) (p q: IPL), IPLE c (impli p q) -> IPLE c p -> IPLE c q.

Example IPLExample_woCut: forall (phi psi theta: IPL),
  IPLE ((impli phi psi) :: (impli psi theta) :: nil)
       (impli phi theta).
Proof. intros. 
       apply ax6.
       apply ax9 with (p := psi).
       - apply ax2.
         apply ax2.
         apply ax1.
       - apply ax9 with (p := phi).
         + apply ax2. 
           apply ax1. 
         + apply ax1.
Qed.

Lemma PO_POIC_l: forall (P: PreOrder) (x y: @pos P) (C := PreOrderDetCat P),
  @pohrel P x y = true -> @arrow C y x.
Proof. intros (P, R, r, t) x y C H.
       unfold PreOrderDetCat in C.
       simpl in *.
       destruct C.
       unfold PreOrderICMap.
       simpl.
       rewrite H.
       exact tt.
Qed.

Lemma PO_POIC_r: forall (P: PreOrder) (x y: @pos P) (C := PreOrderDetCat P),
   @arrow C y x -> @pohrel P x y = true.
Proof. intros (P, R, r, t) x y C H.
       unfold PreOrderDetCat in C.
       simpl in *.
       destruct C.
       unfold PreOrderICMap in H.
       simpl in H.
       case_eq (R x y); intro HH.
       - easy.
       - rewrite HH in H. easy.
Qed.

Lemma soundnessIPL_CCP: forall (x: IPL) (c: ctx) (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2) (i: interp P h1 h2 h3)
  (C := PreOrderDetCat P),
  IPLE c x ->
  @arrow C ((@M P h1 h2 h3 i) x) ((@ML P h1 h2 h3 i) c).
Proof. intros x c P h1 h2 h3 i C H.
       apply PO_POIC_l.
       revert P h1 h2 h3 C i.
       induction H; intros.
       - apply soundRc.
       - simpl.
         rewrite listc.
         specialize (IHIPLE P h1 h2 h3 i).
         simpl in *.
         destruct i.
         simpl in *.
         specialize (i10 (q :: c)).
         destruct h2 as (h2).
         destruct h1.
         destruct P.
         compute.
         destruct (h2 (M0 q) (ML0 c)).
         simpl in *.
         assert (pohrel pobm (ML0 c) = true /\ pohrel (ML0 c) (M0 p) = true) by easy.
         clear h2 h3 i8 i9 i10 C.
         specialize (potrans _ _ _ H0). easy.
       - simpl in *.
         specialize (IHIPLE1 P h1 h2 h3 i).
         specialize (IHIPLE2 P h1 h2 h3 i).
         rewrite listc in IHIPLE2.
         simpl in IHIPLE2.
         destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h1.
         destruct P.
         simpl in *.
         compute in IHIPLE2.
         destruct (h2 (M0 p) (ML0 c)).
         simpl in *.
         specialize (pobmuni (ML0 c)).
         assert (pohrel (ML0 c) (M0 p) = true /\ pohrel (ML0 c) (ML0 c) = true) by easy.
         apply pobmuni in H1.
         assert (pohrel (ML0 c) pobm = true /\ pohrel pobm (M0 q) = true) by easy.
         clear h2 h3 i8 i9 i10 C.
         specialize (potrans _ _ _ H2). easy.
       - simpl in *.
         destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h1.
         simpl in *.
         rewrite i7, potob.
         easy.
       - specialize (IHIPLE1 P h1 h2 h3 i).
         specialize (IHIPLE2 P h1 h2 h3 i).
         destruct i as (M, i1, i2, i3, i4, ML, recI).
         simpl in *.
         destruct h2 as (h2).
         destruct h1.
         simpl in *.
         specialize (i3 p q).
         rewrite i3.
         destruct (h2 (M p) (M q)).
         simpl in *.
         specialize (pobmuni (ML c)).
         rewrite pobmuni.
         easy.
       - simpl in *.
         specialize (IHIPLE P h1 h2 h3 i).
         rewrite listc in IHIPLE.
         destruct i as (M, i1, i2, i3, i4, ML, recI).
         destruct h2 as (h2).
         destruct h3 as (h3).
         destruct h1.
         simpl in *.
         specialize (i4 p q).
         destruct (h3 (M p) (M q)).
         simpl in *.
         specialize (hiob (ML c)).
         destruct (h2 (ML c) (M p)).
         destruct hiob.
         simpl in *.
         destruct (h2 (M p) (ML c)).
         destruct (h2 hi (M p)).
         simpl in *.
         rewrite i4.

         apply H1.
         specialize (pobmuni1 pobm0).
         assert (pohrel pobm (M p) = true /\ pohrel pobm (ML c) = true) by easy.
         apply pobmuni0 in H2.
         assert (pohrel pobm pobm0 = true /\ pohrel pobm0 (M q) = true) by easy .
         clear h2 h3 i2 i3 i4 recI.
         specialize (potrans _ _ _ H3). easy.
       - simpl in *.
         specialize (IHIPLE P h1 h2 h3 i).
         destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h3 as (h3).
         destruct h1.
         destruct P.
         compute.
         compute in IHIPLE.
         specialize (i8 p q).
         compute in i8.
         destruct (h2 (M0 p) (M0 q)).
         simpl in *.
         rewrite i8 in IHIPLE.
         assert (pohrel (ML0 c) pobm = true /\ pohrel pobm (M0 p) = true) by easy.
         clear h2 h3 i8 i9 i10 C.
         specialize (potrans _ _ _ H0). easy.
       - simpl in *.
         specialize (IHIPLE P h1 h2 h3 i).
         destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h3 as (h3).
         destruct h1.
         destruct P.
         compute.
         compute in IHIPLE.
         specialize (i8 p q).
         compute in i8.
         destruct (h2 (M0 p) (M0 q)).
         simpl in *.
         rewrite i8 in IHIPLE.
         assert (pohrel (ML0 c) pobm = true /\ pohrel pobm (M0 q) = true) by easy.
         clear h2 h3 i8 i9 i10 C.
         specialize (potrans _ _ _ H0). easy.
       - simpl in *.
         specialize (IHIPLE1 P h1 h2 h3 i).
         specialize (IHIPLE2 P h1 h2 h3 i).
         destruct i.
         simpl in *.
         destruct h2 as (h2).
         destruct h3 as (h3).
         destruct h1.
         destruct P.
         specialize (i9 p q).
         compute in i9.
         destruct (h3 (M0 p) (M0 q)).
         simpl in *.
         rewrite i9 in IHIPLE1.
         compute in hiapp.
         destruct (h2 hi (M0 p)).
         simpl in *.
         specialize (pobmuni (ML0 c)).
         assert ( pohrel (ML0 c) hi = true /\ pohrel (ML0 c) (M0 p) = true) by easy.
         apply pobmuni in H1.
         assert (pohrel (ML0 c) pobm = true /\ pohrel pobm (M0 q) = true) by easy.
         clear h2 h3 i8 i9 i10 hiob C.
         specialize (potrans _ _ _ H2). easy.
Qed.


