From Cat Require Import Imports Category Preorder Monoid Poset Isomorphism Terminal Dual Initial Product CoProduct Exponential.


Set Universe Polymorphism.

(** CCC *)

Class CCC (C: Category): Type :=
{ 
  hasT: hasTerminal C; 
  hasP: hasProducts C;
  hasE: hasExponentials C hasP;
}.

(** SetCat is a CCC *)

Definition SetCatCCC: CCC SetCat.
Proof. unshelve econstructor.
       - apply hasProductsSetCat.
       - apply hasTerminalSetCat.
       - apply hasExponentialsSetCat.
Defined.

(** PreOrderCat + top + meets + heyting implications is a CCC *)

Definition PreOrderDetCatCCC (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2): CCC (PreOrderDetCat P).
Proof. unshelve econstructor.
       - apply hasProductsPreOrderDetCat. exact h2.
       - apply hasTerminalPreOrderDetCat. exact h1.
       - apply hasExponentialsPreOrderDetCat. exact h3.
Defined.

Class isCCC: Type :=
 {
    uc  : Category;
    uobs: CCC uc
 }.

Class isDisplayedCCC: Type :=
 {
    ucat : Category;
    uobli: CCC ucat;
    udisp: DisplayedCategory ucat
 }.

Definition PreOrderDetCatisCCC (P: PreOrder) (h1: top P) (h2: hasPOBM P) (h3: hasPOHI P h2): isCCC.
Proof. unshelve econstructor.
       - exact (PreOrderDetCat P).
       - eapply PreOrderDetCatCCC; easy.
Defined.

