Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Vectors.Fin.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import Lia.
Import EqNotations.
Local Open Scope program_scope.

Module List.
  Import ListNotations.
  
  Fixpoint lookup {A : Type} (xs : list A) : Fin.t (length xs) -> A :=
    match xs with
    | [] => Fin.case0 (fun _ => A)
    | x :: xs => fun i =>
      match i in Fin.t (S n) return n = length xs -> A with
      | F1 => const x
      | FS j => fun H => lookup xs (rew H in j)
      end eq_refl
    end.
  
  Fixpoint take {A : Type} (xs : list A) : Fin.t (S (length xs)) -> list A :=
    match xs with
    | [] => const []
    | x :: xs => fun i =>
      match i in Fin.t (S n) return n = S (length xs) -> list A with
      | F1 => const []
      | FS j => fun H => x :: take xs (rew H in j)
      end eq_refl
    end.
  
  Fixpoint drop {A : Type} (xs : list A) : Fin.t (S (length xs)) -> list A :=
    match xs with
    | [] => const []
    | x :: xs => fun i =>
      match i in Fin.t (S n) return n = S (length xs) -> list A with
      | F1 => const (x :: xs)
      | FS j => fun H => drop xs (rew H in j)
      end eq_refl
    end.

  Theorem Forall_lookup {A : Type} {P : A -> Prop} {xs : list A} : Forall P xs -> forall i, P (lookup xs i).
  Proof.
    induction xs.
    - intros.
      inversion i.
    - intros.
      dependent destruction H.
      dependent destruction i.
      + apply H.
      + apply IHxs.
        apply H0.
  Qed.

End List.

Module Vector.
  Import VectorDef.
  Import VectorNotations.

  Fixpoint take {A : Type} (m : nat) {n : nat} : VectorDef.t A (m+n) -> VectorDef.t A m :=
    match m return VectorDef.t A (m + n) -> VectorDef.t A m with
    | 0 => Basics.const []
    | S m => fun xs =>
      match xs in VectorDef.t _ l return l = S m + n -> VectorDef.t A (S m) with
      | [] => fun H => False_rect _ (O_S _ H)
      | x :: xs => fun H => x :: take m (rew eq_add_S _ _ H in xs)
      end eq_refl
    end.
  
  Fixpoint drop {A : Type} (m : nat) {n : nat} : VectorDef.t A (m+n) -> VectorDef.t A n :=
    match m return VectorDef.t A (m + n) -> VectorDef.t A n with
    | 0 => id
    | S m => fun xs =>
      match xs in VectorDef.t _ l return l = S m + n -> VectorDef.t A n with
      | [] => fun H => False_rect _ (O_S _ H)
      | x :: xs => fun H => drop m (rew eq_add_S _ _ H in xs)
      end eq_refl
    end.

  Fixpoint tabulate {A : Type} {n : nat} : (Fin.t n -> A) -> VectorDef.t A n :=
    match n as m return m = n -> (Fin.t m -> A) -> VectorDef.t A n with
    | 0 => fun H f => rew H in []
    | S n' => fun H f => rew H in (f F1 :: tabulate (f ∘ FS))
    end eq_refl.

  Definition sum_nat {n : nat} : VectorDef.t nat n -> nat :=
    fun xs => fold_right plus xs 0.

  Definition inner_product {n : nat} : VectorDef.t nat n -> VectorDef.t nat n -> nat :=
    fun xs ys => sum_nat (map2 mult xs ys).

End Vector.

Module Fin.

  Fixpoint inject1 {n : nat} : Fin.t n -> Fin.t (S n) :=
    match n return Fin.t n -> Fin.t (S n) with
    | 0 => Fin.case0 _
    | S n => fun i =>
      match i in Fin.t (S m) return m = n -> Fin.t (S (S n)) with
      | F1 => const F1
      | FS j => fun H => FS (inject1 (rew H in j))
      end eq_refl
    end.
  
  Fixpoint sum_Fin {n : nat} : (Fin.t n -> nat) -> nat :=
    match n with
    | 0 => const 0
    | S n => fun f => f F1 + sum_Fin (f ∘ FS)
    end.
  
  Definition toNat {n : nat} : Fin.t n -> nat := fun x => proj1_sig (Fin.to_nat x).
  
End Fin.

Import List.
Import Vector.
Import Fin.

Definition solution_set (xs : list Z) :=
  sigT (fun i : Fin.t (length xs) =>
  sigT (fun j : Fin.t (length xs) =>
  sig  (fun k : Fin.t (length xs) =>
    toNat i < toNat j < toNat k /\
    Z.sub (lookup xs j) (lookup xs i) = Z.sub (lookup xs k) (lookup xs j)
  ))).

Definition Iso (A B : Type) : Prop :=
  exists (f : A -> B) (g : B -> A),
  g ∘ f = id /\ f ∘ g = id.

Definition solution_rel (xs : list Z) (n : nat) := Iso (solution_set xs) (Fin.t n).

Import ListNotations.
Fixpoint count (x : Z) (xs : list Z) : nat :=
  match xs with
  | [] => 0
  | y :: xs =>
    if Z.eq_dec x y
      then S (count x xs)
      else count x xs
  end.


Definition toZ {n : nat} : Fin.t n -> Z := fun x => Z.of_nat (proj1_sig (Fin.to_nat x)).

Local Open Scope Z_scope.
Definition distribution (xs : list Z) (a b : Z) (Hab : a <= b) : VectorDef.t nat (Z.to_nat (b - a)) :=
  tabulate (fun i : Fin.t (Z.to_nat (b-a)) => count (a + toZ i) xs).

Lemma Connex_Z_le_le (x y : Z) : ({x <= y} + {y <= x}).
Proof.
  destruct (x <=? y) eqn: P;
  [ left; apply Z.leb_le
  | right; apply Z.lt_le_incl; apply Z.leb_gt
  ];
  assumption.
Defined.

Import VectorDef.
Import Vector.

Definition solution_dec (xs : list Z) (a b : Z) (Hab : a <= b) (H : List.Forall (fun x => a <= x < b) xs) : nat :=
  sum_Fin (fun i =>
    let l := Z.to_nat (b-a) in
    let xs_i := List.take xs (inject1 i) in
    let xs_k := List.drop xs (FS i) in
    let xj := lookup xs i in
    let xj_range : a <= xj < b := Forall_lookup H i in
      match Connex_Z_le_le (2*xj) (a+b-1) with
      | left P =>
        let m := Z.to_nat (2*xj - 2*a + 1) in
        let m_split : l = (m + (l - m))%nat := ltac: (lia) in
        let ds_i := take m (rew m_split in distribution xs_i a b Hab) in
        let ds_k := take m (rew m_split in distribution xs_k a b Hab) in
        inner_product ds_i (rev ds_k)
      | right P =>
        let m := Z.to_nat (2*xj - (a+b-1)) in
        let m_split : l = (m + (l - m))%nat := ltac: (lia) in
        let ds_i := drop m (rew m_split in distribution xs_i a b Hab) in
        let ds_k := drop m (rew m_split in distribution xs_k a b Hab) in
        inner_product ds_i (rev ds_k)
      end).
