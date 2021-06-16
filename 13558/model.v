Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Program.Basics.

Import EqNotations.
Local Open Scope program_scope.

Fixpoint lookup {A : Type} (xs : list A) : Fin.t (length xs) -> A :=
  match xs with
  | List.nil => Fin.case0 (fun _ => A)
  | x :: xs => fun i =>
    match i in Fin.t (S n) return n = length xs -> A with
    | F1 => const x
    | FS j => fun H => lookup xs (rew H in j)
    end eq_refl
  end.

Require Import Coq.ZArith.ZArith.
Definition toNat {n : nat} : Fin.t n -> nat := fun x => proj1_sig (Fin.to_nat x).

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

Fixpoint count (x : Z) (xs : list Z) : nat :=
  match xs with
  | List.nil => 0
  | y :: xs =>
    if Z.eq_dec x y
      then S (count x xs)
      else count x xs
  end.

Require Import Coq.Vectors.VectorDef.
Fixpoint tabulate {A : Type} {n : nat} : (Fin.t n -> A) -> VectorDef.t A n :=
  match n as m return m = n -> (Fin.t m -> A) -> VectorDef.t A n with
  | O => fun H f => rew H in nil A
  | S n' => fun H f => rew H in cons A (f F1) n' (tabulate (f ∘ FS))
  end eq_refl.

Definition toZ {n : nat} : Fin.t n -> Z := fun x => Z.of_nat (proj1_sig (Fin.to_nat x)).

Local Open Scope Z_scope.
Definition distribution (xs : list Z) (a b : Z) (H : a <= b) : VectorDef.t nat (Z.to_nat (b - a)) :=
  tabulate (fun i : Fin.t (Z.to_nat (b-a)) => count (a + toZ i) xs).

Definition trisect {A : Type} (xs : list A) (i : Fin.t (length xs)) : list A * A * list A :=
  (firstn (toNat i) xs , lookup xs i , skipn (S (toNat i)) xs).
