Require Import VST.floyd.proofauto.

Definition zip_with {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
  := map (uncurry f) (combine xs ys).

Definition sum_Z := fold_right Z.add 0.

Lemma sum_Z_app xs ys : sum_Z (xs ++ ys) = sum_Z xs + sum_Z ys.
Proof.
  induction xs; simpl; lia.
Qed.

Lemma sum_Z_sublist (xs : list Z) (i : Z) :
  0 <= i < Zlength xs -> sum_Z (sublist 0 (i+1) xs) = sum_Z (sublist 0 i xs) + Znth i xs.
Proof.
  intros.
  rewrite (sublist_split 0 i (i+1)) by lia.
  rewrite (sublist_one i (i+1)) by lia.
  rewrite sum_Z_app; simpl.
  lia.
Qed.

Lemma Zlength_combine (xs ys : list Z) :
  Zlength (combine xs ys) = Z.min (Zlength xs) (Zlength ys).
Proof.
  apply Zlength_length.
  list_solve.
  rewrite combine_length.
  rewrite Z2Nat.inj_min.
  rewrite 2 ZtoNat_Zlength.
  reflexivity.
Qed.

Lemma Znth_combine (xs ys : list Z) (i : Z) :
  0 <= i < Zlength (combine xs ys) ->
  Znth i (combine xs ys) = (Znth i xs, Znth i ys).
Proof.
  intros.
  set (n := Zlength (combine xs ys)).
  rewrite <- (Znth_firstn (combine xs ys) i n).
  rewrite combine_firstn.
  rewrite <- nth_Znth.
  rewrite combine_nth.
  rewrite 2 nth_Znth.
  rewrite 2 Znth_firstn.
  reflexivity.
  all: unfold n.
  all: repeat (rewrite Zlength_combine in *).
  all: repeat (rewrite Zlength_firstn).
  all: repeat (rewrite firstn_length).
  all: repeat (rewrite <- ZtoNat_Zlength).
  all: lia.
Qed.

Definition to_onehot (a b x : Z) : list Z :=
  list_repeat (Z.to_nat (x - a)) 0 ++ [1] ++ list_repeat (Z.to_nat (b - x - 1)) 0.

Definition addvec : list Z -> list Z -> list Z := zip_with Z.add.

Definition count_frequency (xs : list Z) (a b : Z) : list Z
  := fold_right addvec (list_repeat (Z.to_nat (b - a)) 0) (map (to_onehot a b) xs).

Definition flipped_inner_product (xs ys : list Z) : Z :=
  sum_Z (zip_with Z.mul xs (rev ys)).

Lemma Zlength_to_onehot (a b x : Z) :
  a <= x < b -> Zlength (to_onehot a b x) = b - a.
Proof.
  intros.
  unfold to_onehot.
  rewrite 2 Zlength_app.
  rewrite 2 Zlength_list_repeat.
  - assert (Zlength_one : Zlength [1] = 1) by reflexivity.
    rewrite Zlength_one.
    lia.
  - lia.
  - lia.
Qed.

Lemma Zlength_count_frequency (xs : list Z) (a b : Z) :
  a <= b ->
  Forall (fun x => a <= x < b) xs ->
  Zlength (count_frequency xs a b) = b - a.
Proof.
  intros.
  unfold count_frequency.
  induction xs; simpl.
  - rewrite Zlength_list_repeat; lia.
  - unfold addvec, zip_with in *.
    rewrite Zlength_map.
    rewrite Zlength_combine.
    rewrite IHxs.
    rewrite Zlength_to_onehot.
    + lia.
    + inversion H0.
      lia.
    + inversion H0.
      assumption.
Qed.

Lemma length_count_frequency (xs : list Z) (a b : Z) :
  a <= b ->
  Forall (fun x => a <= x < b) xs ->
  length (count_frequency xs a b) = Z.to_nat (b - a).
Proof.
  intros.
  rewrite <- (Zlength_count_frequency xs a b); try assumption.
  rewrite ZtoNat_Zlength.
  reflexivity.
Qed.  

Lemma combine_list_repeat (A B : Type) (y : A) (xs : list B) :
  combine (list_repeat (length xs) y) xs = map (fun x => (y,x)) xs.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma list_repeat_zip_with_id_l (xs : list Z) :
  addvec (list_repeat (length xs) 0) xs = xs.
Proof.
  unfold addvec, zip_with.
  rewrite combine_list_repeat.
  rewrite map_map.
  rewrite map_id.
  reflexivity.
Qed.

Lemma addvec_assoc (xs ys zs : list Z) :
  addvec xs (addvec ys zs) = addvec (addvec xs ys) zs.
Proof.
  revert zs.
  revert ys.
  induction xs.
  - reflexivity.
  - intros.
    destruct ys, zs.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold addvec, zip_with in *.
      simpl in *.
      rewrite IHxs.
      assert (H : a + (z + z0) = (a + z) + z0) by lia.
      rewrite H.
      reflexivity.
Qed.

Lemma count_frequency_cons (a b x : Z) (xs : list Z) :
  count_frequency (x :: xs) a b = addvec (to_onehot a b x) (count_frequency xs a b).
Proof.
  reflexivity.
Qed.

Lemma count_frequency_app (xs ys : list Z) (a b : Z) :
  a <= b ->
  Forall (fun x => a <= x < b) ys ->
  count_frequency (xs ++ ys) a b = addvec (count_frequency xs a b) (count_frequency ys a b).
Proof.
  intros.
  induction xs.
  - unfold count_frequency at 2.
    simpl.
    rewrite <- (length_count_frequency ys a b); try assumption.
    rewrite list_repeat_zip_with_id_l.
    reflexivity.
  - simpl.
    rewrite 2 count_frequency_cons.
    rewrite IHxs.
    apply addvec_assoc.
Qed.
