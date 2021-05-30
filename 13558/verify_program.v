Require Import VST.floyd.proofauto.
Require Import program.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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
  Search firstn Znth.
  rewrite <- (Znth_firstn (combine xs ys) i n).
  rewrite combine_firstn.
  rewrite <- nth_Znth.
  rewrite combine_nth.
  rewrite 2 nth_Znth.
  rewrite 2 Znth_firstn.
  reflexivity.
  - lia.
  - lia.
  - rewrite Zlength_firstn.
    unfold n.
    rewrite Zlength_combine in *.
    lia.
  - rewrite Zlength_firstn.
    unfold n.
    rewrite Zlength_combine in *.
    lia.
  - rewrite 2 firstn_length.
    unfold n.
    rewrite Zlength_combine in *.
    rewrite <- 2 ZtoNat_Zlength.
    lia.
  - rewrite Zlength_combine.
    rewrite 2 Zlength_firstn.
    unfold n.
    rewrite Zlength_combine in *.
    lia.
  - lia.
Qed.

Definition flipped_inner_product (xs ys : list Z) : Z :=
  sum_Z (zip_with Z.mul xs (rev ys)).

Definition flipped_inner_product_spec : ident * funspec :=
  DECLARE _flipped_inner_product
    WITH xs_sh : share, ys_sh : share, xs_ptr : val, ys_ptr : val, xs : list Z, ys : list Z, size : Z
    PRE [ tptr tuint, tptr tuint, tulong ]
      PROP (
        readable_share xs_sh;
        readable_share ys_sh;
        0 <= size <= Int64.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) xs;
        Forall (fun x => 0 <= x <= Int.max_unsigned) ys
      )
      PARAMS (xs_ptr; ys_ptr; Vlong (Int64.repr size))
      SEP (
        data_at xs_sh (tarray tuint size) (map (Vint oo Int.repr) xs) xs_ptr;
        data_at ys_sh (tarray tuint size) (map (Vint oo Int.repr) ys) ys_ptr
      )
    POST [ tulong ]
      PROP ()
      RETURN (Vlong (Int64.repr (flipped_inner_product xs ys)))
      SEP (
        data_at xs_sh (tarray tuint size) (map (Vint oo Int.repr) xs) xs_ptr;
        data_at ys_sh (tarray tuint size) (map (Vint oo Int.repr) ys) ys_ptr
      ).

Definition solve_spec : ident * funspec :=
  DECLARE _solve
    WITH seq_sh : share, seq_ptr : val, seq : list Z, size : Z
    PRE [ tptr tushort, tulong ]
      PROP ()
      PARAMS (seq_ptr; Vlong (Int64.repr size))
      SEP (
        data_at seq_sh (tarray tushort size) (map (Vint oo Int.repr) seq) seq_ptr
      )
    POST [ tulong ]
      PROP ()
      RETURN ()
      SEP (
        data_at seq_sh (tarray tushort size) (map (Vint oo Int.repr) seq) seq_ptr
      ).

Definition Gprog : funspecs := [ flipped_inner_product_spec; solve_spec ].

(*
Lemma body_solve_spec :
  semax_body Vprog Gprog f_solve solve_spec.
Proof.
  start_function.
  forward.
  forward_for_simple (
    EX i : Z,
      PROP (0 <= i < 30000)
      LOCAL (
        temp _m (Vlong (Int64.repr 30000));
        lvar _counti (tarray tuint 30000) v_counti;
        lvar _countk (tarray tuint 30000) v_countk
      )
      SEP (
        data_at seq_sh (tarray tushort size) (map (Vint oo Int.repr) seq) seq_ptr;
        data_at_ Tsh (tarray tuint 30000) v_counti;
        data_at_ Tsh (tarray tuint 30000) v_countk
      )).
  - entailer!.
  - forward.
    forward.
*)

Lemma body_flipped_inner_product_spec :
  semax_body Vprog Gprog f_flipped_inner_product flipped_inner_product_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound size (
    EX i : Z,
      PROP (
        readable_share xs_sh;
        readable_share ys_sh;
        i <= size
      )
      LOCAL (
        temp _sum (Vlong (Int64.repr (sum_Z (sublist 0 i (map (uncurry Z.mul) (combine xs (rev ys)))))));
        temp _xs xs_ptr;
        temp _ys ys_ptr;
        temp _n (Vlong (Int64.repr size))
      )
      SEP (
            data_at xs_sh (tarray tuint size) (map (Vint oo Int.repr) xs) xs_ptr;
            data_at ys_sh (tarray tuint size) (map (Vint oo Int.repr) ys) ys_ptr
      )).
  - entailer!.
  - assert_PROP (0 <= i < Zlength xs) by (entailer!; list_solve).
    forward.
    assert_PROP (0 <= size - i - 1 < Zlength ys) by (entailer!; list_solve).
    forward.
    forward.
    entailer!.
    rewrite sum_Z_sublist.
    repeat (rewrite Zlength_map in *).
    rewrite <- H9.
    rewrite <- Znth_rev.
    rewrite Znth_map.
    rewrite Znth_combine.
    simpl.
    rewrite 2 Int.unsigned_repr.
    reflexivity.
    all: repeat (rewrite Zlength_map in *); try (rewrite Zlength_combine, Zlength_rev in *); try lia.
    all: apply sublist.Forall_Znth; try (apply Forall_rev); try assumption.
    rewrite Zlength_rev.
    lia.
  - forward.
    entailer!.
    unfold flipped_inner_product, zip_with.
    repeat (rewrite Zlength_map in *).
    rewrite sublist_same; try reflexivity.
    rewrite Zlength_map.
    rewrite Zlength_combine.
    rewrite Zlength_rev.
    lia.
Qed.
