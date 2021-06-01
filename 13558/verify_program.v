Require Import VST.floyd.proofauto.
Require Import program.
Require Import list_lemma.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition zeroing_spec : ident * funspec :=
  DECLARE _zeroing
    WITH xs_sh : share, xs_ptr : val, size : Z
    PRE [ tptr tuint, tulong ]
      PROP (
        writable_share xs_sh;
        0 <= size <= Int64.max_unsigned
      )
      PARAMS (xs_ptr; Vlong (Int64.repr size))
      SEP (
        data_at_ xs_sh (tarray tuint size) xs_ptr
      )
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (
        data_at xs_sh (tarray tuint size) (list_repeat (Z.to_nat size) (Vint (Int.repr 0))) xs_ptr
      ).

Definition count_frequency_spec : ident * funspec :=
  DECLARE _count_frequency
    WITH count_sh : share, count_ptr : val, xs_sh : share, xs_ptr : val, xs : list Z, n : Z, a : Z, b : Z
    PRE [ tptr tuint, tptr tushort, tulong, tushort ]
      PROP (
        writable_share count_sh;
        readable_share xs_sh;
        0 <= n <= Int.max_unsigned;
        0 <= a <= 65535;
        0 <= b <= 65535;
        a <= b;
        Forall (fun x => a <= x < b) xs
      )
      PARAMS (count_ptr; xs_ptr; Vlong (Int64.repr n); Vint (Int.repr a))
      SEP (
        data_at count_sh (tarray tuint (b - a)) (list_repeat (Z.to_nat (b - a)) (Vint (Int.repr 0))) count_ptr;
        data_at xs_sh (tarray tushort n) (map (Vint oo Int.repr) xs) xs_ptr
      )
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (
        data_at count_sh (tarray tuint (b - a)) (map (Vint oo Int.repr) (count_frequency xs a b)) count_ptr;
        data_at xs_sh (tarray tushort n) (map (Vint oo Int.repr) xs) xs_ptr
      ).

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
      PROP (
        readable_share seq_sh;
        0 <= size <= Int.max_unsigned;
        Forall (fun x => 1 <= x <= 30000) seq
      )
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

Definition Gprog : funspecs := [ zeroing_spec; count_frequency_spec; flipped_inner_product_spec; solve_spec ].

Ltac range_solve :=
  unfold Int.max_unsigned, Int.modulus;
  simpl;
  try lia.

Lemma body_zeroing :
  semax_body Vprog Gprog f_zeroing zeroing_spec.
Proof.
  start_function.
  forward_for_simple_bound size (
    EX i : Z,
      PROP ()
      LOCAL (
        temp _xs xs_ptr;
        temp _n (Vlong (Int64.repr size))
      )
      SEP (
        data_at xs_sh (tarray tuint size)
          ( list_repeat (Z.to_nat i) (Vint (Int.repr 0))
         ++ list_repeat (Z.to_nat (size - i)) Vundef
          ) xs_ptr
      )).
  - entailer!.
    simpl.
    entailer!.
  - forward.
    entailer!.
    list_solve.
  - entailer!.
    list_solve.
Qed.

Lemma body_count_frequency :
  semax_body Vprog Gprog f_count_frequency count_frequency_spec.
Proof.
  start_function.
  forward_for_simple_bound n (
    EX i : Z,
      PROP ()
      LOCAL (
        temp _count count_ptr;
        temp _xs xs_ptr;
        temp _n (Vlong (Int64.repr n));
        temp _base (Vint (Int.repr a))
      )
      SEP (
        data_at count_sh (tarray tuint (b - a)) (map (Vint oo Int.repr) (count_frequency (sublist 0 i xs) a b)) count_ptr;
        data_at xs_sh (tarray tushort n) (map (Vint oo Int.repr) xs) xs_ptr
      )).
  - entailer!.
    unfold count_frequency.
    simpl.
    rewrite map_list_repeat.
    entailer!.
  - assert_PROP (0 <= i < Zlength xs).
    {  entailer!.
       rewrite Zlength_map in *.
       assumption.
    }
    forward.
    + entailer!.
      assert (a <= Znth i xs < b) by (apply Forall_Znth; assumption).
      rewrite Int.unsigned_repr.
      lia.
      range_solve.
    + forward.
      assert (a <= Znth i xs < b) by (apply Forall_Znth; assumption).
      assert_PROP (Zlength (count_frequency (sublist 0 i xs) a b) = b - a).
      { entailer!.
        rewrite Zlength_count_frequency.
        - reflexivity.
        - lia.
        - apply Forall_sublist.
          assumption.
      }
      forward.
      forward.
      entailer!.
      rewrite (sublist_split 0 i (i+1)); try lia.
      rewrite count_frequency_app; try lia.
      rewrite (sublist_one i (i+1)); try lia.
      unfold count_frequency at 4.
      simpl.
      assert (Z.to_nat (b - a) = length (onehot a b (Znth i xs))).
      { rewrite <- ZtoNat_Zlength.
        rewrite Zlength_onehot.
        lia.
        assumption.
      }
      rewrite H15.
      rewrite addvec_id_r.
      rewrite <- addvec_onehot_r.
      list_solve.
      lia.
      rewrite Zlength_count_frequency.
      reflexivity.
      lia.
      apply Forall_sublist; assumption.
      apply Forall_sublist; assumption.
  - entailer!.
    rewrite Zlength_map.
    rewrite sublist_same.
    entailer!.
    + reflexivity.
    + reflexivity.
Qed.

(*
Lemma body_solve :
  semax_body Vprog Gprog f_solve solve_spec.
Proof.
  start_function.
  forward_call (Tsh, v_counti, 30000).
  1: (split; [auto | computable ]).
  forward_call (Tsh, v_countk, 30000).
  1: split; [auto | computable].
  forward_for_simple_bound size (
    EX i : Z,
      PROP ()
      LOCAL (
        lvar _counti (tarray tuint 30000) v_counti;
        lvar _countk (tarray tuint 30000) v_countk;
        temp _seq seq_ptr;
        temp _n (Vlong (Int64.repr size))
      )
      SEP (
        data_at Tsh (tarray tuint 30000) (list_repeat (Z.to_nat 30000) (Vint (Int.repr 0))) v_counti;
        data_at Tsh (tarray tuint 30000) (list_repeat (Z.to_nat 30000) (Vint (Int.repr 0))) v_countk;
        data_at seq_sh (tarray tushort size) (map (Vint oo Int.repr) seq) seq_ptr
      )).
  - entailer!.
  - assert_PROP (0 <= i < Zlength seq).
    1: entailer!; rewrite Zlength_map in H1; assumption.
    forward.
    { entailer!.
      assert (1 <= Znth i seq <= 30000) by (apply Forall_Znth; assumption).
      rewrite Int.unsigned_repr.
      lia.
      unfold Int.max_unsigned, Int.modulus.
      simpl.
      lia.
    }
    forward.
    assert_PROP (1 <= Znth i seq <= 30000).
    1: entailer!; apply Forall_Znth; assumption.
*)

Lemma body_flipped_inner_product :
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
