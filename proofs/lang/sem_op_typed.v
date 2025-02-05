(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export type expr sem_type.
Require Export flag_combination.
Import Utf8.

Definition sem_sop1_typed (o: sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → sem_t t.2 :=
  match o with
  | Oword_of_int sz => wrepr sz
  | Oint_of_word sz => wunsigned
  | Osignext szo szi => @sign_extend szo szi
  | Ozeroext szo szi => @zero_extend szo szi
  | Onot => negb
  | Olnot sz => wnot
  | Oneg Op_int => Z.opp
  | Oneg (Op_w sz) => (-%R)%R
  end.

Arguments sem_sop1_typed : clear implicits.

Definition zlsl (x i : Z) : Z :=
  if (0 <=? i)%Z then (x * 2^i)%Z
  else (x / 2^(-i))%Z.

Definition zasr (x i : Z) : Z :=
  zlsl x (-i).

Definition sem_shift (shift:forall {s}, word s -> Z -> word s) s (v:word s) (i:u8) :=
  let i :=  wunsigned i in
  shift v i.

Definition sem_shr {s} := @sem_shift (@wshr) s.
Definition sem_sar {s} := @sem_shift (@wsar) s.
Definition sem_shl {s} := @sem_shift (@wshl) s.
Definition sem_ror {s} := @sem_shift (@wror) s.
Definition sem_rol {s} := @sem_shift (@wrol) s.

Definition sem_vadd (ve:velem) {ws:wsize} := (lift2_vec ve +%R ws).
Definition sem_vsub (ve:velem) {ws:wsize} := (lift2_vec ve (fun x y => x - y)%R ws).
Definition sem_vmul (ve:velem) {ws:wsize} := (lift2_vec ve *%R ws).

Definition sem_vshr (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wshr x (wunsigned i)) ws v.

Definition sem_vsar (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wsar x (wunsigned i)) ws v.

Definition sem_vshl (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wshl x (wunsigned i)) ws v.

Definition signed {A:Type} (fu fs:A) s :=
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Definition mk_sem_ui sz o (w1 w2 : word sz) : exec (word sz) :=
  let z := o (wunsigned w1) (wunsigned w2) in
  if Z.leb 0 z && Z.leb z (wmax_unsigned sz) then ok (wrepr sz z)
  else Error ErrArith.

Definition mk_sem_divmod sz o (w1 w2: word sz) : exec (word sz) :=
  if ((w2 == 0) || ((wsigned w1 == wmin_signed sz) && (w2 == -1)))%R then Error ErrArith
  else ok (o w1 w2).

Definition mk_sem_sop2 (t1 t2 t3: Type) (o:t1 -> t2 -> t3) v1 v2 : exec t3 :=
  ok (o v1 v2).

Definition sem_sop2_typed (o: sop2) :
  let t := type_of_op2 o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o with
  | Obeq => mk_sem_sop2 (@eq_op bool)
  | Oand => mk_sem_sop2 andb
  | Oor  => mk_sem_sop2 orb

  | Oadd (Op_k Op_int)      => mk_sem_sop2 Z.add
  | Oadd (Op_k (Op_w s))    => mk_sem_sop2 +%R
  | Oadd (Op_ui s)          => mk_sem_ui Z.add
  | Omul (Op_k Op_int)      => mk_sem_sop2 Z.mul
  | Omul (Op_k (Op_w s))    => mk_sem_sop2 *%R
  | Omul (Op_ui s)          => mk_sem_ui Z.mul
  | Osub (Op_k Op_int)      => mk_sem_sop2 Z.sub
  | Osub (Op_k (Op_w s))    => mk_sem_sop2 (fun x y =>  x - y)%R
  | Osub (Op_ui s)          => mk_sem_ui Z.sub
  | Odiv Cmp_int     => mk_sem_sop2 Z.div
  | Odiv (Cmp_w u s) => @mk_sem_divmod s (signed wdiv wdivi u)
  | Omod Cmp_int     => mk_sem_sop2 Z.modulo
  | Omod (Cmp_w u s) => @mk_sem_divmod s (signed wmod wmodi u)

  | Oland s       => mk_sem_sop2 wand
  | Olor  s       => mk_sem_sop2 wor
  | Olxor s       => mk_sem_sop2 wxor
  | Olsr s        => mk_sem_sop2 sem_shr
  | Olsl Op_int   => mk_sem_sop2 zlsl
  | Olsl (Op_w s) => mk_sem_sop2 sem_shl
  | Oasr Op_int   => mk_sem_sop2 zasr
  | Oasr (Op_w s) => mk_sem_sop2 sem_sar
  | Oror s        => mk_sem_sop2 sem_ror
  | Orol s        => mk_sem_sop2 sem_rol

  | Oeq (Op_k Op_int)    => mk_sem_sop2 Z.eqb
  | Oeq (Op_k (Op_w s))  => mk_sem_sop2 eq_op
  | Oeq (Op_ui s)  => mk_sem_sop2 eq_op

  | Oneq (Op_k Op_int)   => mk_sem_sop2 (fun x y => negb (Z.eqb x y))
  | Oneq (Op_k (Op_w s)) => mk_sem_sop2 (fun x y => (x != y))
  | Oneq (Op_ui s) => mk_sem_sop2 (fun x y => (x != y))

  (* Fixme use the "new" Z *)
  | Olt (Cmp_k Cmp_int)   => mk_sem_sop2 Z.ltb
  | Ole (Cmp_k Cmp_int)   => mk_sem_sop2 Z.leb
  | Ogt (Cmp_k Cmp_int)   => mk_sem_sop2 Z.gtb
  | Oge (Cmp_k Cmp_int)   => mk_sem_sop2 Z.geb

  | Olt (Cmp_k (Cmp_w u s)) => mk_sem_sop2 (wlt u)
  | Ole (Cmp_k (Cmp_w u s)) => mk_sem_sop2 (wle u)
  | Ogt (Cmp_k (Cmp_w u s)) => mk_sem_sop2 (fun x y => wlt u y x)
  | Oge (Cmp_k (Cmp_w u s)) => mk_sem_sop2 (fun x y => wle u y x)

  | Olt (Cmp_ui s) => mk_sem_sop2 (wlt Unsigned)
  | Ole (Cmp_ui s) => mk_sem_sop2 (wle Unsigned)
  | Ogt (Cmp_ui s) => mk_sem_sop2 (fun x y => wlt Unsigned y x)
  | Oge (Cmp_ui s) => mk_sem_sop2 (fun x y => wle Unsigned y x)

  | Ovadd ve ws     => mk_sem_sop2 (sem_vadd ve)
  | Ovsub ve ws     => mk_sem_sop2 (sem_vsub ve)
  | Ovmul ve ws     => mk_sem_sop2 (sem_vmul ve)
  | Ovlsr ve ws     => mk_sem_sop2 (sem_vshr ve)
  | Ovlsl ve ws     => mk_sem_sop2 (sem_vshl ve)
  | Ovasr ve ws     => mk_sem_sop2 (sem_vsar ve)
  end.

Arguments sem_sop2_typed : clear implicits.

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

Definition sem_combine_flags (cf : combine_flags) (b0 b1 b2 b3 : bool) : bool :=
  cf_xsem negb andb orb (fun x y => x == y) b0 b1 b2 b3 cf.

Definition sem_opN_typed (o: opN) :
  let t := type_of_opN o in
  sem_prod t.1 (exec (sem_t t.2)) :=
  match o with
  | Opack sz pe => curry (A := sint) (sz %/ pe) (λ vs, ok (wpack sz pe vs))
  | Ocombine_flags cf =>
      fun b0 b1 b2 b3 => ok (sem_combine_flags cf b0 b1 b2 b3)
  end.

End WITH_PARAMS.
