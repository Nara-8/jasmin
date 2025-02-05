(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util.
Import Utf8.
Import oseq.
Require Import flag_combination.

Local Open Scope seq_scope.
Local Open Scope Z_scope.


Section WITH_PARAMS.

Context `{asmop:asmOp} {pT: progT}.

Definition remove_wint_opk_ui (k : op_kind_ui) : op_kind_ui :=
  match k with
  | Op_ui ws => op_w ws
  | Op_k _ => k
  end.

Definition remove_wint_cmpk_ui (k : cmp_kind_ui) : cmp_kind_ui :=
  match k with
  | Cmp_ui ws => cmp_w Unsigned ws
  | Cmp_k _ => k
  end.

Definition remove_wint_op2 (o : sop2) : sop2 :=
  match o with
  | Oadd k => Oadd (remove_wint_opk_ui k)
  | Omul k => Omul (remove_wint_opk_ui k)
  | Osub k => Osub (remove_wint_opk_ui k)
  | Oeq  k => Oeq  (remove_wint_opk_ui k)
  | Oneq k => Oneq (remove_wint_opk_ui k)
  | Olt  k => Olt  (remove_wint_cmpk_ui k)
  | Ole  k => Ole  (remove_wint_cmpk_ui k)
  | Ogt  k => Ogt  (remove_wint_cmpk_ui k)
  | Oge  k => Oge  (remove_wint_cmpk_ui k)

  | Obeq | Oand | Oor
  | Odiv _ | Omod _
  | Oland _ | Olor _ | Olxor _
  | Olsr _ | Olsl _ | Oasr _
  | Oror _ | Orol _
  | Ovadd _ _ | Ovsub _ _ | Ovmul _ _
  | Ovlsr _ _ | Ovlsl _ _ | Ovasr _ _ => o
  end.

Fixpoint remove_wint_e (e:pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ | Pvar _ => e
  | Pget al aa ws x e => Pget al aa ws x (remove_wint_e e)
  | Psub al ws len x e => Psub al ws len x (remove_wint_e e)
  | Pload al ws x e => Pload al ws x (remove_wint_e e)
  | Papp1 o e => Papp1 o (remove_wint_e e)
  | Papp2 o e1 e2 => Papp2 (remove_wint_op2 o) (remove_wint_e e1) (remove_wint_e e2)
  | PappN o es => PappN o (map remove_wint_e es)
  | Pif ty e1 e2 e3 => Pif ty (remove_wint_e e1) (remove_wint_e e2) (remove_wint_e e3)
  end.

Definition remove_wint_lv (x : lval) : lval :=
  match x with
  | Lnone _ _ | Lvar _ => x
  | Lmem al ws x e => Lmem al ws x (remove_wint_e e)
  | Laset al aa ws x e => Laset al aa ws x (remove_wint_e e)
  | Lasub aa ws len x e => Lasub aa ws len x (remove_wint_e e)
  end.

Fixpoint remove_wint_ir (ir:instr_r) : instr_r :=
  match ir with
  | Cassgn x tag ty e =>
    Cassgn (remove_wint_lv x) tag ty (remove_wint_e e)

  | Copn xs t o es =>
    Copn (map remove_wint_lv xs) t o (map remove_wint_e es)

  | Csyscall xs o es =>
    Csyscall (map remove_wint_lv xs) o (map remove_wint_e es)

  | Cif b c1 c2 =>
    Cif (remove_wint_e b) (map remove_wint_i c1) (map remove_wint_i c2)

  | Cfor x (dir, e1, e2) c =>
    Cfor x (dir, remove_wint_e e1, remove_wint_e e2) (map remove_wint_i c)

  | Cwhile a c e info c' =>
    Cwhile a (map remove_wint_i c) (remove_wint_e e) info (map remove_wint_i c')

  | Ccall xs f es =>
    Ccall (map remove_wint_lv xs) f (map remove_wint_e es)

  end

with remove_wint_i (i:instr) : instr :=
  let (ii,ir) := i in
  MkI ii (remove_wint_ir ir).

Definition remove_wint_fun (f: fundef) :=
  let 'MkFun ii si p c so r ev := f in
  MkFun ii si p (map remove_wint_i c) so r ev.

Definition remove_wint_prog (p:prog) : prog := map_prog (remove_wint_fun ) p.

End WITH_PARAMS.



