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

Context `{asmop:asmOp} {pd : PointerData} {pT: progT}.

Definition type_of_expr (e:pexpr) : stype :=
  match e with
  | Pconst _ => sint
  | Pbool _ => sbool
  | Parr_init len => sarr len
  | Pvar x => vtype (gv x)
  | Pget al aa ws x e => sword ws
  | Psub al ws len x e => sarr len
  | Pload al ws x e => sword ws
  | Papp1 o e => (type_of_op1 o).2
  | Papp2 o e1 e2 => (type_of_op2 o).2
  | PappN o es => (type_of_opN o).2
  | Pif ty e1 e2 e3 => ty
  end.

Definition cast_expr (e:pexpr) (ty:stype) :=
  match type_of_expr e, ty with
  | sint, sword ws => Papp1 (Oint_of_word ws) e
  | sword ws, sint => Papp1 (Oword_of_int ws) e
  | _, _ => e
  end.

Definition w2i_opk_ui (k : op_kind_ui) : op_kind_ui :=
  match k with
  | Op_ui ws => op_int
  | Op_k _ => k
  end.

Definition w2i_cmpk_ui (k : cmp_kind_ui) : cmp_kind_ui :=
  match k with
  | Cmp_ui ws => cmp_int
  | Cmp_k _ => k
  end.

Definition w2i_op2 (o : sop2) : sop2 :=
  match o with
  | Oadd k => Oadd (w2i_opk_ui k)
  | Omul k => Omul (w2i_opk_ui k)
  | Osub k => Osub (w2i_opk_ui k)

  | Oeq  k => Oeq  (w2i_opk_ui k)
  | Oneq k => Oneq (w2i_opk_ui k)
  | Olt  k => Olt  (w2i_cmpk_ui k)
  | Ole  k => Ole  (w2i_cmpk_ui k)
  | Ogt  k => Ogt  (w2i_cmpk_ui k)
  | Oge  k => Oge  (w2i_cmpk_ui k)

  | Obeq | Oand | Oor
  | Odiv _ | Omod _
  | Oland _ | Olor _ | Olxor _
  | Olsr _ | Olsl _ | Oasr _
  | Oror _ | Orol _
  | Ovadd _ _ | Ovsub _ _ | Ovmul _ _
  | Ovlsr _ _ | Ovlsl _ _ | Ovasr _ _ => o
  end.

Definition w2i_op1_e (o : sop1) (e : pexpr) :=
  match o with
  | Oint_of_word ws => cast_expr e sint
  | _ => Papp1 o (cast_expr e (type_of_op1 o).1)
  end.

Definition w2i_op2_e (o : sop2) (e1 e2 : pexpr) :=
  let o := w2i_op2 o in
  let ty := type_of_op2 o in
  Papp2 o (cast_expr e1 ty.1.1) (cast_expr e2 ty.1.2).

Section Section.
Context (m: var -> option var).

Fixpoint w2i_e (e:pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => e
  | Pvar x =>
    if is_glob x then e
    else
      let x := gv x in
      match m x with
      | Some xi => Pvar (mk_lvar {|v_var := xi; v_info := v_info x|})
      | None => e
      end
  | Pget al aa ws x e => Pget al aa ws x (cast_expr (w2i_e e) sint)
  | Psub al ws len x e => Psub al ws len x (cast_expr (w2i_e e) sint)
  | Pload al ws x e => Pload al ws x (cast_expr (w2i_e e) (sword Uptr))
  | Papp1 o e => w2i_op1_e o (w2i_e e)
  | Papp2 o e1 e2 => w2i_op2_e o (w2i_e e1) (w2i_e e2)
  | PappN o es =>
    let ty := type_of_opN o in
    PappN o (map2 (fun e ty => cast_expr (w2i_e e) ty) es ty.1)
  | Pif ty e1 e2 e3 =>
    let e1 := w2i_e e1 in
    let e2 := w2i_e e2 in
    let e3 := w2i_e e3 in
    if (type_of_expr e2 == sint) && (type_of_expr e3 == sint) then
      Pif sint e1 e2 e3
    else Pif ty e1 (cast_expr e2 ty) (cast_expr e3 ty)
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
