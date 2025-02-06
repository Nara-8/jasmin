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


Module Import E.

  Definition pass : string := "wint_to_int".

  Definition ierror := pp_internal_error_s pass.

End E.

Section WITH_PARAMS.

Context {msfsz : MSFsize} `{asmop:asmOp} {pd : PointerData} {pT: progT}.

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

Definition w2i_lv (x : lval) :=
  match x with
  | Lnone _ _ => x
  | Lvar x =>
    match m x with
    | Some xi => Lvar {|v_var := xi; v_info := v_info x|}
    | _ => x
    end
  | Lmem al ws x e => Lmem al ws x (cast_expr (w2i_e e) (sword Uptr))
  | Laset al aa ws x e => Laset al aa ws x (cast_expr (w2i_e e) sint)
  | Lasub aa ws len x e => Lasub aa ws len x (cast_expr (w2i_e e) sint)
  end.

Definition check_lv (x : lval) :=
  match x with
  | Lnone _ _ => true
  | Lvar x =>
    match m x with
    | Some xi => false
    | _ => true
    end
  | Lmem al ws x e => true
  | Laset al aa ws x e => true
  | Lasub aa ws len x e => true
  end.

Definition type_of_lv (x : lval) :=
  match x with
  | Lnone _ ty => ty
  | Lvar x => vtype x
  | Lmem al ws x e => sword ws
  | Laset al aa ws x e => sword ws
  | Lasub aa ws len x e => sarr len
  end.

Context (sigs : funname -> option (list stype * list stype)).

Definition get_sig f :=
  match sigs f with
  | Some sig => ok sig
  | None => Error (E.ierror "unknown function")
  end.

Fixpoint w2i_ir ii (ir:instr_r) : cexec instr_r :=
  match ir with
  | Cassgn x tag ty e =>
    let x := w2i_lv x in
    let e := w2i_e e in
    let ty := if type_of_lv x == sint then sint else ty in
    ok (Cassgn x tag ty (cast_expr e ty))

  | Copn xs t o es =>
    if all check_lv xs then
      let xs := map w2i_lv xs in
      let es := map w2i_e es in
      let es := map2 cast_expr es (sopn_tin o) in
      ok (Copn xs t o es)
    else Error (E.ierror "bad lval in Copn") (* FIXME *)

  | Csyscall xs o es =>
    if all check_lv xs then
      let xs := map w2i_lv xs in
      let es := map w2i_e es in
      let tys := scs_tin (syscall_sig_u o) in
      let es := map2 cast_expr es tys in
      ok (Csyscall xs o es)
    else Error (E.ierror "bad lval in Csyscall") (* FIXME *)

  | Cif b c1 c2 =>
    Let c1 := mapM w2i_i c1 in
    Let c2 := mapM w2i_i c2 in
    ok (Cif (w2i_e b) c1 c2)

  | Cfor x (dir, e1, e2) c =>
    Let c := mapM w2i_i c in
    ok (Cfor x (dir, w2i_e e1, w2i_e e2) c)

  | Cwhile a c e info c' =>
    Let c := mapM w2i_i c in
    Let c' := mapM w2i_i c' in
    ok (Cwhile a c (w2i_e e) info c')

  | Ccall xs f es =>
    let xs := map w2i_lv xs in
    let es := map w2i_e es in
    Let sig := get_sig f in
    if List.map type_of_lv xs == sig.1 then
      ok (Ccall xs f (map2 cast_expr es sig.2))
    else Error (E.ierror "bad lval in Ccall") (* FIXME *)
  end

with w2i_i (i:instr) : cexec instr :=
  let (ii,ir) := i in
  Let ir := add_iinfo ii (w2i_ir ii ir) in
  ok (MkI ii ir).

(* FIXME *)

Definition w2i_vari (x:var_i) : var_i :=
  match m x with
  | Some xi => {| v_var := xi; v_info := v_info x |}
  | None => x
  end.

Definition w2i_fun (fn:funname) (f: fundef) :=
  Let sig := add_funname fn (get_sig fn) in
  let 'MkFun ii si p c so r ev := f in
  let p := List.map w2i_vari p in
  let r := List.map w2i_vari r in
  Let c := add_funname fn (mapM w2i_i c) in
  ok (MkFun ii sig.1 p c sig.2 r ev).

Definition build_sig (fd : funname * fundef) :=
 let 'MkFun ii si p c so r ev := fd.2 in
 let mk := map2 (fun (x:var_i) ty => match m x with None => ty | Some _ => sint end) in
 (fd.1, (mk p si, mk r so)).

End Section.

Context (info : var -> option var).

Definition build_info (fv : Sv.t) :=
  Let fvm :=
    foldM (fun x (fvm: Sv.t * Mvar.t var) =>
      match info x with
      | None => ok fvm
      | Some xi =>
        Let _ := assert ((vtype xi == sint) && ~~Sv.mem xi fvm.1) (E.ierror "invalid info") in
        ok (Sv.add xi fvm.1, Mvar.set fvm.2 x xi)
      end)
      (fv, Mvar.empty var)
      (Sv.elements fv) in
   ok (Mvar.get fvm.2).

Definition remove_wint_prog (p:prog) : cexec prog :=
  let fv := vars_p (p_funcs p) in
  Let m := build_info fv in
  let sigs := map (build_sig m) (p_funcs p) in
  Let funcs := map_cfprog_name (w2i_fun m (get_fundef sigs)) (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End WITH_PARAMS.
