From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import
  compiler_util
  expr
  pseudo_operator.
Import Utf8.

(*
semantics: Ccopy x ws n y

x & y have type array(ws * n)
all y[i] is init (ok u)

*)

Module Import E.
  Definition pass : string := "array copy".

  Definition error := pp_internal_error_s pass "fresh variables are not fresh ...".

End E.

Section Section.

Context `{asmop:asmOp}.
Context (fresh_var_ident: v_kind → string → stype → Ident.ident).

Let fresh_counter : Ident.ident := fresh_var_ident Inline "i__copy" sint.
Let fresh_temporary (ws: wsize) : Ident.ident := fresh_var_ident (Reg (Normal, Direct)) "tmp" (sword ws).

(** Replaces each x = #copy(y) with the following:

  x = ArrayInit();
  for i = 0 to n {
    x[i] = y[i];
  }

  The “x = ArrayInit()” part is neither introduced when x and y are the same local variable nor when x is a ptr.

  Each copied value goes through a temporary variable when both x and y are in memory (stack or global).
*)

Definition direct_copy ws x y i :=
  [:: Cassgn (Laset Aligned AAscale ws x i) AT_none (sword ws) (Pget Aligned AAscale ws y i) ].

Definition tmp_var ws :=
  {| vtype := sword ws; vname := fresh_temporary ws |}.

Definition indirect_copy ws x y i :=
  let tmp := {| v_var := tmp_var ws ; v_info := v_info x |} in
  [:: Cassgn (Lvar tmp) AT_none (sword ws) (Pget Aligned AAscale ws y i);
   Cassgn (Laset Aligned AAscale ws x i) AT_none (sword ws) (Pvar (mk_lvar tmp)) ].

Definition needs_temporary x y : bool :=
  is_var_in_memory x && is_var_in_memory y.

Definition array_copy ii (x: var_i) (ws: wsize) (n: positive) (y: gvar) :=
  let i_name := fresh_counter in
  let i := {| v_var := {| vtype := sint ; vname := i_name |}; v_info := v_info x |} in
  let ei := Pvar (mk_lvar i) in
  let sz := Z.to_pos (wsize_size ws * n) in
  let pre :=
    if eq_gvar (mk_lvar x) y
    || is_ptr x
    then Copn [::] AT_none sopn_nop [::]
    else Cassgn (Lvar x) AT_none (sarr sz) (Parr_init sz) in
  [:: MkI ii pre;
      MkI ii
        (Cfor i (UpTo, Pconst 0, Pconst n)
           [seq MkI ii i | i <- (if needs_temporary x y.(gv) then indirect_copy else direct_copy) ws x y ei ])
    ].

Definition array_copy_c V (array_copy_i : Sv.t -> instr -> cexec cmd) (c:cmd) : cexec cmd :=
  Let cs := mapM (array_copy_i V) c in
  ok (flatten cs).

Definition is_copy o :=
  match o with
  | Opseudo_op (Ocopy ws p) => Some (ws, p)
  | _ => None
  end.

Definition get_source V ii (es: pexprs) : cexec (gvar * cmd) :=
  if es is [:: e ] then
    match e with
    | Pvar x => ok (x, [::])
    | Psub aa ws len x ofs =>
        let ty := sarr (Z.to_pos (arr_size ws len)) in
        let y_name := fresh_var_ident (Ident.id_kind x.(gv).(v_var).(vname)) "src" ty in
        let y_var := {| v_var := Var ty y_name ; v_info := var_info_of_ii ii |} in
        Let _ := assert (~~ Sv.mem y_var V)
                   (pp_internal_error_s_at E.pass ii "fresh source not fresh") in
        let y := {| gs := Slocal ; gv := y_var |} in
        ok (y, [:: MkI ii (Cassgn (Lvar y_var) AT_rename ty e) ])
    | _ => Error (pp_internal_error_s_at E.pass ii "unexpected source for copy ")
    end
  else Error (pp_internal_error_s_at E.pass ii "copy should have a single source").

Definition get_target V ii (xs: lvals) : cexec (var_i * cmd) :=
  if xs is [:: d ] then
    match d with
    | Lvar x => ok (x, [::])
    | Lasub aa ws len x ofs =>
        let ty := sarr (Z.to_pos (arr_size ws len)) in
        let x_name := fresh_var_ident (Ident.id_kind x.(v_var).(vname)) "dst" ty in
        let x_var := {| v_var := Var ty x_name ; v_info := var_info_of_ii ii |} in
        Let _ := assert (~~ Sv.mem x_var V)
                        (pp_internal_error_s_at E.pass ii "fresh destination not fresh") in
        let x := {| gs := Slocal ; gv := x_var |} in
        ok (x_var, [:: MkI ii (Cassgn d AT_rename ty (Pvar x)) ])
    | _ => Error (pp_internal_error_s_at E.pass ii "unexpected destination for copy ")
    end
  else Error (pp_internal_error_s_at E.pass ii "copy should have a single destination").

Fixpoint array_copy_i V (i:instr) : cexec cmd :=
  let:(MkI ii id) := i in
  match id with
  | Cassgn _ _ _ _ => ok [:: i]
  | Copn xs _ o es =>
    match is_copy o with
    | Some (ws, n) =>
      Let: (y, pre) := get_source V ii es in
      Let: (x, post) := get_target V ii xs in
          Let _ := assert (vtype x == sarr (Z.to_pos (arr_size ws n)))
                          (pp_internal_error_s_at E.pass ii "bad type for copy") in
          ok (pre ++ array_copy ii x ws n y ++ post)

    | _ => ok [:: i]
    end
  | Csyscall _ _ _ => ok [:: i]
  | Cif e c1 c2    =>
      Let c1 := array_copy_c V array_copy_i c1 in
      Let c2 := array_copy_c V array_copy_i c2 in
      ok [:: MkI ii (Cif e c1 c2)]
  | Cfor i r c =>
      Let c := array_copy_c V array_copy_i c in
      ok [:: MkI ii (Cfor i r c)]
  | Cwhile a c1 e info c2 =>
      Let c1 := array_copy_c V array_copy_i c1 in
      Let c2 := array_copy_c V array_copy_i c2 in
      ok [:: MkI ii (Cwhile a c1 e info c2)]
  | Ccall _ _ _ => ok [:: i]
  end.

Context {pT: progT}.

Definition array_copy_fd V (f:fundef) :=
  let 'MkFun fi tyin params c tyout res ev := f in
  Let c := array_copy_c V array_copy_i c in
  ok (MkFun fi tyin params c tyout res ev).

Definition array_copy_prog (p:prog) :=
  let V := vars_p (p_funcs p) in
  let fresh := Sv.add {| vtype := sint ; vname := fresh_counter |} (sv_of_list tmp_var wsizes) in
  Let _ := assert (disjoint fresh V) E.error in
  Let fds := map_cfprog (array_copy_fd V) (p_funcs p) in
  ok {| p_funcs := fds;
        p_globs := p_globs p;
        p_abstr := p_abstr p;
        p_extra := p_extra p|}.

End Section.
