(* Assembly printer for RISC-V.
*)

open Arch_decl
open Utils
open PrintCommon
open Prog
open Var0
open Asm_printer
open Risc_utils
open Asm_utils

(* Architecture imports*)
open Riscv_decl
open Riscv_instr_decl



let arch = riscv_decl
let arch_name = "RISCV"

let imm_pre = ""

let pp_reg_address_aux base disp off scal =
  match (disp, off, scal) with
  | None, None, None ->
      Printf.sprintf "(%s)" base
  | Some disp, None, None ->
      Printf.sprintf "%s%s(%s)" imm_pre disp base
  | _, _, _ ->
      hierror
      ~loc:Lnone
      ~kind:"assembly printing"
      "the address computation is too complex: an intermediate variable might be needed"

let pp_imm = Risc_utils.pp_imm imm_pre

let pp_register = Risc_utils.pp_register arch

let pp_reg_address addr =
  Risc_utils.pp_reg_address arch arch_name pp_reg_address_aux addr

let pp_address = Risc_utils.pp_address arch arch_name pp_reg_address_aux

let pp_condition_kind  (ck : Riscv_decl.condition_kind) =
  match ck with
  | EQ -> "beq"
  | NE -> "bne"
  | LT Signed -> "blt"
  | LT Unsigned -> "bltu"
  | GE Signed -> "bge"
  | GE Unsigned -> "bgeu"

let pp_cond_arg (ro: Riscv_decl.register option) =
  match ro with
  | Some r -> pp_register r
  | None -> "x0"


(* this can probably be factor out, but I'm unsure how to do it for the moment*)
let pp_asm_arg (arg : (register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, condt) asm_arg) =
  match arg with
  | Condt _ -> None
  | Imm (ws, w) -> Some (pp_imm (Conv.z_of_word ws w))
  | Reg r -> Some (pp_register r)
  | Regx _ -> .
  | Addr addr -> Some (pp_address addr)
  | XReg _ -> .

(* -------------------------------------------------------------------- *)

(* TODO_RISCV: Review. *)
let headers = [  ]

(* -------------------------------------------------------------------- *)

  let pp_iname_ext _ = ""
  let pp_iname2_ext ext _ _ = ext

let pp_ext = function
 | PP_error             -> assert false
 | PP_name              -> ""
 | PP_iname ws          -> pp_iname_ext ws
 | PP_iname2(s,ws1,ws2) -> pp_iname2_ext s ws1 ws2
 | PP_viname(ve,long)   -> assert false
 | PP_viname2(ve1, ve2) -> assert false
 | PP_ct ct            -> assert false

let pp_name_ext pp_op =
  Format.asprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)



let pp_instr fn i =
  match i with
  | ALIGN ->
      failwith "TODO_RISCV: pp_instr align"

  | LABEL (_, lbl) ->
      [ Label (pp_label fn lbl) ]

  | STORELABEL (dst, lbl) ->
      [ Instr ("adr", [ pp_register dst; string_of_label fn lbl ]) ]

  | JMP lbl ->
      [ Instr ("j", [ pp_remote_label lbl ]) ]

  | JMPI arg ->
      begin match arg with
      | Reg RA -> [Instr ("ret", [])]
      | Reg r -> [ Instr ("jr", [ pp_register r ]) ]
      | _ -> failwith "TODO_RISCV: pp_instr jmpi"
      end

  | Jcc (lbl, ct) ->
      let iname = pp_condition_kind ct.cond_kind in
      let cond_fst = pp_cond_arg ct.cond_fst in
      let cond_snd = pp_cond_arg ct.cond_snd in
      [ Instr (iname, [ cond_fst; cond_snd; pp_label fn lbl ]) ]

  | JAL (RA, lbl) ->
      [Instr ("call", [pp_remote_label lbl])]

  | JAL _
  | CALL _
  | POPPC ->
      assert false

  | SysCall op ->
      [Instr ("call", [ pp_syscall op ])]

  | AsmOp (op, args) ->
      let id = instr_desc riscv_decl riscv_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = pp_name_ext pp in
      let args = List.filter_map (fun (_, a) -> pp_asm_arg a) pp.pp_aop_args in
      [ Instr (name, args) ]


(* -------------------------------------------------------------------- *)

let pp_body fn =
  let open List in
  concat_map @@ fun { asmi_i = i ; asmi_ii = (ii, _) } ->
  let i =
    try pp_instr fn i
    with HiError err -> raise (HiError (Utils.add_iloc err ii)) in
  append
    [Dwarf (DebugInfo.source_positions ii.base_loc)]
    i

(* -------------------------------------------------------------------- *)

let pp_fun (fn, fd) =
  let fn = fn.fn_name in
  let head =
    let fn = escape fn in
    if fd.asm_fd_export then
      [ Instr (".global", [ mangle fn ]); Instr (".global", [ fn ]); ]
    else []
  in let pre =
    let fn = escape fn in
    if fd.asm_fd_export then
      [ Label (mangle fn);
        Label fn;
        Instr ("addi", [ pp_register SP; pp_register SP; "-4"]);
        Instr ("sw", [ pp_register RA;  pp_reg_address_aux (pp_register SP) None None None])]
    else []
  in
  let body = pp_body fn fd.asm_fd_body in
  let pos =
    if fd.asm_fd_export then
      [ Instr ("lw", [ pp_register RA;  pp_reg_address_aux (pp_register SP) None None None]);
        Instr ("addi", [ pp_register SP; pp_register SP; "4"]);
        Instr ("ret", [ ]) ]
    else []
  in
  head @ pre @ body @ pos

let pp_funcs funs = List.concat_map pp_fun funs

let pp_data globs =
  if not (List.is_empty globs) then
    Instr (".p2align", ["5"]) ::
    Label global_datas_label :: List.map (fun b -> Byte (Z.to_string (Conv.z_of_int8 b))) globs
  else []

let pp_prog p =
  let code = pp_funcs p.asm_funcs in
  let data = pp_data p.asm_globs in
  headers @ code @ data

let print_prog fmt p = Asm_printer.pp_asm fmt (pp_prog p)
