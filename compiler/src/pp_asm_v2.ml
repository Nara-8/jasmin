
(* Assembly printer for RISC-V.
*)

open Arch_decl
open Utils
open PrintCommon
open Prog
open Var0
open X86_decl
open Wsize

open Asm_utils

type rsize = [ `U8 | `U16 | `U32 | `U64 ]

(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

(* -------------------------------------------------------------------- *)
let mangle (x : string) = "_" ^ x

(* -------------------------------------------------------------------- *)
let iwidth = 4

(* -------------------------------------------------------------------- *)
type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg : register) =
  match reg with
  | RSP -> RSpecial `RStack
  | RBP -> RSpecial `RBase
  | RSI -> RSpecial `RSrcIdx
  | RDI -> RSpecial `RDstIdx
  | RAX -> RAlpha 'a'
  | RBX -> RAlpha 'b'
  | RCX -> RAlpha 'c'
  | RDX -> RAlpha 'd'
  | R8  -> RNumeric  8
  | R9  -> RNumeric  9
  | R10 -> RNumeric 10
  | R11 -> RNumeric 11
  | R12 -> RNumeric 12
  | R13 -> RNumeric 13
  | R14 -> RNumeric 14
  | R15 -> RNumeric 15


let x86_asm_global_label = "glob_data"
(* -------------------------------------------------------------------- *)
let rsize_of_wsize (ws : wsize) =
  match ws with
  | U8  -> `U8
  | U16 -> `U16
  | U32 -> `U32
  | U64 -> `U64
  | _   -> raise (InvalidRegSize ws)

(* -------------------------------------------------------------------- *)
let string_of_register ~(reg_prefix:string) (ws : rsize) (reg : register) =
  let ssp = function
    | `RStack  -> "sp"
    | `RBase   -> "bp"
    | `RSrcIdx -> "si"
    | `RDstIdx -> "di" in

  let s = 
    match lreg_of_reg reg, ws with
    | RNumeric i, `U8  -> Printf.sprintf "r%d%s" i "b"
    | RNumeric i, `U16 -> Printf.sprintf "r%d%s" i "w"
    | RNumeric i, `U32 -> Printf.sprintf "r%d%s" i "d"
    | RNumeric i, `U64 -> Printf.sprintf "r%d%s" i ""
    | RAlpha c  , `U8  -> Printf.sprintf "%s%c%s" ""  c "l"
    | RAlpha c  , `U16 -> Printf.sprintf "%s%c%s" ""  c "x"
    | RAlpha c  , `U32 -> Printf.sprintf "%s%c%s" "e" c "x"
    | RAlpha c  , `U64 -> Printf.sprintf "%s%c%s" "r" c "x"
    | RSpecial x, `U8  -> Printf.sprintf "%s%s%s" ""  (ssp x) "l"
    | RSpecial x, `U16 -> Printf.sprintf "%s%s%s" ""  (ssp x) ""
    | RSpecial x, `U32 -> Printf.sprintf "%s%s%s" "e" (ssp x) ""
    | RSpecial x, `U64 -> Printf.sprintf "%s%s%s" "r" (ssp x) "" in
  Printf.sprintf "%s%s" reg_prefix s   

(* -------------------------------------------------------------------- *)

let pp_register_ext ~(reg_pre:string) (_ws: wsize) (r: register_ext) : string =
  Format.sprintf "%smm%d" 
    reg_pre
    (match r with
     | MM0 -> 0
     | MM1 -> 1
     | MM2 -> 2
     | MM3 -> 3
     | MM4 -> 4
     | MM5 -> 5
     | MM6 -> 6
     | MM7 -> 7)

(* -------------------------------------------------------------------- *)
let pp_xmm_register ~(reg_pre:string) (ws: wsize) (r: xmm_register) : string =
  Format.sprintf "%s%smm%d" 
    reg_pre
    (match ws with
     | U8 
     | U16
     | U32
     | U64
     | U128 -> "x"
     | U256 -> "y"
     )
    (match r with
     | XMM0 -> 0
     | XMM1 -> 1
     | XMM2 -> 2
     | XMM3 -> 3
     | XMM4 -> 4
     | XMM5 -> 5
     | XMM6 -> 6
     | XMM7 -> 7
     | XMM8 -> 8
     | XMM9 -> 9
     | XMM10 -> 10
     | XMM11 -> 11
     | XMM12 -> 12
     | XMM13 -> 13
     | XMM14 -> 14
     | XMM15 -> 15)

(* -------------------------------------------------------------------- *)
let pp_scale (scale : Datatypes.nat) =
  match scale with
  | O -> "1"
  | S O -> "2"
  | S (S O) -> "4"
  | S (S (S O)) -> "8"
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let global_datas = "glob_data"

(* -------------------------------------------------------------------- *)
let string_of_label = string_of_label

let string_of_remote_label (fn, lbl) =
  string_of_label fn.fn_name lbl

(* -------------------------------------------------------------------- *)
let string_of_ct (ct : X86_decl.condt) =
  match ct with
  | O_ct   -> "o"
  | NO_ct  -> "no"
  | B_ct   -> "b"
  | NB_ct  -> "nb"
  | E_ct   -> "e"
  | NE_ct  -> "ne"
  | BE_ct  -> "be"
  | NBE_ct -> "nbe"
  | S_ct   -> "s"
  | NS_ct  -> "ns"
  | P_ct   -> "p"
  | NP_ct  -> "np"
  | L_ct   -> "l"
  | NL_ct  -> "nl"
  | LE_ct  -> "le"
  | NLE_ct -> "nle"

(* -------------------------------------------------------------------- *)

let align_of_ws =
  function
  | U8 -> 0
  | U16 -> 1
  | U32 -> 2
  | U64 -> 3
  | U128 -> 4
  | U256 -> 5

let string_of_align ws =
  let n = align_of_ws ws in
  Format.sprintf "%d" n

(* ----------------------------------------------------------------------- *)

let pp_instr_wsize (ws : wsize) =
  match ws with
  | U8  -> "b"
  | U16 -> "w"
  | U32 -> "l"
  | U64 -> "q"
  | _   -> raise (InvalidRegSize ws)

let pp_instr_velem =
  function
  | VE8 -> "b"
  | VE16 -> "w"
  | VE32 -> "d"
  | VE64 -> "q"

let pp_instr_velem_long =
  function
  | VE8 -> "bw"
  | VE16 -> "wd"
  | VE32 -> "dq"
  | VE64 -> "qdq"



module type X86AsmSyntax = sig
  
  val style : Glob_options.x86_assembly_style

  val reg_prefix : string 
  val imm_prefix : string 
  val indirect_prefix : string

  val string_of_adress : wsize -> (register, 'a, 'b, 'c, 'd) Arch_decl.address -> string
  val rev_args : 'a list -> 'a list
  val string_of_iname_extension : wsize -> string 

  val string_of_iname2_extension : string -> wsize -> wsize -> string

  val asm_of_storelabel : string -> register -> Label.label -> asm_element list
  val asm_syntax : asm_element

end


module IntelSyntax : X86AsmSyntax = struct 
  let style = `Intel

  let reg_prefix = ""
  let imm_prefix = ""
  let indirect_prefix = ""

  let pp_reg_address (addr : (_, _, _, _, _) Arch_decl.reg_address) =
    let disp = Conv.z_of_int64 addr.ad_disp in
    let base = addr.ad_base in
    let off  = addr.ad_offset in
    let scal = addr.ad_scale in
  
    if Option.is_none base && Option.is_none off then
      Z.to_string disp
    else 
      begin
        let disp = if Z.equal disp Z.zero then None else Some disp in
        let disp = Option.map_default Z.to_string "" disp in
        let base = Option.map_default (string_of_register ~reg_prefix`U64) "" base in
        let off  = Option.map (string_of_register ~reg_prefix `U64) off in
    
        match off, scal with
        | None, _ ->
            Format.asprintf "%s(%s)" disp base
        | Some off, O ->
            Format.asprintf "%s(%s,%s)" disp base off
        | Some off, _ ->
            Format.asprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
      end

    let pp_address_size (ws:wsize) = 
      match ws with
      | U8   -> "byte"
      | U16  -> "word"
      | U32  -> "dword"
      | U64  -> "qword"
      | U128 -> "xmmword"
      | U256 -> "ymmword"

  let pp_address _ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> pp_reg_address ra
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Printf.sprintf "%s + %s(%%rip)" global_datas disp

  let string_of_adress ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> Printf.sprintf "%s ptr[%s]" (pp_address_size ws) (pp_reg_address ra)
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Printf.sprintf "%s ptr [rip + %s + %s]" (pp_address_size ws) global_datas disp
  
  let rev_args args = args

  let string_of_iname_extension _ = ""

  let string_of_iname2_extension ext _ _ = ext

  let asm_of_storelabel name dst lbl = 
      let reg = string_of_register ~reg_prefix `U64 dst in
      let storage = Format.asprintf "[rip + %s]" (string_of_label name lbl) in
      [Instr ("lea", [reg ; storage])]
  
  let asm_syntax = Header (".intel_syntax noprefix", [])

end


module ATTSyntax : X86AsmSyntax = struct

  let style = `ATT

  let reg_prefix = "$"
  let imm_prefix = "%"
  let indirect_prefix = "*"

  (* -------------------------------------------------------------------- *)
  let pp_reg_address (addr : (_, _, _, _, _) Arch_decl.reg_address) =
    let disp = Conv.z_of_int64 addr.ad_disp in
    let base = addr.ad_base in
    let off  = addr.ad_offset in
    let scal = addr.ad_scale in
  
    if Option.is_none base && Option.is_none off then
      Z.to_string disp
    else begin
      let disp = if Z.equal disp Z.zero then None else Some disp in
      let disp = Option.map_default Z.to_string "" disp in
      let base = Option.map_default (string_of_register ~reg_prefix `U64) "" base in
      let off  = Option.map (string_of_register ~reg_prefix `U64) off in
  
      match off, scal with
      | None, _ ->
          Printf.sprintf "%s(%s)" disp base
      | Some off, O ->
          Printf.sprintf "%s(%s,%s)" disp base off
      | Some off, _ ->
          Printf.sprintf "%s(%s,%s,%s)" disp base off (pp_scale scal)
    end
  
  let string_of_adress _ws (addr : (_, _, _, _, _) Arch_decl.address) =
    match addr with
    | Areg ra -> pp_reg_address ra
    | Arip d ->
      let disp = Z.to_string (Conv.z_of_int64 d) in
      Printf.sprintf "%s + %s(%%rip)" global_datas disp
  
  let rev_args = List.rev 

  (* -------------------------------------------------------------------- *)
  
  let string_of_iname_extension ws = pp_instr_wsize ws
  let string_of_iname2_extension _ ws1 ws2 = Format.asprintf "%s%s" (pp_instr_wsize ws1) (pp_instr_wsize ws2)

  let asm_of_storelabel name dst lbl = 
      let op = Format.asprintf "lea%s" (pp_instr_wsize U64) in
      let load = Format.asprintf "%s(%%rip)" (string_of_label name lbl) in
      let storage = (string_of_register ~reg_prefix `U64 dst) in
    [Instr (op, [load; storage])]

  let asm_syntax = Header(".att_syntax", [])
end 




module X86AsmTranslate (AsmSyntax: X86AsmSyntax) = struct

  let string_of_register ~reg_prefix (ws : rsize) (reg : register) =
    string_of_register ~reg_prefix:reg_prefix ws reg

  let string_of_imm (imm:Z.t) = 
    Format.asprintf "%s%s" AsmSyntax.imm_prefix (Z.to_string imm)

  let string_of_asm_arg ((ws,op) : (wsize * (_, _,_,_,_) Arch_decl.asm_arg)) = 
    match op with 
    | Condt  _   -> assert false
    | Imm(ws, w) -> string_of_imm ((if ws = U8 then Conv.z_unsigned_of_word else Conv.z_of_word) ws w)
    | Reg r      -> string_of_register ~reg_prefix:AsmSyntax.reg_prefix (rsize_of_wsize ws) r
    | Regx r     -> pp_register_ext ~reg_pre:AsmSyntax.reg_prefix ws r
    | Addr addr  -> AsmSyntax.string_of_adress ws addr
    | XReg r     -> pp_xmm_register ~reg_pre:AsmSyntax.reg_prefix ws r

  let string_of_asm_args args = List.map string_of_asm_arg (AsmSyntax.rev_args args)

  (* -------------------------------------------------------------------- *)
  let string_of_indirect_label lbl =
    Format.sprintf "%s%s" AsmSyntax.indirect_prefix (string_of_asm_arg (U64, lbl))


  let pp_ext = function
    | PP_error -> assert false
    | PP_name  -> ""
    | PP_iname ws  -> AsmSyntax.string_of_iname_extension ws
    | PP_iname2(s,ws1,ws2) -> AsmSyntax.string_of_iname2_extension s ws1 ws2
    | PP_viname(ve,long) -> 
      if long then 
        pp_instr_velem_long ve 
      else 
        pp_instr_velem ve 
    | PP_viname2(ve1, ve2) -> 
      Format.asprintf "%s%s" (pp_instr_velem ve1) (pp_instr_velem ve2)
    | PP_ct ct       -> 
      string_of_ct (match ct with Condt ct -> ct | _ -> assert false)

  let string_of_name_extension pp_op =
    Printf.sprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)

  let string_of_syscall (o : 'a Syscall_t.syscall_t) =
    match o with
    | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"


  let asm_instr_r name instr_r = 
    match instr_r with 
    | ALIGN ->
      [Instr (".p2align", ["5"])]
    | LABEL (_, lbl) ->
      [Label (pp_label name lbl)]
    | STORELABEL (dst, lbl) ->
      AsmSyntax.asm_of_storelabel name dst lbl
    | JMP lbl ->
      [Instr ("jmp", [string_of_remote_label lbl])]
    | JMPI lbl ->
      [Instr ("jmp", [string_of_indirect_label lbl])]
    | Jcc(lbl,ct) ->
      let iname = Format.asprintf "j%s" (string_of_ct ct) in
      [Instr(iname, [string_of_label name lbl])]
    | JAL _ -> assert false (* Not possible in x86*)
    | CALL lbl ->
      [Instr ("call", [string_of_remote_label lbl])]
    | POPPC ->
      [Instr ("ret", [])]
    | SysCall(op) ->
      let name = "call" in
      [Instr(name, [string_of_syscall op])]

    | AsmOp(op, args) ->
      let id = instr_desc X86_decl.x86_decl X86_instr_decl.x86_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name = string_of_name_extension pp in
      [Instr(name, (string_of_asm_args pp.pp_aop_args))]
  
  let asm_debug_info ({Location.base_loc = ii; _}, _) =
    [Dwarf (DebugInfo.source_positions ii)]

  let asm_instr name instr = 
    let Arch_decl.({ asmi_i = i; asmi_ii = ii}) = instr in
    asm_debug_info ii @ asm_instr_r name i

  let asm_instrs name instrs = 
    List.fold_left (fun acc instr -> 
      acc @ (asm_instr name instr)
    ) [] instrs

  let asm_function_body (n,d) = 
    let name = n.fn_name in 
    let export = d.asm_fd_export in
    let function_label = if export then
      let name = escape name in 
      [
        Label (mangle (name));
        Label (name);
      ]
    else
      []
    in 
    let function_body = 
      asm_instrs name d.asm_fd_body in 
    let function_tail = if export then 
      [
        Instr ("ret", []);
      ]
    else
      [] 
    in
    function_label @ function_body @ function_tail

  let asm_functions_body funcs = 
    List.fold_left (fun acc (func) -> 
      acc @ (asm_function_body func)
    ) [] funcs
    
  let asm_function_head (n,d) = 
    if d.asm_fd_export then
      let fn = escape n.fn_name in
    [
      Instr (".globl", [mangle fn]);
      Instr (".globl", [fn])
    ]
    else []

  let asm_functions_head (funcs) = 
    List.fold_left (fun acc (func) -> 
      acc @ (asm_function_head func)
    ) [] funcs

  let asm_headers = 
    [
      AsmSyntax.asm_syntax;
      Header (".text", []);
      Header (".p2align", ["5"]); (* Need to determine what 5 is*)
    ]

  let asm_data_segment_header globs names = 

      let name = x86_asm_global_label in 
      let mname = mangle name in 
      [
        Header (".data", []);
        Header (".p2align", [string_of_align U256]);
        Label (mname);
        Label (name);
      ]

  let asm_data_segment_body globs names =
    let datas = Asm_utils.format_glob_data globs names in
    List.fold_left (fun acc data -> 
      acc @ [(data)]
    ) [] datas


  let asm_data_segment globs names =
    if not (List.is_empty globs) then 
      let headers = asm_data_segment_header globs names in
      let data = asm_data_segment_body globs names in 
      headers @ data
    else
      []

  let asm_of_prog (asm : X86_instr_decl.x86_prog) = 
    let headers = asm_headers in 
    let functions_head = asm_functions_head asm.asm_funcs in
    let functions_body = asm_functions_body asm.asm_funcs in
    let data_segment = asm_data_segment asm.asm_globs asm.asm_glob_names in
    headers @ functions_head @ functions_body @ data_segment

end

module TranslateATT = X86AsmTranslate(ATTSyntax)
module TranslateIntel = X86AsmTranslate(IntelSyntax)

let asm_of_prog (asm : X86_instr_decl.x86_prog) = 
  match !Glob_options.assembly_style with
  | `ATT -> TranslateATT.asm_of_prog asm
  | `Intel -> TranslateIntel.asm_of_prog asm
