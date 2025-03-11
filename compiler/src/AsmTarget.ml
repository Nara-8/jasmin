
open Arch_decl
open Utils
open PrintCommon
open Prog
open Var0


type asm_element = 
| Header of string * string list
| Label of string
| Dwarf of string
| Instr of string * string list
| Comment of string
| Byte of string

type asm = asm_element list

module type AsmTarget = sig 

  type reg
  type regx 
  type xreg
  type rflag
  type cond
  type op

  type arch = (reg, regx, xreg, rflag, cond) arch_decl
  type prog = (reg, regx, xreg, rflag, cond, op)  asm_prog
  type arg = (reg, regx, xreg, rflag, cond) asm_arg
  type func = (reg, regx, xreg, rflag, cond, op) asm_fundef
  type args = arg list

  (**
  Asm instructions (asm_i_r) build functions
  *)
  val build_align : string -> asm
  val build_label : Label.label_kind -> BinNums.positive -> string -> asm
  val build_storelabel : reg -> BinNums.positive -> string -> asm
  val build_jmp : Label.remote_label -> string -> asm
  val build_jmpi : arg -> string -> asm
  val build_jcc : BinNums.positive -> cond -> string -> asm
  val build_jal : reg -> Label.remote_label -> string -> asm
  val build_call : Label.remote_label -> string -> asm
  val build_poppc : string -> asm
  val build_syscall : BinNums.positive Syscall_t.syscall_t -> string -> asm
  val build_asmop : op -> args -> string -> asm
  
  val build_function_header : func -> asm

  (** 
  Asm data segment build functions
  *)
  val build_data_segment : Obj.t list -> ((Var.var * 'a) * BinNums.coq_Z) list -> asm 

  val build_program_header : prog -> asm

end


module AsmBuilder = struct 

  module type S = sig 

  end

  module Make (T : AsmTarget) : S = struct 
    let make_instr_r (fn:string) (i:(T.reg, T.regx, T.xreg, T.rflag, T.cond,T.op) asm_i_r) = 
      match i with
      | ALIGN -> T.build_align fn
      | LABEL (lbl, pos) -> T.build_label lbl pos fn
      | STORELABEL (dst, pos) -> T.build_storelabel dst pos fn
      | JMP lbl -> T.build_jmp lbl fn
      | JMPI arg -> T.build_jmpi arg fn
      | Jcc (lbl, ct) -> T.build_jcc lbl ct fn
      | JAL (r, lbl) -> T.build_jal r lbl fn
      | CALL lbl -> T.build_call lbl fn
      | POPPC -> T.build_poppc fn
      | SysCall op -> T.build_syscall op fn
      | AsmOp (op, args) -> T.build_asmop op args fn
    
    (* let make_instr (fn:string) (i:(T.reg, T.regx, T.xreg, T.rflag, T.cond, T.op) asm_i_r) : asm =
      []
    
    let make_instrs (fn:string) (instrs:(T.reg, T.regx, T.xreg, T.rflag, T.cond, T.op) asm_i list) : asm = 
      List.concat_map (make_instr fn) instrs
     *)
    let make_func_body (fname:funname) (f:T.func) : asm = 
      if f.asm_fd_export then 
        []
      else
        []

    let make_func ((fname,f) : funname * T.func) : asm = 
      let function_headers = T.build_function_header f in
      let function_body = make_func_body fname f in
      function_headers @ function_body

    let make_funcs (funcs : (funname * T.func) list) : asm = 
      List.concat_map make_func funcs

    let make_data_segment (prog) : asm = 
      T.build_data_segment prog.asm_globs prog.asm_glob_names 
    
    let make_prog_headers (prog : T.prog) : asm = 
      T.build_program_header prog
    
    let make_prog (prog : T.prog) : asm = 
      let headers = make_prog_headers prog in
      let code = make_funcs prog.asm_funcs in
      let data = make_data_segment prog in
      headers @ code @ data

  end

end 

module type BPrinter = sig 
  val style            : Glob_options.x86_assembly_style
  val imm_prefix       : string
  val reg_prefix       : string
  val indirect_prefix  : string
  val string_of_adress : Wsize.wsize -> ('a, 'b, 'c, 'd, 'e) Arch_decl.address -> string
  val rev_args         : 'a list -> 'a list
  val string_of_iname_ext     : Wsize.wsize -> string
  val string_of_iname2_ext    : string -> Wsize.wsize -> Wsize.wsize -> string
  val string_of_storelabel   : string -> 'a -> Label.label -> string
  val asm_syntax : string  
end 


let pp_remote_label (fn, lbl) =
  PrintASM.string_of_label fn.fn_name lbl


let make_label (fname:string) (lbl:BinNums.positive) : string = 
  Format.asprintf "L%s$%d" (escape fname) (Conv.int_of_pos lbl)

module X86Target(BP: BPrinter) : (AsmTarget with
  type reg  = X86_decl.register 
  and type regx = X86_decl.register_ext 
  and type xreg = X86_decl.xmm_register 
  and type rflag = X86_decl.rflag 
  and type cond = X86_decl.condt
  and type op = X86_instr_decl.x86_op)
= struct 

  type reg  = X86_decl.register 
  type regx = X86_decl.register_ext 
  type xreg = X86_decl.xmm_register 
  type rflag = X86_decl.rflag 
  type cond = X86_decl.condt
  type op = X86_instr_decl.x86_op

  type arch = (reg, regx, xreg, rflag, cond) arch_decl
  type prog = (reg, regx, xreg, rflag, cond, op)  asm_prog
  type arg = (reg, regx, xreg, rflag, cond) asm_arg
  type func = (reg, regx, xreg, rflag, cond, op) asm_fundef
  type args = arg list

  let pp_imm (imm : Z.t) =
    Format.sprintf "%s%s" BP.imm_prefix (Z.to_string imm)

  let string_of_asm_arg ((ws,op):(Wsize.wsize * (_, _, _, _, _) Arch_decl.asm_arg)) =
    match op with
    | Condt  _   -> assert false (* explain why*)
    | Imm(ws, w) -> pp_imm ((if ws = U8 then Conv.z_unsigned_of_word else Conv.z_of_word) ws w)
    | Reg r      -> AsmX86Utils.pp_register ~reg_pre:(BP.reg_prefix) (AsmX86Utils.rsize_of_wsize ws) r
    | Regx r     -> AsmX86Utils.pp_register_ext ~reg_pre:(BP.reg_prefix) ws r
    | Addr addr  -> BP.string_of_adress ws addr
    | XReg r     -> AsmX86Utils.pp_xmm_register ~reg_pre:(BP.reg_prefix) ws r
    
  let string_of_indirect_label lbl =
    Format.asprintf "%s%s" BP.indirect_prefix (string_of_asm_arg (Wsize.U64, lbl))
   
  let pp_ext = function
    | PP_error                          -> assert false
    | PP_name                           -> ""
    | PP_iname ws          -> BP.string_of_iname_ext ws
    | PP_iname2(s,ws1,ws2) -> BP.string_of_iname2_ext s ws1 ws2
    | PP_viname(ve,long)          -> if long then AsmX86Utils.pp_instr_velem_long ve else AsmX86Utils.pp_instr_velem ve 
    | PP_viname2(ve1, ve2) -> Printf.sprintf "%s%s" (AsmX86Utils.pp_instr_velem ve1) (AsmX86Utils.pp_instr_velem ve2)
    | PP_ct ct       -> AsmX86Utils.pp_ct (match ct with Condt ct -> ct | _ -> assert false)
  


  let pp_name_ext pp_op =
    Format.sprintf "%s%s" pp_op.pp_aop_name (pp_ext pp_op.pp_aop_ext)

  let build_align fname = 
    [Instr (".p2align", ["5"])]
  
  let build_label (_:Label.label_kind) (pos:BinNums.positive) (name:string) =
    [Label (make_label name pos)]

  let build_storelabel dst lbl fname = 
    [Instr (BP.string_of_storelabel fname dst lbl,[])]

  let build_jmp (fname,lbl) fname =
    [Instr( "jmp", [(AsmTargetUtils.string_of_label fname lbl)])]

  let build_jmpi lbl fname =
    [Instr( "jmp", [])]

  let build_jcc lbl cond fname =
    let iname = Format.asprintf "j%s" (AsmX86Utils.pp_ct cond) in
    [Instr(iname, [AsmTargetUtils.string_of_label fname lbl])]

  let build_jal reg lbl fname = 
    assert false (* Need to explain why*)

  let build_call lbl fname = 
    [Instr("call", [pp_remote_label lbl])]
  
  let build_poppc fname = 
    [Instr("ret", [])]

  let build_syscall op fname = 
    [Instr("call", [pp_syscall op])]

  let build_asmop op args string =
    let id = instr_desc X86_decl.x86_decl X86_instr_decl.x86_op_decl (None, op) in
    let pp = id.id_pp_asm args in
    let name = pp_name_ext pp in
    let args = List.map (string_of_asm_arg) pp.pp_aop_args in
    [Instr(name, args)]
  

  let build_function_header f = []
  (** 
  Asm data segment build functions
  *)
  let build_data_segment gd names = 
    if gd = [] then []
    else 
      [
        Header (".data", []);
        Header (".p2align", [AsmTargetUtils.align Wsize.U256]);
      ]

  let build_program_header prog = 
    [
      Header (".intel_syntax", ["noprefix"]);
      Header (".text", []);
      Header (".p2align", ["5"]);
    ]

end