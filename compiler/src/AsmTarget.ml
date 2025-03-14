
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
