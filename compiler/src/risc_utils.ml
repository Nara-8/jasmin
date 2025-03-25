open PrintCommon
open Arch_decl
open Utils
open Prog
open Var0

let global_datas_label = "glob_data"

let string_of_label name p = Printf.sprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

let pp_label n lbl = string_of_label n lbl

let pp_remote_label (fn, lbl) =
  string_of_label fn.fn_name lbl

let hash_to_string (to_string : 'a -> string) =
  let tbl = Hashtbl.create 17 in
  fun r ->
     try Hashtbl.find tbl r
     with Not_found ->
       let s = to_string r in
       Hashtbl.add tbl r s;
       s

let pp_imm imm_pre imm = Format.asprintf "%s%s" imm_pre (Z.to_string imm)

let pp_rip_address (p : Ssralg.GRing.ComRing.sort) : string =
  Format.asprintf "%s+%a" global_datas_label Z.pp_print (Conv.z_of_int32 p)

let pp_register arch = hash_to_string arch.toS_r.to_string

let pp_reg_address (arch:('a,'b,'c,'d,'e)arch_decl) (arch_name:string) pp_reg_address_aux addr =
  match addr.ad_base with
  | None ->
      failwith (Format.asprintf "TODO_%s: pp_reg_address" arch_name)
  | Some r ->
      let base = pp_register arch r in
      let disp = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let disp =
        if Z.equal disp Z.zero then None else Some (Z.to_string disp)
      in
      let off = Option.map (pp_register arch) addr.ad_offset in
      let scal = Conv.z_of_nat addr.ad_scale in
      let scal =
        if Z.equal scal Z.zero then None else Some (Z.to_string scal)
      in
      pp_reg_address_aux base disp off scal

let pp_address arch arch_name pp_reg_address_aux addr =
  match addr with
  | Areg ra -> pp_reg_address arch arch_name pp_reg_address_aux ra
  | Arip r -> pp_rip_address r 

let pp_syscall (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

  let mangle x = Printf.sprintf "_%s" x

  let pp_brace s = Format.sprintf "{%s}" s