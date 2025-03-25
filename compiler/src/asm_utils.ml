open PrintCommon
open Arch_decl
open Prog
open Var0

let global_datas_label = "glob_data"

 let pp_syscall (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

let string_of_label name p = Format.asprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

let pp_label n lbl = string_of_label n lbl

let pp_remote_label (fn, lbl) =
  string_of_label fn.fn_name lbl

let mangle x = Format.asprintf "_%s" x

let pp_brace s = Format.asprintf "{%s}" s