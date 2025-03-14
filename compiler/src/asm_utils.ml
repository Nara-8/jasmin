
open Prog
open Utils 
open PrintCommon
open Arch_decl 


type asm_element = 
| Header of string * string list
| Label of string
| Dwarf of string list
| Instr of string * string list
| Comment of string
| Byte of string


let mangle x = "_" ^ x
let escape = PrintCommon.escape

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

let string_of_register arch reg = hash_to_string arch.toS_r.to_string reg

let string_of_glob occurrences x =
  Hash.modify_def (-1) x.v_name Stdlib.Int.succ occurrences;
  let count =  Hash.find occurrences x.v_name in
  (* Adding the number of occurrences to the label to avoid names conflict *)
  let suffix = if count > 0 then Format.asprintf "$%d" count else "" in
  Format.asprintf "G$%s%s" (escape x.v_name) suffix


let format_glob_data globs names = 
    (* Creating a Hashtable to count occurrences of a label name*)
    let occurrences = Hash.create 42 in
    let names =
      List.map (fun ((x, _), p) -> (Conv.var_of_cvar x, Conv.z_of_cz p)) names
    in
    List.flatten
      (List.mapi
         (fun i b ->
           let b = Byte (Z.to_string (Conv.z_of_int8 b)) in
           match List.find (fun (_, p) -> Z.equal (Z.of_int i) p) names with
           | exception Not_found -> [ b ]
           | x, _ -> [ Label (string_of_glob occurrences x); b ])
         globs)