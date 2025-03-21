
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

let iwidth = 4

type asm = asm_element list

let pp_header fmt name params = 
  match params with 
  | [] -> Format.fprintf fmt "\t%s\n" name
  | _ ->  Format.fprintf fmt "\t%-*s\t%s\n" iwidth name (String.concat ", " params)

let pp_label fmt name =
  Format.fprintf fmt "%s:\n" name

let pp_instr fmt name params = 
  match params with 
  | [] -> Format.fprintf fmt "\t%s\n" name (* In case there is no params, we do not print a tab*)
  | _ ->  Format.fprintf fmt "\t%-*s\t%s\n" iwidth name (String.concat ", " params)

let pp_comment fmt comment = 
  Format.fprintf fmt "// %s\n" comment

let pp_byte fmt byte = 
  Format.fprintf fmt "\t.byte\t%s\n" byte

let pp_dwarf fmt (dwarf:string list) = 
  List.iter (Format.fprintf fmt "\t%s\n") dwarf

let pp_asm_element fmt asm_element = 
  match asm_element with
  | Header (name, params) -> 
    pp_header fmt name params
  | Label name ->
    pp_label fmt name
  | Dwarf locs ->
    pp_dwarf fmt locs
  | Instr (name, params) ->
    pp_instr fmt name params
  | Comment content ->
    pp_comment fmt content
  | Byte data ->
    pp_byte fmt data
  
let pp_asm fmt asm = 
  List.iter (pp_asm_element fmt) asm

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