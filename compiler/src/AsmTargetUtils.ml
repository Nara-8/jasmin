open Wsize


let align_of_ws =
  function
  | Wsize.U8 -> 0
  | Wsize.U16 -> 1
  | Wsize.U32 -> 2
  | Wsize.U64 -> 3
  | Wsize.U128 -> 4
  | Wsize.U256 -> 5



let align ws = 
  Format.asprintf "%d" (align_of_ws ws)


let string_of_label name p =
  Format.asprintf "L%s$%d" (PrintCommon.escape name) (Conv.int_of_pos p)

let mangle (x : string) = "_" ^ x
 