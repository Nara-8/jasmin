open Wsize
open Utils

 
type rsize = [ `U8 | `U16 | `U32 | `U64 ]

exception InvalidRegSize of Wsize.wsize
  
  
let iwidth = 4
  
let pp_gen (fmt : Format.formatter) = function
  | `Label lbl ->
      Format.fprintf fmt "%s:" lbl
  | `Instr (s, []) ->
      Format.fprintf fmt "\t%s" s
  | `Instr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s"
        iwidth s (String.join ", " args)

let pp_gens (fmt : Format.formatter) xs =
  List.iter (Format.fprintf fmt "%a\n%!" pp_gen) xs

type lreg =
  | RNumeric of int
  | RAlpha   of char
  | RSpecial of [`RStack | `RBase | `RSrcIdx | `RDstIdx]

let lreg_of_reg (reg:X86_decl.register) =
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

(* -------------------------------------------------------------------- *)
let rsize_of_wsize (ws : Wsize.wsize) =
  match ws with
  | U8  -> `U8
  | U16 -> `U16
  | U32 -> `U32
  | U64 -> `U64
  | _   -> raise (InvalidRegSize ws)

let pp_register ~(reg_pre:string) (ws : rsize) (reg:X86_decl.register) =
  let ssp = function
    | `RStack  -> "sp"
    | `RBase   -> "bp"
    | `RSrcIdx -> "si"
    | `RDstIdx -> "di" 
  in
  let s = 
    match lreg_of_reg reg, ws with
    | RNumeric i, `U8  -> Format.sprintf "r%d%s" i "b"
    | RNumeric i, `U16 -> Format.sprintf "r%d%s" i "w"
    | RNumeric i, `U32 -> Format.sprintf "r%d%s" i "d"
    | RNumeric i, `U64 -> Format.sprintf "r%d%s" i ""
    | RAlpha c  , `U8  -> Format.sprintf "%s%c%s" ""  c "l"
    | RAlpha c  , `U16 -> Format.sprintf "%s%c%s" ""  c "x"
    | RAlpha c  , `U32 -> Format.sprintf "%s%c%s" "e" c "x"
    | RAlpha c  , `U64 -> Format.sprintf "%s%c%s" "r" c "x"
    | RSpecial x, `U8  -> Format.sprintf "%s%s%s" ""  (ssp x) "l"
    | RSpecial x, `U16 -> Format.sprintf "%s%s%s" ""  (ssp x) ""
    | RSpecial x, `U32 -> Format.sprintf "%s%s%s" "e" (ssp x) ""
    | RSpecial x, `U64 -> Format.sprintf "%s%s%s" "r" (ssp x) "" 
  in
  Printf.sprintf "%s%s" reg_pre s   

  let pp_register_ext ~(reg_pre:string) (_ws: Wsize.wsize) (r: X86_decl.register_ext) : string =
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
let pp_xmm_register ~(reg_pre:string) (ws: Wsize.wsize) (r: X86_decl.xmm_register) : string =
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
  

let pp_ct (ct : X86_decl.condt) =
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
  | Wsize.U8 -> 0
  | Wsize.U16 -> 1
  | Wsize.U32 -> 2
  | Wsize.U64 -> 3
  | Wsize.U128 -> 4
  | Wsize.U256 -> 5

let pp_align ws =
  let n = align_of_ws ws in
  Format.sprintf "%d" n

(* ----------------------------------------------------------------------- *)



let pp_instr_wsize (ws : Wsize.wsize) =
  match ws with
  | Wsize.U8  -> "b"
  | Wsize.U16 -> "w"
  | Wsize.U32 -> "l"
  | Wsize.U64 -> "q"
  | _   -> raise (InvalidRegSize ws)

let pp_instr_velem =
  function
  | Wsize.VE8 -> "b"
  | Wsize.VE16 -> "w"
  | Wsize.VE32 -> "d"
  | Wsize.VE64 -> "q"

let pp_instr_velem_long =
  function
  | Wsize.VE8 -> "bw"
  | Wsize.VE16 -> "wd"
  | Wsize.VE32 -> "dq"
  | Wsize.VE64 -> "qdq"
