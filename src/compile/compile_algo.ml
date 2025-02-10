(* Import *)

open Compile_utils
open X86_64

(* Data *)

let get_label_data, new_label_data =
  let cpt = ref ~-1 in

  let gld () = Format.sprintf ".D%d" !cpt in

  let nld () =
    incr cpt;
    Format.sprintf ".D%d" !cpt
  in

  (gld, nld)

(* Printf *)

let compile_printf () : text =
  label label_print_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq !%rdi !%rsi
  ++ movq (ilab label_print_data) !%rdi
  ++ xorq !%rax !%rax ++ call "printf" ++ movq !%rbp !%rsp ++ popq rbp ++ ret
