(* Import *)

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

let compile_printf (string_label : string) : text =
  pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq !%rdi !%rsi
  ++ movq (ilab string_label) !%rdi
  ++ movq (imm 0) !%rax
  ++ call "printf" ++ movq !%rbp !%rsp ++ popq rbp
