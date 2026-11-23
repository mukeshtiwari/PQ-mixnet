(* fpdecverify: the decryption-proof verifier extracted from Rocq (ExecDec.v: xdec_verify_bytes).

     fpdecverify N tau base kdig C1 C2 qbits STATEMENT PROOF     exit 0: accepted, 1: rejected, 2: usage

   File formats of dec_proof.py: dec_stmt_serialize, dec_serialize. This driver computes the code
   parameters (fp_core.code_params), the evaluation points, the noise offset base^kdig / 2 and the
   transcript tag, reads the files, and calls the extracted function; it is not verified.
   FP_PROX_DIV and FP_RATE_INV are read as in fp_core.py. *)

let q = Z.of_string "302231454903657394339841"
let two_adicity = 24
let p_plain = 2

let env_int name default =
  match Sys.getenv_opt name with Some s -> int_of_string s | None -> default

let prox_div = env_int "FP_PROX_DIV" 3
let rate_inv = env_int "FP_RATE_INV" 4

(* fp_core.code_params *)
let code_params c qbits =
  let n = ref (rate_inv * c) and nq = ref 1 and result = ref None in
  while !result = None do
    let k = c + !nq in
    while (rate_inv / 2) * k > !n || !n - k < prox_div do n := 2 * !n done;
    let e = (!n - k) / prox_div in
    let need = int_of_float (Float.ceil (float_of_int qbits /. (-. Float.log2 (1.0 -. float_of_int e /. float_of_int !n)))) in
    if need <= !nq then result := Some (k, !n, !nq) else nq := need
  done;
  match !result with Some r -> r | None -> assert false

let root = Z.powm (Z.of_int 3) (Z.shift_right (Z.sub q Z.one) two_adicity) q
let omega n = Z.powm root (Z.of_int ((1 lsl two_adicity) / n)) q

let log2i n = let rec go k = if 1 lsl k >= n then k else go (k + 1) in go 0

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let bytes_of s = List.init (String.length s) (fun i -> Z.of_int (Char.code s.[i]))

let be_int s pos k =
  let r = ref Z.zero in
  for i = 0 to k - 1 do r := Z.add (Z.mul !r (Z.of_int 256)) (Z.of_int (Char.code s.[pos + i])) done; !r

let parse_statement s =
  if String.length s < 8 then failwith "statement: too short";
  let n = Z.to_int (be_int s 0 4) and tau = Z.to_int (be_int s 4 4) in
  if String.length s <> 8 + (2 + 2 * tau) * n * 10 then failwith "statement: wrong length";
  let pos = ref 8 in
  let poly () =
    let p = List.init n (fun i -> be_int s (!pos + 10 * i) 10) in
    if List.exists (fun v -> Z.geq v q) p then failwith "statement: entry not reduced";
    pos := !pos + 10 * n; p in
  let a = poly () in let b = poly () in
  let us = List.init tau (fun _ -> poly ()) in
  let ts = List.init tau (fun _ -> poly ()) in
  (n, tau, a, b, us, ts)

let () =
  match Array.to_list Sys.argv with
  | [_; sn; stau; sbase; skd; sc1; sc2; sqb; fst_; fproof] ->
      let n = int_of_string sn and tau = int_of_string stau and base = int_of_string sbase
      and kd = int_of_string skd and c1 = int_of_string sc1 and c2 = int_of_string sc2
      and qbits = int_of_string sqb in
      let (ni, ti, a, b, us, ts) =
        try parse_statement (read_file fst_) with Failure m -> (prerr_endline m; print_endline "reject"; exit 1) in
      if ni <> n || ti <> tau then (prerr_endline "statement does not match N, tau"; print_endline "reject"; exit 1);
      let (kb, nb, nqb) = code_params c1 qbits and (ks, ns, nqs) = code_params c2 qbits in
      let off = Z.div (Z.pow (Z.of_int base) kd) (Z.of_int 2) in
      let tag = Printf.sprintf "dec|N=%d|tau=%d|base=%d|kdig=%d|C1=%d|C2=%d|rate=%d|qbits=%d|prox=%d"
                  n tau base kd c1 c2 rate_inv qbits prox_div in
      let ok = Fpexeclib.Fpexec.xdec_verify_bytes (log2i n) (log2i tau) (log2i c1) kd base kb nb nqb ks ns nqs
                 (omega nb) (omega ns) (bytes_of tag) (Z.of_int p_plain) off a b us ts (bytes_of (read_file fproof)) in
      print_endline (if ok then "accept" else "reject");
      exit (if ok then 0 else 1)
  | _ -> prerr_endline "usage: fpdecverify N tau base kdig C1 C2 qbits STATEMENT PROOF"; exit 2
