(* fpdecprove: the decryption prover extracted from Rocq (ExecDecProve.v: xdec_prove).

     fpdecprove N tau base kdig C1 C2 qbits STATEMENT WITNESS OUT [COINS]

   Writes the proof in the byte format read by fpdecverify (ExecDec.v: xdec_parse); exit 0 on
   success, 1 if the prover gives up (a challenge was zero or could not be drawn), 2 on usage errors.

   STATEMENT: the format of fpdecverify (N, tau as 4-byte big-endian integers, then a, b, u_1..u_tau,
   t_1..t_tau, N coefficients of 10 bytes each).
   WITNESS (this driver's format): s, e (N coefficients each), then E_1..E_tau (N each), every
   coefficient as 10 bytes, reduced mod q.
   COINS (optional): as for fpprove, a 4-byte count, that many 10-byte integers mod q, a 4-byte count,
   that many 16-byte salts. Without COINS the coins are read from /dev/urandom.

   The code parameters, evaluation points, noise offset and transcript tag are computed as in
   fpdecverify; this driver is not verified. *)

let q = Z.of_string "302231454903657394339841"
let two_adicity = 24
let p_plain = 2

let env_int name default =
  match Sys.getenv_opt name with Some s -> int_of_string s | None -> default

let prox_div = env_int "FP_PROX_DIV" 3
let rate_inv = env_int "FP_RATE_INV" 4

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
  let poly () = let p = List.init n (fun i -> be_int s (!pos + 10 * i) 10) in pos := !pos + 10 * n; p in
  let a = poly () in let b = poly () in
  let us = List.init tau (fun _ -> poly ()) in
  let ts = List.init tau (fun _ -> poly ()) in
  (n, tau, a, b, us, ts)

let parse_witness s n tau =
  if String.length s <> (2 + tau) * n * 10 then failwith "witness: wrong length";
  let pos = ref 0 in
  let poly () = let p = List.init n (fun i -> be_int s (!pos + 10 * i) 10) in pos := !pos + 10 * n; p in
  let sk = poly () in let e = poly () in
  let ee = List.init tau (fun _ -> poly ()) in
  (sk, e, ee)

let parse_coins s =
  let nz = Z.to_int (be_int s 0 4) in
  let zs = List.init nz (fun i -> be_int s (4 + 10 * i) 10) in
  let p = 4 + 10 * nz in
  let ns = Z.to_int (be_int s p 4) in
  let ss = List.init ns (fun i -> bytes_of (String.sub s (p + 4 + 16 * i) 16)) in
  if String.length s <> p + 4 + 16 * ns then failwith "coins: wrong length";
  (zs, ss)

let urandom = lazy (open_in_bin "/dev/urandom")
let rand_bytes k = really_input_string (Lazy.force urandom) k
let rec rand_zq () =
  let v = Z.logand (be_int (rand_bytes 10) 0 10) (Z.sub (Z.shift_left Z.one 79) Z.one) in
  if Z.lt v q then v else rand_zq ()

let usage () = prerr_endline "usage: fpdecprove N tau base kdig C1 C2 qbits STATEMENT WITNESS OUT [COINS]"; exit 2

let () =
  match Array.to_list Sys.argv with
  | _ :: sn :: stau :: sbase :: skd :: sc1 :: sc2 :: sqb :: fst_ :: fwit :: fout :: rest ->
      let n = int_of_string sn and tau = int_of_string stau and base = int_of_string sbase
      and kd = int_of_string skd and c1 = int_of_string sc1 and c2 = int_of_string sc2
      and qbits = int_of_string sqb in
      let (ni, ti, a, b, us, ts) = parse_statement (read_file fst_) in
      if ni <> n || ti <> tau then (prerr_endline "statement does not match N, tau"; exit 2);
      let (sk, e, ee) = parse_witness (read_file fwit) n tau in
      let (kb, nb, nqb) = code_params c1 qbits and (ks, ns, nqs) = code_params c2 qbits in
      let n1 = log2i n and ell = log2i tau and lo1 = log2i c1 and lo2 = log2i c2 in
      let module P = Fpprovelib.Fpprove_core in
      let (zs, ss) = match rest with
        | [fc] -> parse_coins (read_file fc)
        | [] ->
            let nz = P.dzcoins_needed n1 ell lo1 lo2 kd base nqb nqs and nsalt = P.dscoins_needed nb ns in
            (List.init nz (fun _ -> rand_zq ()), List.init nsalt (fun _ -> bytes_of (rand_bytes 16)))
        | _ -> usage () in
      let coins = P.dcoins_of n1 ell lo1 lo2 kd base nb nqb ns nqs zs ss in
      let off = Z.div (Z.pow (Z.of_int base) kd) (Z.of_int 2) in
      let tag = Printf.sprintf "dec|N=%d|tau=%d|base=%d|kdig=%d|C1=%d|C2=%d|rate=%d|qbits=%d|prox=%d"
                  n tau base kd c1 c2 rate_inv qbits prox_div in
      (match P.xdec_prove n1 ell lo1 lo2 kd base nb nqb ns nqs (omega nb) (omega ns) (bytes_of tag)
               (Z.of_int p_plain) off a b us ts sk e ee coins with
       | Some prf ->
           let oc = open_out_bin fout in
           List.iter (fun x -> output_char oc (Char.chr (Z.to_int x))) prf;
           close_out oc; exit 0
       | None -> prerr_endline "prover: no proof"; exit 1)
  | _ -> usage ()
