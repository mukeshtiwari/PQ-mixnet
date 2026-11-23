(* fpprove: the shuffle prover extracted from Rocq (ExecProve.v: xmix_prove).

     fpprove [--text] N tau C1 C2 qbits INSTANCE WITNESS OUT [COINS]

   Writes the proof (mix_proof.py: mix_serialize format) to OUT; exit 0 on success, 1 if the
   prover gives up (a challenge could not be drawn), 2 on usage errors.
   With --text it also writes OUT.txt: the same proof as numbers, one labelled section per part
   (Z_q entries in decimal; a GF(q^2) element a + b t as "a b"; hashes and salts in hex). The text
   is produced by decoding OUT with the verifier's extracted parser (xmix_parse), so it shows
   exactly what a verifier reads. OUT.txt is for reading only; the verifiers take the binary OUT.

   WITNESS (this driver's format; there is no witness format elsewhere): sigma as tau 4-byte
   big-endian integers, then r, e1, e2, each as tau polynomials of N coefficients, 10 bytes
   each (mod q).
   COINS (optional; Unverified/cross_prove.py writes it to replay mix_prove's draws): a 4-byte
   count, that many 10-byte integers mod q, a 4-byte count, that many 16-byte salts.
   Without COINS the coins are read from /dev/urandom (integers mod q by rejection sampling).

   The code parameters, evaluation points and transcript tag are computed as in fpverify.ml;
   this driver is not verified. *)

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

let parse_instance s =
  let n = Z.to_int (be_int s 0 4) and tau = Z.to_int (be_int s 4 4) in
  if String.length s <> 8 + (2 + 4 * tau) * n * 10 then failwith "instance: wrong length";
  let pos = ref 8 in
  let poly () = let p = List.init n (fun i -> be_int s (!pos + 10 * i) 10) in pos := !pos + 10 * n; p in
  let a = poly () in let b = poly () in
  let cin = List.init tau (fun _ -> let c0 = poly () in let c1 = poly () in (c0, c1)) in
  let cout = List.init tau (fun _ -> let c0 = poly () in let c1 = poly () in (c0, c1)) in
  (n, tau, a, b, cin, cout)

let parse_witness s n tau =
  if String.length s <> 4 * tau + 3 * tau * n * 10 then failwith "witness: wrong length";
  let sigma = List.init tau (fun i -> be_int s (4 * i) 4) in
  let pos = ref (4 * tau) in
  let poly () = let p = List.init n (fun i -> be_int s (!pos + 10 * i) 10) in pos := !pos + 10 * n; p in
  let tbl () = List.init tau (fun _ -> poly ()) in
  let r = tbl () in let e1 = tbl () in let e2 = tbl () in
  (sigma, r, e1, e2)

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

let hex bs = String.concat "" (List.map (fun x -> Printf.sprintf "%02x" (Z.to_int x)) bs)
let fe (a, b) = Z.to_string a ^ " " ^ Z.to_string b

(* the proof as numbers, from the verifier's parse of the bytes *)
let write_text path n tau c1 c2 qbits (kb, nb, nqb) (ks, ns, nqs) prf =
  let n1 = log2i n and ell = log2i tau and lo1 = log2i c1 and lo2 = log2i c2 in
  match Fpprovelib.Fpprove_core.xmix_parse n1 ell lo1 lo2 kb nb nqb ks ns nqs prf with
  | None -> prerr_endline "text: the proof does not parse"; exit 1
  | Some p ->
      let oc = open_out path in
      let pr fmt = Printf.fprintf oc fmt in
      pr "# shuffle proof as numbers: N=%d tau=%d C1=%d C2=%d qbits=%d, %d bytes\n" n tau c1 c2 qbits (List.length prf);
      pr "# Z_q entries in decimal; a GF(q^2) element a + b t (t^2 = 3) as \"a b\"; hashes and salts in hex\n";
      pr "root_big %s\nroot_small1 %s\nroot_small2 %s\n" (hex p.qrB) (hex p.qr1) (hex p.qr2);
      let vec name v = pr "%s (%d elements)\n" name (List.length v); List.iter (fun x -> pr "  %s\n" (fe x)) v in
      let msgs name ms =
        pr "%s (%d rounds)\n" name (List.length ms);
        List.iteri (fun j ev -> pr "  round %d: %s\n" j (String.concat "  " (List.map fe ev))) ms in
      vec "G (mask sums of sumchecks A, B, C)" p.qG;
      msgs "sumcheck A messages (values at 0, 2, .., d)" p.qmA;
      vec "evaluations after A (U, Uhat, s, H)" p.qevA;
      msgs "sumcheck B messages" p.qmB;
      msgs "sumcheck C messages" p.qmC;
      vec "evaluations after C (w1, w2, w3 at r_z)" p.qevC;
      pr "mu %s\n" (fe p.qmu);
      vec "slot vector S1 (big matrix)" p.qv1; vec "slot vector S2 (big matrix)" p.qv2;
      vec "slot vector S3 (small matrix)" p.qv3; vec "slot vector S4 (small matrix)" p.qv4;
      vec "proximity vector, big matrix" p.qpvB; vec "proximity vector, small matrix" p.qpvS;
      let cols name cs =
        pr "%s (%d columns)\n" name (List.length cs);
        List.iteri (fun c batches ->
          List.iteri (fun bi ((e, salt), path) ->
            pr "  column %d batch %d: %d entries\n    %s\n    salt %s\n    path %s\n" c bi (List.length e)
              (String.concat " " (List.map Z.to_string e)) (hex salt) (String.concat " " (List.map hex path))) batches) cs in
      cols "opened columns, big matrix" p.qcB;
      cols "opened columns, small matrix" p.qcS;
      close_out oc

let () =
  let argv = Array.to_list Sys.argv in
  let text = List.mem "--text" argv in
  let argv = List.filter (fun a -> a <> "--text") argv in
  match argv with
  | _ :: sn :: stau :: sc1 :: sc2 :: sqb :: finst :: fwit :: fout :: rest ->
      let n = int_of_string sn and tau = int_of_string stau and c1 = int_of_string sc1
      and c2 = int_of_string sc2 and qbits = int_of_string sqb in
      let (ni, ti, a, b, cin, cout) = parse_instance (read_file finst) in
      if ni <> n || ti <> tau then (prerr_endline "instance does not match N, tau"; exit 2);
      let (sigma, r, e1, e2) = parse_witness (read_file fwit) n tau in
      let (kb, nb, nqb) = code_params c1 qbits and (ks, ns, nqs) = code_params c2 qbits in
      let n1 = log2i n and ell = log2i tau and lo1 = log2i c1 and lo2 = log2i c2 in
      let (zs, ss) = match rest with
        | [fc] -> parse_coins (read_file fc)
        | [] ->
            let nz = Fpprovelib.Fpprove_core.zcoins_needed n1 ell lo1 lo2 nqb nqs
            and nsalt = Fpprovelib.Fpprove_core.scoins_needed nb ns in
            (List.init nz (fun _ -> rand_zq ()), List.init nsalt (fun _ -> bytes_of (rand_bytes 16)))
        | _ -> prerr_endline "usage: fpprove [--text] N tau C1 C2 qbits INSTANCE WITNESS OUT [COINS]"; exit 2 in
      let coins = Fpprovelib.Fpprove_core.coins_of n1 ell lo1 lo2 nb nqb ns nqs zs ss in
      let tag = Printf.sprintf "mix|N=%d|tau=%d|C1=%d|C2=%d|rate=%d|qbits=%d|prox=%d" n tau c1 c2 rate_inv qbits prox_div in
      (match Fpprovelib.Fpprove_core.xmix_prove n1 ell lo1 lo2 nb nqb ns nqs (omega nb) (omega ns) (bytes_of tag)
               (Z.of_int p_plain) a b cin cout sigma r e1 e2 coins with
       | Some prf ->
           let oc = open_out_bin fout in
           List.iter (fun x -> output_char oc (Char.chr (Z.to_int x))) prf;
           close_out oc;
           if text then write_text (fout ^ ".txt") n tau c1 c2 qbits (kb, nb, nqb) (ks, ns, nqs) prf;
           exit 0
       | None -> prerr_endline "prover: no proof"; exit 1)
  | _ -> prerr_endline "usage: fpprove [--text] N tau C1 C2 qbits INSTANCE WITNESS OUT [COINS]"; exit 2
