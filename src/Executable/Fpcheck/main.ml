(* Driver for the cross-check of the extracted field arithmetic against
   fp_core.py. Reads one request per line from stdin, prints one answer per
   line. Numbers are decimal.

     add|sub|mul a0 a1 b0 b1      ->  r0 r1
     neg|inv a0 a1                ->  r0 r1
     int c                        ->  r0 r1
     eqb a0 a1 b0 b1              ->  0|1
     eqeval n  r_0 .. r_(n-1)  s_0 .. s_(n-1)     (each element two numbers)  ->  r0 r1
     zval n  r_0 .. r_(n-1)                       ->  r0 r1
     eqtable n  r_0 .. r_(n-1)                    ->  2^n elements, all on one line
     interp n  v_0 .. v_(n-1)  x                  ->  r0 r1
     lovec|hicoefs lo n  x_0 .. x_(n-1)            ->  elements on one line
     sha HEX                                      ->  HEX        (HEX "-" is the empty string)
     leaf SALTHEX n e_1 .. e_n                    ->  HEX
     root LEAFHEX j k SIB_1 .. SIB_k              ->  HEX
     fs DOMAINHEX  (A LABEL DATA | F NAME n | I NAME n bound)*   ->  the drawn values, one line
     claims n1 ell lo1 lo2 SO  la dA..  lb dB..  lc dC..  invN rhoB mrp1 mrp2 mrp3  r.. ry.. rz..
                                                  ->  per claim: "C k" then k terms "slot row c0 c1 L lv.."
     open ...                                     ->  0|1   (opening checks; format in cross_field.py: open_request)
     derive ...                                   ->  9 values | reject   (format: cross_field.py: derive_request)
     rhor a.. b.. ru.. rv.. (each a list: length then pairs)  ->  rho' first block
     mle tbl.. r..                                ->  r0 r1
     decverify ...                                ->  1|0   (format: cross_field.py: decverify_request)
     mtree d j LEAFHEX_1 .. LEAFHEX_(2^d)          ->  ROOTHEX PATHHEX..
     encrow om n k m_1 .. m_k                     ->  the n codeword entries
     scv m claim  (d_j  e_1 .. e_dj  r_j) for j < m   ->  c0 c1  |  reject              *)

let z = Z.of_string
let show (a, b) = Printf.printf "%s %s\n" (Z.to_string a) (Z.to_string b)

let rec take_pairs n l =
  if n = 0 then ([], l)
  else match l with
    | a :: b :: rest -> let (ps, rest') = take_pairs (n - 1) rest in ((z a, z b) :: ps, rest')
    | _ -> failwith "short line"

let of_hex h =
  if h = "-" then []
  else List.init (String.length h / 2) (fun i -> Z.of_string ("0x" ^ String.sub h (2 * i) 2))
let to_hex l =
  if l = [] then "-" else String.concat "" (List.map (fun b -> Printf.sprintf "%02x" (Z.to_int b)) l)

let rec fs_ops ch acc = function
  | "A" :: lab :: data :: rest -> fs_ops (Fpexeclib.Fpexec.fs_absorb ch (of_hex lab) (of_hex data)) acc rest
  | "F" :: name :: n :: rest ->
      (match Fpexeclib.Fpexec.get_F ch (of_hex name) (int_of_string n) with
       | Some (xs, ch') ->
           fs_ops ch' (List.rev_append (List.concat_map (fun (a, b) -> [Z.to_string a; Z.to_string b]) xs) acc) rest
       | None -> failwith "get_F: out of fuel")
  | "I" :: name :: n :: bound :: rest ->
      (match Fpexeclib.Fpexec.get_I ch (of_hex name) (int_of_string n) (z bound) with
       | Some (vs, ch') -> fs_ops ch' (List.rev_append (List.map Z.to_string vs) acc) rest
       | None -> failwith "get_I: out of fuel")
  | [] -> List.rev acc
  | _ -> failwith "bad fs script"

(* a token stream *)
let toks = ref []
let next () = match !toks with x :: r -> toks := r; x | [] -> failwith "short open"
let ni () = int_of_string (next ())
let nz () = z (next ())
let nf () = let a = nz () in let b = nz () in (a, b)
let nlist f = let k = ni () in List.init k (fun _ -> f ())

let open_request rest =
  toks := rest;
  let kB = ni () in let kS = ni () in let omB = nf () in let omS = nf () in let so = ni () in
  let svB = nlist ni in let svS = nlist ni in
  let slots = List.map (fun v ->
      let kd = ni () in let fr = ni () in let lt = nlist nf in
      let mcb = nlist (fun () -> let r = ni () in let w = nf () in (r, w)) in
      (v, (kd = 1, fr, lt, mcb))) (svB @ svS) in
  let find v = List.assoc v slots in
  let rwsB = nlist ni in let rwsS = nlist ni in
  let pmB0 = ni () in let pmB1 = ni () in let pmS0 = ni () in let pmS1 = ni () in
  let cls = nlist (fun () -> nlist (fun () ->
      let sl = ni () in let row = ni () in let c = nf () in let lv = nlist nf in (((sl, row), c), lv))) in
  let vals = nlist nf in let kp = nlist nf in let c = nf () in
  let gamB = nlist nf in let gamS = nlist nf in let jB = nlist ni in let jS = nlist ni in
  let mu = nf () in
  let ubs = List.map (fun v -> (v, nlist nf)) (svB @ svS) in
  let pvB = nlist nf in let pvS = nlist nf in
  let colsB = List.map (fun j -> (j, Array.of_list (nlist nz))) jB in
  let colsS = List.map (fun j -> (j, Array.of_list (nlist nz))) jS in
  let xe i j =
    if i < so then ((List.assoc j colsB).(i), Z.zero) else ((List.assoc j colsS).(i - so), Z.zero) in
  let tg = (Z.zero, Z.one) in
  let xmp r0 r1 j = Fpexeclib.Fpexec.xadd (xe r0 j) (Fpexeclib.Fpexec.xmul tg (xe r1 j)) in
  let kind v = (match find v with (k, _, _, _) -> k) and frow v = (match find v with (_, f, _, _) -> f) in
  let ltx v = (match find v with (_, _, l, _) -> l) and mcb v = (match find v with (_, _, _, m) -> m) in
  let ub v = try List.assoc v ubs with Not_found -> [] in
  (* code lengths 0: every column value by Horner, as before the NTT path (the verifiers use the real lengths) *)
  Fpexeclib.Fpexec.xaccO xe omB omS 0 0 kB kS (xmp pmB0 pmB1) (xmp pmS0 pmS1) rwsB rwsS kind frow ltx mcb svB svS cls vals
    kp c gamB gamS jB jS mu ub pvB pvS

let derive_request rest =
  toks := rest;
  let n1 = ni () in let ell = ni () in
  let a = nlist nf in let b = nlist nf in let pp = nf () in
  let ctxs () = nlist (fun () -> let c0 = nlist nf in let c1 = nlist nf in (c0, c1)) in
  let cin = ctxs () in let cout = ctxs () in
  let ru = nlist nf in let rv = nlist nf in let al = nf () in let be = nf () in
  let tc = nlist nf in let kA = nlist nf in let rA = nlist nf in let rhoB = nf () in let ry = nlist nf in
  let tz = nlist nf in let kC = nlist nf in let rz = nlist nf in
  let gA = nf () in let gB = nf () in let gC = nf () in
  let mA = nlist (fun () -> nlist nf) in
  let u = nf () in let uh = nf () in let sv = nf () in let hd = nf () in
  let mB = nlist (fun () -> nlist nf) in let mC = nlist (fun () -> nlist nf) in
  let w1 = nf () in let w2 = nf () in let w3 = nf () in
  ignore (a, b, pp); Fpexeclib.Fpexec.xderive cin cout n1 ell ru rv al be tc kA rA rhoB ry tz kC rz gA gB gC mA u uh sv hd mB mC w1 w2 w3

let decverify_request rest =
  toks := rest;
  let n1 = ni () in let ell = ni () in let lo1 = ni () in let kd = ni () in let base = ni () in
  let kB = ni () in let nB = ni () in let nqB = ni () in let kS = ni () in let nS = ni () in let nqS = ni () in
  let omB = nz () in let omS = nz () in let tag = of_hex (next ()) in let pp = nz () in let off = nz () in
  let a = nlist nz in let b = nlist nz in let us = nlist (fun () -> nlist nz) in let ts = nlist (fun () -> nlist nz) in
  let rb = of_hex (next ()) in let rs = of_hex (next ()) in
  let g = nlist nf in let mG = nlist (fun () -> nlist nf) in let zG = nlist nf in
  let mT = nlist (fun () -> nlist nf) in let zT = nlist nf in let mu = nf () in
  let v1 = nlist nf in let v2 = nlist nf in let vs = nlist nf in let ve = nlist nf in let vm = nlist nf in
  let pvB = nlist nf in let pvS = nlist nf in
  let cols () = nlist (fun () -> nlist (fun () ->
      let e = nlist nz in let salt = of_hex (next ()) in let path = nlist (fun () -> of_hex (next ())) in ((e, salt), path))) in
  let colsB = cols () in let colsS = cols () in
  Fpexeclib.Fpexec.xdec_verify n1 ell lo1 kd base kB nB nqB kS nS nqS omB omS tag pp off a b us ts
    rb rs g mG zG mT zT mu v1 v2 vs ve vm pvB pvS colsB colsS

let () =
  try
    while true do
      let line = input_line stdin in
      match String.split_on_char ' ' (String.trim line) with
      | ["add"; a0; a1; b0; b1] -> show (Fpexeclib.Fpexec.xadd (z a0, z a1) (z b0, z b1))
      | ["sub"; a0; a1; b0; b1] -> show (Fpexeclib.Fpexec.xsub (z a0, z a1) (z b0, z b1))
      | ["mul"; a0; a1; b0; b1] -> show (Fpexeclib.Fpexec.xmul (z a0, z a1) (z b0, z b1))
      | ["neg"; a0; a1] -> show (Fpexeclib.Fpexec.xneg (z a0, z a1))
      | ["inv"; a0; a1] -> show (Fpexeclib.Fpexec.xinv (z a0, z a1))
      | ["int"; c] -> show (Fpexeclib.Fpexec.xint (z c))
      | ["eqb"; a0; a1; b0; b1] ->
          print_endline (if Fpexeclib.Fpexec.xeqb (z a0, z a1) (z b0, z b1) then "1" else "0")
      | "eqeval" :: n :: rest ->
          let n = int_of_string n in
          let (r, rest) = take_pairs n rest in
          let (s, _) = take_pairs n rest in
          show (Fpexeclib.Fpexec.xeq_eval r s)
      | "zval" :: n :: rest ->
          let (r, _) = take_pairs (int_of_string n) rest in
          show (Fpexeclib.Fpexec.xzval r)
      | "eqtable" :: n :: rest ->
          let (r, _) = take_pairs (int_of_string n) rest in
          print_endline (String.concat " "
            (List.map (fun (a, b) -> Z.to_string a ^ " " ^ Z.to_string b) (Fpexeclib.Fpexec.xeq_table r)))
      | ("lovec" | "hicoefs") as cmd :: lo :: n :: rest ->
          let (x, _) = take_pairs (int_of_string n) rest in
          let f = if cmd = "lovec" then Fpexeclib.Fpexec.xlo_vec else Fpexeclib.Fpexec.xhi_coefs in
          print_endline (String.concat " "
            (List.map (fun (a, b) -> Z.to_string a ^ " " ^ Z.to_string b) (f (int_of_string lo) x)))
      | "interp" :: n :: rest ->
          let (v, rest) = take_pairs (int_of_string n) rest in
          let (x, _) = take_pairs 1 rest in
          show (Fpexeclib.Fpexec.xinterp v (List.hd x))
      | "scv" :: m :: rest ->
          let m = int_of_string m in
          let (cl, rest) = take_pairs 1 rest in
          let rec rounds k l =
            if k = 0 then ([], [])
            else match l with
              | d :: l' ->
                  let (ev, l'') = take_pairs (int_of_string d) l' in
                  let (r, l''') = take_pairs 1 l'' in
                  let (evs, rs) = rounds (k - 1) l''' in
                  (ev :: evs, List.hd r :: rs)
              | [] -> failwith "short scv" in
          let (msgs, chals) = rounds m rest in
          (match Fpexeclib.Fpexec.xsc_verify msgs chals (List.hd cl) with
           | Some c -> show c
           | None -> print_endline "reject")
      | "claims" :: n1 :: ell :: lo1 :: lo2 :: so :: rest ->
          let i = int_of_string in
          let n1 = i n1 and ell = i ell in
          let ints k l = (List.map i (List.filteri (fun j _ -> j < k) l), List.filteri (fun j _ -> j >= k) l) in
          let la, rest = (match rest with x :: r -> (i x, r) | _ -> failwith "claims") in
          let dA, rest = ints la rest in
          let lb, rest = (match rest with x :: r -> (i x, r) | _ -> failwith "claims") in
          let dB, rest = ints lb rest in
          let lc, rest = (match rest with x :: r -> (i x, r) | _ -> failwith "claims") in
          let dC, rest = ints lc rest in
          let (sc, rest) = take_pairs 5 rest in
          let nth k = List.nth sc k in
          let (r, rest) = take_pairs ell rest in
          let (ry, rest) = take_pairs n1 rest in
          let (rz, _) = take_pairs (n1 + ell) rest in
          let cls = Fpexeclib.Fpexec.xclaims9 n1 ell (i lo1) (i lo2) (i so) dA dB dC (nth 0) r ry rz (nth 1) (nth 2) (nth 3) (nth 4) in
          let pr (a, b) = Z.to_string a ^ " " ^ Z.to_string b in
          let term (((sl, row), c), lv) =
            String.concat " " ([string_of_int sl; string_of_int row; pr c; string_of_int (List.length lv)] @ List.map pr lv) in
          print_endline (String.concat " "
            (List.map (fun cl -> String.concat " " (("C " ^ string_of_int (List.length cl)) :: List.map term cl)) cls))
      | "derive" :: rest ->
          (match derive_request rest with
           | Some vs -> print_endline (String.concat " " (List.map (fun (a, b) -> Z.to_string a ^ " " ^ Z.to_string b) vs))
           | None -> print_endline "reject")
      | "rhor" :: rest ->
          toks := rest;
          let a = nlist nf in let b = nlist nf in let ru = nlist nf in let rv = nlist nf in
          print_endline (String.concat " "
            (List.map (fun (x, y) -> Z.to_string x ^ " " ^ Z.to_string y) (Fpexeclib.Fpexec.xrho_r a b ru rv)))
      | "mle" :: rest ->
          toks := rest; let t = nlist nf in let r = nlist nf in show (Fpexeclib.Fpexec.xmle t r)
      | "decverify" :: rest -> print_endline (if decverify_request rest then "1" else "0")
      | "mtree" :: d :: j :: leaves ->
          let ls = List.map of_hex leaves in
          let d = int_of_string d and j = int_of_string j in
          print_endline (String.concat " "
            (to_hex (Fpexeclib.Fpexec.mroot d ls) :: List.map to_hex (Fpexeclib.Fpexec.mpath d ls j)))
      | "encrow" :: om :: n :: k :: msg ->
          let msg = List.map z (List.filteri (fun i _ -> i < int_of_string k) msg) in
          print_endline (String.concat " "
            (List.map Z.to_string (Fpexeclib.Fpexec.xenc_row (z om) (int_of_string n) msg)))
      | "open" :: rest -> print_endline (if open_request rest then "1" else "0")
      | ["sha"; h] -> print_endline (to_hex (Fpexeclib.Fpexec.sha256 (of_hex h)))
      | ["shaspec"; h] -> print_endline (to_hex (Fpexeclib.Fpexec.sha256_spec (of_hex h)))
      | "leaf" :: salt :: n :: rest ->
          let es = List.map z (List.filteri (fun i _ -> i < int_of_string n) rest) in
          print_endline (to_hex (Fpexeclib.Fpexec.leaf_hash (of_hex salt) es))
      | "root" :: leaf :: j :: k :: rest ->
          let path = List.map of_hex (List.filteri (fun i _ -> i < int_of_string k) rest) in
          print_endline (to_hex (Fpexeclib.Fpexec.root_from (of_hex leaf) (z j) path))
      | "fs" :: dom :: ops -> print_endline (String.concat " " (fs_ops (Fpexeclib.Fpexec.fs_init (of_hex dom)) [] ops))
      | [""] -> ()
      | _ -> failwith ("bad request: " ^ line)
    done
  with End_of_file -> ()
