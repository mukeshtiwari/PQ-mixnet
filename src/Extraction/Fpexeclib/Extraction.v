(* Extraction of the executable field arithmetic to OCaml. Z is mapped to
   zarith's arbitrary-precision integers, nat to OCaml int. *)
From Stdlib Require Import ZArith Extraction ExtrOcamlBasic ExtrOcamlZBigInt ExtrOcamlNatInt.
(* Bit operations on Z, realized by zarith (used by SHA-256 and the challenger, always with
   non-negative shift amounts). Trusted in the same way as the arithmetic of ExtrOcamlZBigInt. *)
Extract Constant Z.land => "Z.logand".
Extract Constant Z.lor => "Z.logor".
Extract Constant Z.lxor => "Z.logxor".
Extract Constant Z.lnot => "Z.lognot".
Extract Constant Z.shiftr => "(fun x n -> Z.shift_right x (Z.to_int n))".
Extract Constant Z.shiftl => "(fun x n -> Z.shift_left x (Z.to_int n))".
Extract Constant Z.even => "Z.is_even".

(* List functions realized by OCaml's standard library (OCaml >= 5.3), which is tail-recursive
   (tail-modulo-cons) where the extracted definitions are not. Same functions, same results; the
   extracted recursions are deep on tables of millions of entries, and OCaml 5 scans the whole stack
   at every minor collection, which made the extracted verifier quadratic in practice. Trusted in
   the same way as ExtrOcamlBasic. *)
Extract Constant length => "List.length".
Extract Constant app => "List.append".
Extract Constant List.map => "List.map".
Extract Constant List.seq => "(fun s n -> List.init n (fun i -> s + i))".
Extract Constant List.repeat => "(fun x n -> List.init n (fun _ -> x))".
Extract Constant List.firstn => "List.take".
Extract Constant List.concat => "List.concat".
Extract Constant List.flat_map => "List.concat_map".
Extract Constant List.fold_right => "(fun f a l -> List.fold_left (fun acc x -> f x acc) a (List.rev l))".
Extract Constant List.combine => "(fun l1 l2 -> let rec go a b acc = match a, b with x :: a', y :: b' -> go a' b' ((x, y) :: acc) | _ -> List.rev acc in go l1 l2 [])".
(* Arithmetic of the Nat module on OCaml int, as ExtrOcamlNatInt does for the top-level nat operations.
   Extracted, these recurse once per unit (Nat.pow 2 20 makes about a million calls), and N = 2^n1 is
   recomputed at every use. All values here stay far below 2^62. Trusted in the same way as ExtrOcamlNatInt. *)
Extract Constant Nat.add => "(+)".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.sub => "(fun n m -> Stdlib.max 0 (n - m))".
Extract Constant Nat.pow => "(fun b e -> let rec go acc e = if e = 0 then acc else go (acc * b) (e - 1) in go 1 e)".

From Examples Require Import ExecFFT ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecDec ExecMerkle.

(* SHA-256 on byte lists by HACL*'s formally verified implementation (opam package hacl-star). Inputs are
   always byte lists here; the wrapper (src/Extraction/Hshalib/hsha.ml) raises on any entry outside [0, 255] instead of hashing something else.
   The Rocq definition sha256_spec is extracted as well and cross-checked (Unverified/cross_field.py). *)
Extract Constant ExecHash.sha256 => "Hsha.hash".

Extraction "fpexec.ml" xadd xsub xneg xmul xinv xint xeqb xeq_eval xzval xeq_table xinterp xsc_verify xlo_vec xhi_coefs sha256 sha256_spec fs_init fs_absorb get_F get_I leaf_hash root_from xclaims9 xaccO xderive xrho_r xmle xmix_verify xdec_verify xdec_verify_bytes mroot mpath xenc_row.
