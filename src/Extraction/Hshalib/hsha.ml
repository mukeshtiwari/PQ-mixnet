(* SHA-256 of a byte list (entries in [0, 255], as zarith integers) by HACL*'s verified implementation.
   The target of the extraction of ExecHash.sha256 (Extract.v). Raises Invalid_argument on a non-byte entry. *)
let hash (m : Z.t list) : Z.t list =
  let b = Bytes.create (List.length m) in
  List.iteri (fun i z ->
      if Z.sign z < 0 || Z.gt z (Z.of_int 255) then invalid_arg "sha256: not a byte"
      else Bytes.unsafe_set b i (Char.unsafe_chr (Z.to_int z))) m;
  let d = Hacl_star.Hacl.SHA2_256.hash b in
  List.init 32 (fun i -> Z.of_int (Char.code (Bytes.get d i)))
