(* Executable SHA-256, the Fiat-Shamir challenger and Merkle paths of
   fp_core.py (H, FSChallenger, merkle_root_from, leaf_hash, ser_base,
   ser_f).

   Bytes are integers in [0, 256), byte strings are lists of them, 32-bit
   words are integers in [0, 2^32). SHA-256 follows FIPS 180-4, sections
   5.1.1 (padding), 6.2 (computation); the round constants are those of
   Utility/Sha256.v. Nothing is proven about the hash: it is outside the
   oracle model of the soundness theorems. It is checked on the four test
   vectors of Utility/Sha256.v (by computation, below) and against Python's
   hashlib on random inputs (Unverified/cross_field.py).

   The challenger is a state record; get_F and get_I return None only if a
   rejection-sampling loop exceeds its fuel (2^-1000 for get_F; for get_I
   it depends on how close n is to bound). *)

From Stdlib Require Import Utf8 ZArith List Lia String Ascii.
From Examples Require Import ConcreteField ExecField.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition bytes : Type := list Z.

(* ---------------------------------------------------------------------- *)
(* SHA-256 *)

Definition m32 : Z := 2 ^ 32.
Definition add32 (x y : Z) : Z := (x + y) mod m32.
Definition rotr (n x : Z) : Z := Z.lor (Z.shiftr x n) ((Z.shiftl x (32 - n)) mod m32).
Definition shr (n x : Z) : Z := Z.shiftr x n.
Definition chf (x y z : Z) : Z := Z.lxor (Z.land x y) (Z.land (Z.lnot x) z).
Definition majf (x y z : Z) : Z := Z.lxor (Z.lxor (Z.land x y) (Z.land x z)) (Z.land y z).
Definition bsig0 (x : Z) : Z := Z.lxor (Z.lxor (rotr 2 x) (rotr 13 x)) (rotr 22 x).
Definition bsig1 (x : Z) : Z := Z.lxor (Z.lxor (rotr 6 x) (rotr 11 x)) (rotr 25 x).
Definition ssig0 (x : Z) : Z := Z.lxor (Z.lxor (rotr 7 x) (rotr 18 x)) (shr 3 x).
Definition ssig1 (x : Z) : Z := Z.lxor (Z.lxor (rotr 17 x) (rotr 19 x)) (shr 10 x).

Definition KK : list Z :=
  [0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
   0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
   0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
   0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
   0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
   0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
   0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
   0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2].

Definition HH0 : list Z :=
  [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19].

Fixpoint words (l : bytes) : list Z :=
  match l with
  | a :: b :: c :: d :: r => (((a * 256 + b) * 256 + c) * 256 + d) :: words r
  | _ => []
  end.

Fixpoint sched (fuel : nat) (win : list Z) : list Z :=
  match fuel with
  | O => []
  | S f =>
      let nw := add32 (add32 (add32 (ssig1 (nth 14 win 0)) (nth 9 win 0)) (ssig0 (nth 1 win 0))) (nth 0 win 0) in
      nw :: sched f (tl win ++ [nw])
  end.

Definition st8 : Type := (Z * Z * Z * Z * Z * Z * Z * Z)%type.

Definition round (s : st8) (kw : Z * Z) : st8 :=
  let '(a, b, c, d, e, f, g, h) := s in
  let t1 := add32 (add32 (add32 (add32 h (bsig1 e)) (chf e f g)) (fst kw)) (snd kw) in
  let t2 := add32 (bsig0 a) (majf a b c) in
  (add32 t1 t2, a, b, c, add32 d t1, e, f, g).

Definition compress (hv : list Z) (blk : bytes) : list Z :=
  let w16 := words blk in
  let W := w16 ++ sched 48 w16 in
  let s0 := (nth 0 hv 0, nth 1 hv 0, nth 2 hv 0, nth 3 hv 0, nth 4 hv 0, nth 5 hv 0, nth 6 hv 0, nth 7 hv 0) in
  let '(a, b, c, d, e, f, g, h) := fold_left round (combine KK W) s0 in
  [add32 a (nth 0 hv 0); add32 b (nth 1 hv 0); add32 c (nth 2 hv 0); add32 d (nth 3 hv 0);
   add32 e (nth 4 hv 0); add32 f (nth 5 hv 0); add32 g (nth 6 hv 0); add32 h (nth 7 hv 0)].

(* big-endian, k bytes *)
Fixpoint be_bytes (k : nat) (x : Z) : bytes :=
  match k with
  | O => []
  | S k' => be_bytes k' (x / 256) ++ [x mod 256]
  end.

Definition from_be (l : bytes) : Z := fold_left (fun acc b => acc * 256 + b) l 0.

Definition pad (m : bytes) : bytes :=
  let n := Z.of_nat (List.length m) in
  let k := (55 - n) mod 64 in
  m ++ [128] ++ repeat 0 (Z.to_nat k) ++ be_bytes 8 (8 * n).

Fixpoint blocks (fuel : nat) (l : bytes) (hv : list Z) : list Z :=
  match fuel with
  | O => hv
  | S f =>
      match l with
      | [] => hv
      | _ => blocks f (skipn 64 l) (compress hv (firstn 64 l))
      end
  end.

Definition sha256_spec (m : bytes) : bytes :=
  let p := pad m in
  flat_map (be_bytes 4) (blocks (S (List.length p / 64)) p HH0).

(* The hash used by the protocol code. Extraction maps it to HACL*'s verified SHA-256 (src/Extraction/*/Extraction.v);
   sha256_spec stays extracted too and is cross-checked against it and against hashlib. *)
Definition sha256 (m : bytes) : bytes := sha256_spec m.

Definition bytes_of_string (s : String.string) : bytes :=
  map (fun c => Z.of_nat (Ascii.nat_of_ascii c)) (String.list_ascii_of_string s).

Definition hex (l : bytes) : Z := from_be l.

Lemma sha256_abc :
  hex (sha256 (bytes_of_string "abc"%string)) = 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_empty :
  hex (sha256 []) = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_448 :
  hex (sha256 (bytes_of_string "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"%string))
  = 0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_896 :
  hex (sha256 (bytes_of_string (String.append "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghij"%string
                                 "klmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"%string)))
  = 0xcf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* serialisation of field elements (fp_core.py: ser_base, ser_f, ser_fs) *)

Definition EB : nat := 10.
Definition ser_base (x : Z) : bytes := be_bytes EB x.
Definition ser_f (x : xf) : bytes := ser_base (fst x) ++ ser_base (snd x).
Definition ser_fs (xs : list xf) : bytes := flat_map ser_f xs.

(* ---------------------------------------------------------------------- *)
(* the Fiat-Shamir challenger (fp_core.py: FSChallenger) *)

Record chal : Type := mk_chal { cstate : bytes; cbuf : bytes; cctr : Z }.

Definition sep (s : String.string) : bytes := bytes_of_string s.

Definition fs_init (domain : bytes) : chal :=
  mk_chal (sha256 (bytes_of_string "FP-BGV-v2|"%string ++ domain)) [] 0.

Definition fs_absorb (ch : chal) (label data : bytes) : chal :=
  mk_chal (sha256 (cstate ch ++ sep "|A|"%string ++ label ++ sep "|"%string ++ sha256 data)) [] 0.

(* make the buffer at least k bytes long *)
Fixpoint fill (fuel : nat) (k : nat) (ch : chal) : chal :=
  match fuel with
  | O => ch
  | S f =>
      if Nat.leb k (List.length (cbuf ch)) then ch
      else fill f k (mk_chal (cstate ch) (cbuf ch ++ sha256 (cstate ch ++ sep "|S|"%string ++ be_bytes 8 (cctr ch)))
                             (cctr ch + 1))
  end.

Definition take (k : nat) (ch : chal) : bytes * chal :=
  let ch' := fill (S k) k ch in
  (firstn k (cbuf ch'), mk_chal (cstate ch') (skipn k (cbuf ch')) (cctr ch')).

Definition start (ch : chal) (name : bytes) : chal :=
  mk_chal (sha256 (cstate ch ++ sep "|C|"%string ++ name)) [] 0.

Fixpoint base (fuel : nat) (ch : chal) : option (Z * chal) :=
  match fuel with
  | O => None
  | S f =>
      let '(bs, ch') := take EB ch in
      let v := Z.land (from_be bs) (2 ^ 79 - 1) in
      if Z.ltb v Q then Some (v, ch') else base f ch'
  end.

Fixpoint get_Fs (n : nat) (ch : chal) : option (list xf * chal) :=
  match n with
  | O => Some ([], ch)
  | S n' =>
      match base 1000 ch with
      | None => None
      | Some (a, ch1) =>
          match base 1000 ch1 with
          | None => None
          | Some (b, ch2) =>
              match get_Fs n' ch2 with
              | None => None
              | Some (xs, ch3) => Some ((a, b) :: xs, ch3)
              end
          end
      end
  end.

Definition get_F (ch : chal) (name : bytes) (n : nat) : option (list xf * chal) :=
  get_Fs n (start ch name).

(* n distinct indices below bound (a power of 2), in the order drawn *)
Fixpoint get_Is (fuel : nat) (n : nat) (bound : Z) (seen : list Z) (ch : chal) : option (list Z * chal) :=
  match n with
  | O => Some ([], ch)
  | S n' =>
      match fuel with
      | O => None
      | S f =>
          let '(bs, ch') := take 4 ch in
          let v := Z.land (from_be bs) (bound - 1) in
          if existsb (Z.eqb v) seen then get_Is f n bound seen ch'
          else match get_Is f n' bound (v :: seen) ch' with
               | None => None
               | Some (vs, ch'') => Some (v :: vs, ch'')
               end
      end
  end.

Definition get_I (ch : chal) (name : bytes) (n : nat) (bound : Z) : option (list Z * chal) :=
  get_Is (n * 64 + 1000) n bound [] (start ch name).

(* ---------------------------------------------------------------------- *)
(* Merkle paths (fp_core.py: leaf_hash, merkle_root_from) *)

Definition leaf_hash (salt : bytes) (entries : list Z) : bytes :=
  sha256 (salt ++ flat_map ser_base entries).

Fixpoint root_from (h : bytes) (j : Z) (path : list bytes) : bytes :=
  match path with
  | [] => h
  | sib :: path' =>
      root_from (if Z.even j then sha256 (h ++ sib) else sha256 (sib ++ h)) (Z.shiftr j 1) path'
  end.
