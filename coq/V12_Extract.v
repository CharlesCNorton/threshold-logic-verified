(** * V12_Extract: OCaml Extraction for Depth-2 Parity Network *)

(**
   Extracts the verified depth-2 parity network from V12_Depth2Minimal.v
   to executable OCaml code.

   USAGE:
   1. Compile V12_Depth2Minimal.v first.
   2. Compile this file: coqc V12_Extract.v
   3. Output appears in extracted/parity_verified.ml

   The extracted code inherits correctness from the Coq proofs.
   See extracted/test_parity.ml for a test suite.
*)

Require Import V12_Depth2Minimal.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.

(** Boolean extraction to native OCaml. *)
Extract Inlined Constant negb => "not".
Extract Inlined Constant xorb => "(fun a b -> a <> b)".
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".

(** Nat comparisons to native OCaml. *)
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.eqb => "(=)".

(** Extraction targets. *)

(** The verified parity function (depth-2 threshold network). *)
Definition verified_parity := parity_depth2_concrete.

(** Reference parity (XOR-based) for testing. *)
Definition reference_parity := parity.

(** All 256 8-bit inputs for exhaustive testing. *)
Definition all_8bit_inputs := all_inputs 8.

(** Exhaustive correctness test. *)
Definition test_all := check_all.

(** Perform extraction. *)
Cd "..".
Extraction "extracted/parity_verified"
  verified_parity
  reference_parity
  all_8bit_inputs
  test_all
  hamming_weight.
