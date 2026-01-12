
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val eqb : bool -> bool -> bool

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val compare : int -> int -> comparison

  val geb : int -> int -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type bit = bool

val hamming_weight : bit list -> int

val parity : bit list -> bit

val heaviside : int -> bit

val dot : int list -> bit list -> int

val neuron : int list -> int -> bit list -> bit

val ones : int -> int list

val l1_weights_concrete : (int list * int) list

val l2_weights_concrete : int list * int

val output_weights_concrete : int list * int

val layer : (int list * int) list -> bit list -> bit list

val parity_depth2_concrete : bit list -> bit

val all_inputs : int -> bit list list

val check_all : bool

val verified_parity : bit list -> bit

val reference_parity : bit list -> bit

val all_8bit_inputs : bit list list

val test_all : bool
