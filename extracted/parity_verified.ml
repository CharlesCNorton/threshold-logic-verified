
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val geb : int -> int -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

type bit = bool

(** val hamming_weight : bit list -> int **)

let rec hamming_weight = function
| [] -> 0
| b :: xs' ->
  if b then Stdlib.Int.succ (hamming_weight xs') else hamming_weight xs'

(** val parity : bit list -> bit **)

let rec parity = function
| [] -> false
| x :: xs' -> (fun a b -> a <> b) x (parity xs')

(** val heaviside : int -> bit **)

let heaviside x =
  Z.geb x 0

(** val dot : int list -> bit list -> int **)

let rec dot ws xs =
  match ws with
  | [] -> 0
  | w :: ws' ->
    (match xs with
     | [] -> 0
     | x :: xs' -> Z.add (if x then w else 0) (dot ws' xs'))

(** val neuron : int list -> int -> bit list -> bit **)

let neuron ws b xs =
  heaviside (Z.add (dot ws xs) b)

(** val ones : int -> int list **)

let rec ones n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> 1 :: (ones n'))
    n

(** val l1_weights_concrete : (int list * int) list **)

let l1_weights_concrete =
  ((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
     0))))))))),
    0) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    1)) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->2*p)
    1))) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->1+2*p)
    1))) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->2*p) ((fun p->2*p)
    1)))) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->1+2*p) ((fun p->2*p)
    1)))) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->2*p) ((fun p->1+2*p)
    1)))) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->1+2*p) ((fun p->1+2*p)
    1)))) :: (((ones (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), ((~-)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))) :: []))))))))

(** val l2_weights_concrete : int list * int **)

let l2_weights_concrete =
  ((1 :: (((~-) 1) :: (1 :: (((~-) 1) :: (1 :: (((~-) 1) :: (1 :: (((~-)
    1) :: (1 :: []))))))))), ((~-) 1))

(** val output_weights_concrete : int list * int **)

let output_weights_concrete =
  ((((~-) 1) :: []), 0)

(** val layer : (int list * int) list -> bit list -> bit list **)

let layer neurons xs =
  map (fun wb -> neuron (fst wb) (snd wb) xs) neurons

(** val parity_depth2_concrete : bit list -> bit **)

let parity_depth2_concrete xs =
  let h1 = layer l1_weights_concrete xs in
  let h2 = neuron (fst l2_weights_concrete) (snd l2_weights_concrete) h1 in
  neuron (fst output_weights_concrete) (snd output_weights_concrete)
    (h2 :: [])

(** val all_inputs : int -> bit list list **)

let rec all_inputs n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [] :: [])
    (fun n' ->
    app (map (fun x -> false :: x) (all_inputs n'))
      (map (fun x -> true :: x) (all_inputs n')))
    n

(** val check_all : bool **)

let check_all =
  forallb (fun xs -> eqb (parity_depth2_concrete xs) (parity xs))
    (all_inputs (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))

(** val verified_parity : bit list -> bit **)

let verified_parity =
  parity_depth2_concrete

(** val reference_parity : bit list -> bit **)

let reference_parity =
  parity

(** val all_8bit_inputs : bit list list **)

let all_8bit_inputs =
  all_inputs (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))

(** val test_all : bool **)

let test_all =
  check_all
