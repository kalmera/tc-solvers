open Datatypes
open Decimal
open Hexadecimal
open Number

type t = int

val zero : int

val one : int

val two : int

val succ : int -> int

val pred : int -> int

val add : int -> int -> int

val double : int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val leb : int -> int -> bool

val ltb : int -> int -> bool

val compare : int -> int -> comparison

val even : int -> bool

val odd : int -> bool

val pow : int -> int -> int

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : Decimal.uint -> int -> int

val of_uint : Decimal.uint -> int

val of_hex_uint_acc : Hexadecimal.uint -> int -> int

val of_hex_uint : Hexadecimal.uint -> int

val of_num_uint : uint -> int

val to_little_uint : int -> Decimal.uint -> Decimal.uint

val to_uint : int -> Decimal.uint

val to_little_hex_uint : int -> Hexadecimal.uint -> Hexadecimal.uint

val to_hex_uint : int -> Hexadecimal.uint

val to_num_uint : int -> uint

val to_num_hex_uint : int -> uint

val of_int : Decimal.signed_int -> int option

val of_hex_int : Hexadecimal.signed_int -> int option

val of_num_int : signed_int -> int option

val to_int : int -> Decimal.signed_int

val to_hex_int : int -> Hexadecimal.signed_int

val to_num_int : int -> signed_int

val divmod : int -> int -> int -> int -> int * int

val div : int -> int -> int

val modulo : int -> int -> int

val gcd : int -> int -> int

val square : int -> int

val sqrt_iter : int -> int -> int -> int -> int

val sqrt : int -> int

val log2_iter : int -> int -> int -> int -> int

val log2 : int -> int

val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

val div2 : int -> int

val testbit : int -> int -> bool

val shiftl : int -> int -> int

val shiftr : int -> int -> int

val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

val coq_land : int -> int -> int

val coq_lor : int -> int -> int

val ldiff : int -> int -> int

val coq_lxor : int -> int -> int
