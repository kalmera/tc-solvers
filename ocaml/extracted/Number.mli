open Decimal
open Hexadecimal

type uint =
| UIntDecimal of Decimal.uint
| UIntHexadecimal of Hexadecimal.uint

type signed_int =
| IntDecimal of Decimal.signed_int
| IntHexadecimal of Hexadecimal.signed_int

type number =
| Decimal of decimal
| Hexadecimal of hexadecimal

val uint_beq : uint -> uint -> bool

val uint_eq_dec : uint -> uint -> bool

val signed_int_beq : signed_int -> signed_int -> bool

val signed_int_eq_dec : signed_int -> signed_int -> bool

val number_beq : number -> number -> bool

val number_eq_dec : number -> number -> bool

val uint_of_uint : uint -> uint

val int_of_int : signed_int -> signed_int
