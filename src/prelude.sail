default Order dec
$include <prelude.sail>
$include <mapping.sail>
$include <smt.sail>

overload operator - = { sub_bits }
// Word around Sail C bug
function concat_str2(s : string, s' : string) -> string = let s'' = concat_str(s,s') in s''
overload append = { concat_str2 }

val "string_hd" : string -> int
function string_destruct(s : string) -> option((int, string)) = {
  if s == "" then None() else Some((string_hd(s), string_drop(s, 1)))
}

val "random_range" : (int, int) -> int
val "random_seed" : int -> unit

// as in Arm

val putchar = pure {
  ocaml: "putchar",
  lem: "putchar",
  interpreter: "putchar",
  c: "sail_putchar",
  coq: "putchar"
} : int -> unit

/* as in RISC-V */

infix 7 >>
infix 7 >>>
infix 7 <<
overload operator >> = { sail_shiftright }
overload operator >>> = { sail_arith_shiftright }
overload operator << = { sail_shiftleft }

infix 4 <_s
infix 4 >_s
infix 4 <=_s
infix 4 >=_s
infix 4 <_u
infix 4 >_u
infix 4 <=_u
infix 4 >=_u

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator >_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator <=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >_s  (x, y) = signed(x) > signed(y)
function operator <=_s (x, y) = signed(x) <= signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >_u  (x, y) = unsigned(x) > unsigned(y)
function operator <=_u (x, y) = unsigned(x) <= unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)

