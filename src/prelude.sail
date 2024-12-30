default Order dec
$include <prelude.sail>

overload operator - = { sub_bits }
overload append = { concat_str }

// as in Arm

val putchar = pure {
  ocaml: "putchar",
  lem: "putchar",
  interpreter: "putchar",
  c: "sail_putchar",
  coq: "putchar"
} : int -> unit

/* as in RISC-V */

infix 7 <<
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

