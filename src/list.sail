/* These index lists starting from zero */

// TODO: use built-ins where appropriate

val nth : forall ('t : Type). (list('t), nat) -> option('t)

function nth(l, i) =
  match l {
  [| |] => None(),
  h::t => if i == 0 then Some(h) else nth(t, i - 1)
  }

val set_nth : forall ('t : Type). (list('t), nat, 't) -> option(list('t))

function set_nth(l, i, v) =
  match l {
  [| |] => None(),
  h::t => if i == 0 then Some(v::t) else match set_nth(t, i - 1, v) { None() => None(), Some(t') => Some(h::t') }
  }

val is_nil : forall ('t : Type). list('t) -> bool
function is_nil(l) = match l { [| |] => true, _ => false }

val is_cons : forall ('t : Type). list('t) -> bool
function is_cons(l) = match l { [| |] => false, _ => true }

val head_tail : forall ('t : Type). list('t) -> ('t, list('t))
function head_tail(l) = match l { [| |] => unreachable("nil in non-empty list"), h::t => (h,t) }

val list_length : forall ('t : Type). list('t) -> nat
function list_length(l) = {
  var l' = l;
  var n : nat = 0;
  while is_cons(l') do {
    let (_, t) = head_tail(l');
    l' = t;
    n = n + 1;
  };
  n
}

overload length = { list_length }

val reverse : forall ('t : Type). list('t) -> list('t)

function reverse(l) = {
  var l_in : list('t) = l;
  var l_out : list('t) = [| |];
  while is_cons(l_in) do {
    let (h,t) = head_tail(l_in);
    l_in = t;
    l_out = h::l_out
  };
  l_out
}
 
val list_append : forall ('t : Type). (list('t), list('t)) -> list('t)
function list_append(l1, l2) = {
  var l1r = reverse(l1);
  var l_out = l2;
  while is_cons(l1r) do {
    let (h,t) = head_tail(l1r);
    l1r = t;
    l_out = h::l_out
  };
  l_out
}

overload append = { list_append }

// TODO: Is this the usual form for drop and take?
val list_drop : forall ('t : Type). (list('t), int) -> list('t)
function list_drop(l, n) = {
  var l' = l;
  foreach (i from 1 to n) {
    match l' {
      [| |] => return [| |],
      _::t => l' = t,
    }
  };
  l'
}

val list_take : forall ('t : Type). (list('t), int) -> list('t)
function list_take(l, n) = {
  var l_in = l;
  var l_out : list('t) = [| |];
  foreach (i from 1 to n) {
    match l_in {
      [| |] => (),
      h::t => {
        l_out = h::l_out;
        l_in = t;
      }
    }
  };
  reverse(l_out)
}

val list_of_vector : forall ('t : Type) 'n. vector('n, 't) -> list('t)

function list_of_vector(v) = {
  var l : list('t) = [| |];
  let len = length(v);
  foreach (i from (len - 1) downto 0) l = v[i]::l;
  l
}

