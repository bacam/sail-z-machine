enum alphabet = { A0, A1, A2 }

// Avoid need for generic equality
function is_A2(a : alphabet) -> bool = match a { A2 => true, _ => false }

type zscii = bits(10)

struct z_decode_state = {
  current_alphabet : alphabet,
  next_char_alphabet : alphabet,
  ten_bit : option(option(bits(5))), // progress through 10-bit ZSCII character
  abbreviation : option(bits(4)), // look up an abbreviation using next char
}

function alphabet_shift(state : z_decode_state, two : bool, lock : bool) -> z_decode_state = {
  let new : alphabet =
    if two
    then match state.current_alphabet { A0 => A1, A1 => A2, A2 => A0 }
    else match state.current_alphabet { A0 => A2, A1 => A0, A2 => A1 };
  if lock
  then { state with current_alphabet = new, next_char_alphabet = new }
  else { state with next_char_alphabet = new }
}

let a2_later : vector(32, bits(10)) = [
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000001011, // carriage return (newline)
  0b0000110000, // 0
  0b0000110001, // 1
  0b0000110010, // 2
  0b0000110011, // 3
  0b0000110100, // 4
  0b0000110101, // 5
  0b0000110110, // 6
  0b0000110111, // 7
  0b0000111000, // 8
  0b0000111000, // 9
  0b0000101110, // .
  0b0000101100, // ,
  0b0000100001, // !
  0b0000111111, // ?
  0b0001011111, // _
  0b0000100011, // #
  0b0000100111, // '
  0b0000100010, // "
  0b0000101111, // /
  0b0001011100, // \
  0b0000101011, // -
  0b0000111010, // :
  0b0000101000, // (
  0b0000101001, // )
]

let a2_v1 : vector(32, bits(10)) = [
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000000000, // dummy
  0b0000110000, // 0
  0b0000110001, // 1
  0b0000110010, // 2
  0b0000110011, // 3
  0b0000110100, // 4
  0b0000110101, // 5
  0b0000110110, // 6
  0b0000110111, // 7
  0b0000111000, // 8
  0b0000111000, // 9
  0b0000101110, // .
  0b0000101100, // ,
  0b0000100001, // !
  0b0000111111, // ?
  0b0001011111, // _
  0b0000100011, // #
  0b0000100111, // '
  0b0000100010, // "
  0b0000101111, // /
  0b0001011100, // \
  0b0000111100, // <
  0b0000101011, // -
  0b0000111010, // :
  0b0000101000, // (
  0b0000101001, // )
]


function decode_z_char(state : z_decode_state, z_char : bits(5)) -> (z_decode_state, option(bits(10))) = {
  match state.ten_bit {
    None() => (),
    Some(None()) => return ({state with ten_bit = Some(Some(z_char))}, None()),
    Some(Some(prev)) => return ({state with ten_bit = None()}, Some(prev @ z_char))
  };
  let alphabet = state.next_char_alphabet;
  let state = { state with next_char_alphabet = state.current_alphabet };
  match z_char {
    0b00000 => (state, Some(0b0000100000)), // space
    0b00001 if version == 1 => (state, Some(0b0000001011)), // carriage return (newline)
    0b00001                 => ({ state with abbreviation = Some(0x0) }, None()),
    0b00010 if version < 3  => (alphabet_shift(state, true,  false), None()),
    0b00010                 => ({ state with abbreviation = Some(0x1) }, None()),
    0b00011 if version < 3  => (alphabet_shift(state, false, false), None()),
    0b00011                 => ({ state with abbreviation = Some(0x2) }, None()),
    0b00100 if version < 3  => (alphabet_shift(state, true,  true), None()),
    0b00100                 => ({state with next_char_alphabet = A1}, None()),
    0b00101 if version < 3  => (alphabet_shift(state, false, true), None()),
    0b00101                 => ({state with next_char_alphabet = A2}, None()),
    0b00110 if is_A2(alphabet) => ({state with ten_bit = Some(None())}, None()),
    _ => {
      let table : address = if version < 5 then 0x00000 else sail_zero_extend(read_word(0x00034), 20);
      let char : zscii =
      if table == 0x00000 then
        match alphabet {
        A0 => 0b0001100001 /* a */ + sail_zero_extend(z_char, 10) - 0b0000000110,
        A1 => 0b0001000001 /* A */ + sail_zero_extend(z_char, 10) - 0b0000000110,
        A2 => if version == 1 then a2_v1[31 - unsigned(z_char)] else a2_later[31 - unsigned(z_char)],
        }
      else unimplemented("zchar tables");
      (state, Some(char))
    }
  }
}

function read_z_coded_string_r(addr : address, in_abbreviation : bool) -> (address, list(zscii)) = {
  var cur_addr = addr;
  // First, extract the Z-characters, find the end
  var z_chars : list(bits(5)) = [| |];
  var done : bool = false;
  repeat {
    let word = read_word(cur_addr);
    cur_addr = cur_addr + 2;
    z_chars = word[4..0] :: word[9..5] :: word[14..10] :: z_chars;
    done = word[15] == bitone;
  } until done;
  z_chars = reverse(z_chars);

  // Now decode them
  var z_string_rev : list(zscii) = [| |];
  var state : z_decode_state = struct {
    current_alphabet = A0,
    next_char_alphabet = A0,
    ten_bit = None(),
    abbreviation = None(),
  };
  while is_cons(z_chars) do {
    let (z_char, tail) = head_tail(z_chars);
    z_chars = tail;
    match state.abbreviation {
      None() => {
        let (new_state, char) = decode_z_char(state, z_char);
        match char {
          Some(c) => z_string_rev = c::z_string_rev,
          None() => ()
        };
	state = new_state
      },
      Some(z) => {
        // TODO: check for incomplete construction
	if in_abbreviation then throw NestedAbbreviation();
	let table = sail_zero_extend(read_word(0x00018), 20);
        let table_entry = table + sail_zero_extend(z, 20) << 6 + sail_zero_extend(z_char, 20) << 1;
	let abbrev_addr = sail_zero_extend(read_word(table_entry), 20) << 1;
        let (_, abb) = read_z_coded_string_r(abbrev_addr, true);
	z_string_rev = abb @ z_string_rev;
        state = { state with abbreviation = None() }
      }
    }
  };
  (cur_addr, z_string_rev)
}

function read_z_coded_string(addr : address) -> (address, list(zscii)) = {
  let (new_addr, s) = read_z_coded_string_r(addr, false);
  (new_addr, reverse(s))
}

function print_zscii(char : zscii) -> unit = {
  match char {
    0b0000000000 => return (),
    0b0000001001 => putchar(9), // TODO: v6 only
    0b0000001011 => putchar(32), // TODO: v6 only
    0b0000001101 => putchar(10),
    _ => (),
  };
  if 0b0000100000 <=_u char & char <=_u 0b0001111110 then putchar(unsigned(char)) else
  unimplemented("non-ascii characters")
}

function print_zscii_string(s : list(zscii)) -> unit = {
  var s' : list(zscii) = s;
  while is_cons(s') do {
    match s' {
      [| |] => unreachable("nil is_cons"),
      h::t => {
        print_zscii(h);
	s' = t
      }
    }
  }
}

val encode_zscii : forall 'n. (implicit('n), vector('n, bits(5)), nat, bits(8)) -> (vector('n, bits(5)), nat)

function encode_zscii(dest_size, dest, start, char) = {
  // To lower case
  let norm_char = if char >=_u 0x41 & char <=_u 0x5a then char + 0x20 else char;
  if char >=_u 0x61 & char <=_u 0x7a then {
    if start < dest_size then {
      var result = dest;
      result[start] = truncate(char - 0x5b, 5);
      (result, start + 1)
    } else (dest, start)
  } else {
    unimplemented("non a-z character")
  }
}

val pack_zchars : forall 'n, 'n in {2,3}. (implicit('n), vector('n * 3, bits(5))) -> vector('n * 2, bits(8))
function pack_zchars(triplets, zchars) = {
  var result : vector('n * 2, bits(8)) = vector_init(0x00);
  foreach (i from 0 to ('n - 1)) {
    result[i * 2] = 0b0 @ zchars[i * 3] @ zchars[i * 3 + 1][4..3];
    result[i * 2 + 1] = zchars[i * 3 + 1][2..0] @ zchars[i * 3 + 2];
  };
  // TODO: not sure if this is necessary, or if it should appear for truncated words
  result[('n - 1) * 2] = result[('n - 1) * 2] | 0x80;
  result
}
