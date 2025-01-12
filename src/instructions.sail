
val fetch_byte : unit -> bits(8)

enum operand_type = {LargeConst, SmallConst, Variable, Omitted}

type operand = bits(16)

// Some opcodes are followed by more data than the generic operands
val fetch_result_destination : unit -> bits(8)
val fetch_string : unit -> list(zscii)
val fetch_branch : unit -> (bool, bits(14))

scattered union instr

val decode_0op : bits(4) -> instr
val decode_1op : (bits(4), operand) -> instr
val decode_2op : (bits(5), operand, operand) -> instr
val decode_var : (bits(5), list(operand)) -> instr

val execute : instr -> unit

scattered function decode_0op
scattered function decode_1op
scattered function decode_2op
scattered function decode_var
scattered function execute

union clause instr = LoadB : (operand, operand, bits(8))
function clause decode_2op (0b10000, x, y) = LoadB(x,y,fetch_result_destination())
function clause execute LoadB(array, index, destination) = {
  let addr = sail_zero_extend(array, 20) + sail_zero_extend(index, 20);
  if addr >_u 0x0ffff then throw LoadAddressOverflow(addr);
  write_variable(destination, sail_zero_extend(read_byte(addr), 16))
}

union clause instr = LoadW : (operand, operand, bits(8))
function clause decode_2op (0b01111, x, y) = LoadW(x,y,fetch_result_destination())
function clause execute LoadW(array, index, destination) = {
  let addr = sail_zero_extend(array, 20) + sail_zero_extend(index, 20) << 1;
  if addr >_u 0x0fffe then throw LoadAddressOverflow(addr);
  write_variable(destination, read_word(addr))
}

union clause instr = Add : (operand, operand, bits(8))
function clause decode_2op (0b10100, x, y) = Add(x,y,fetch_result_destination())
function clause execute Add(x, y, r) = write_variable(r, x + y)

union clause instr = Sub : (operand, operand, bits(8))
function clause decode_2op (0b10101, x, y) = Sub(x,y,fetch_result_destination())
function clause execute Sub(x, y, r) = write_variable(r, x - y)

union clause instr = Mul : (operand, operand, bits(8))
function clause decode_2op (0b10110, x, y) = Mul(x,y,fetch_result_destination())
function clause execute Mul(x, y, r) = write_variable(r, add_bits_int(sail_zeros(16), signed(x) * signed(y)))

union clause instr = Store : (bits(8), operand)
function clause decode_2op (0b01101, x, y) = {
  if x >_u 0x00ff then throw NoSuchLocal(unsigned(x));
  Store(truncate(x, 8), y)
}
function clause execute Store(vr, vl) = write_variable(vr, vl)

union clause instr = JZ : (operand, bool, bits(14))
function clause decode_1op (0x0, x) = {
  let (direction, offset) = fetch_branch();
  JZ(x, direction, offset)
}
function clause execute JZ(operand, direction, offset) = {
  let cond = operand == 0x0000;
  let cond = if direction then cond else not_bool(cond);
  if cond then {
    if offset == 0b00000000000000 then unimplemented("ret false")
    else if offset == 0b00000000000001 then unimplemented("ret true")
    else PC = PC + sail_sign_extend(offset, 20) - 0x00002
  }
}

union clause instr = Load : (operand, bits(8))

// TODO: check what the operand actually is; variable number or value?
function clause decode_1op (0xe, x) = Load(x, fetch_result_destination())

function clause execute Load(x, r) = write_variable(r, x)

union clause instr = Print : list(zscii)
function clause decode_0op 0x2 = Print(fetch_string())
function clause execute Print(s) = print_zscii_string(s)

union clause instr = Nop : unit
function clause decode_0op 0x4 = Nop()
function clause execute Nop() = ()

union clause instr = NewLine : unit
function clause decode_0op 0xb = NewLine()
function clause execute NewLine() = print_endline("")

union clause instr = PrintChar : bits(10)
function clause decode_var (0b00101, operands) =
  match operands {
    [| code |] if code <_u 0x0400 => PrintChar(truncate(code, 10)),
    _ => throw MalformedInstruction("print_char with invalid operand(s)"),
  }
function clause execute PrintChar(char) = print_zscii(char)

union clause instr = Call : (address, list(operand), bits(8))
function clause decode_var (0b00000, operands) =
  match operands {
    [| |] => throw MalformedInstruction("call without routine"),
    routine::arguments => Call(unpack_address(routine, RoutineCall), arguments, fetch_result_destination()),
  }
function clause execute Call(routine, arguments, destination) =
  if routine == 0x00000 then write_variable(destination, 0x0000) else {
  prerr_bits("routine ", routine);
  let number_locals = unsigned(read_byte(routine));
  let locals_from_arguments : list(bits(16)) = list_take(arguments, number_locals);
  var new_locals : list(bits(16)) = [| |];
  foreach (i from number_locals downto (length(locals_from_arguments) + 1)) {
    let v = if version < 5 then read_word(add_bits_int(routine, 2*i)) else 0x0000;
    new_locals = v::new_locals;
  };
  new_locals = locals_from_arguments @ new_locals;
  routine_stack = (locals, stack, Some(destination))::routine_stack;
  locals = new_locals;
  stack = [| |];
  PC = add_bits_int(routine, 2*number_locals+1);
  prerr_bits("new pc ", PC)
}

union clause instr = StoreW : (operand, operand, operand)
function clause decode_var (0b00001, operands) = match operands {
  [| array, index, value |] => StoreW(array, index, value),
  _ => throw MalformedInstruction("storeb without 3 operands")
}
function clause execute StoreW(array, index, value) = {
  let addr = sail_zero_extend(array, 20) + sail_zero_extend(index, 20);
  if addr >_u 0x0fffe then throw LoadAddressOverflow(addr);
  write_word(addr, value)
}

union clause instr = StoreB : (operand, operand, operand)
function clause decode_var (0b00010, operands) = match operands {
  [| array, index, value |] => StoreB(array, index, value),
  _ => throw MalformedInstruction("storeb without 3 operands")
}
function clause execute StoreB(array, index, value) = {
  let addr = sail_zero_extend(array, 20) + sail_zero_extend(index, 20);
  if addr >_u 0x0ffff then throw LoadAddressOverflow(addr);
  if value >_u 0x00ff then warn("Oversize byte store"); // Not sure if this is allowed
  write_byte(addr, truncate(value, 8))
}

union clause instr = Read : (operand, operand, option((operand, address)))
function clause decode_var (0b00100, [| text, parse |]) = Read(text, parse, None())
function clause decode_var ((0b00100, [| text, parse, time, routine |]) if version >= 4) =
  Read(text, parse, Some((time, unpack_address(routine, RoutineCall))))
function clause decode_var (0b00100, _) = throw MalformedInstruction("read with wrong number of operands")

val byte_is_in : forall 'n. (implicit('n), vector('n, dec, bits(8)), bits(8)) -> bool

function byte_is_in(size, chars, char) = {
  var found : bool = false;
  foreach (i from 0 to (size - 1)) {
    if chars[i] == char then found = true;
  };
  found
}

struct dictionary_info = {
  entry_length : nat,
  number_entries : nat,
  entries_start : address,
}

function read_dictionary_info(dictionary : address, number_word_separators : nat) -> dictionary_info = {
  let info : dictionary_info = struct {
    entry_length = unsigned(read_byte(add_bits_int(dictionary, number_word_separators + 1))),
    number_entries = unsigned(read_word(add_bits_int(dictionary, number_word_separators + 2))),
    entries_start = add_bits_int(dictionary, number_word_separators + 3),
  };
  if info.entry_length < (if version <= 3 then 4 else 6) then throw InvalidDictionaryEntryLength(info.entry_length);
  info
}

val lookup_entry : forall 'n. (implicit('n), dictionary_info, vector('n, bits(8))) -> address

function lookup_entry(size_zchars, dictionary, zchars) = {
  // We ought to be able to do a binary search here, but keep it simple
  foreach (i from 1 to dictionary.number_entries) {
    let entry = add_bits_int(dictionary.entries_start, i * dictionary.entry_length);
    var found : bool = true;
    foreach (j from 0 to (size_zchars - 1)) {
      found = found & read_byte(add_bits_int(entry, j)) == zchars[j]
    };
    if found then return entry;
  };
  0x00000
}

function clause execute Read(text, parse, timer) = {
  // TODO: status line
  let text_addr = sail_zero_extend(text, 20);
  let existing_characters = if version >= 5 then unsigned(read_byte(text_addr + 0x00001)) else 0;
  let max_characters = unsigned(read_byte(text_addr)) - existing_characters;
  // TODO: max < 0?
  var s : string = match timer {
    None() => read_command_plain(max_characters),
    Some(_) => unimplemented("timer callback"),
  };
  // Write the string into memory
  let new_start_addr = add_bits_int(text_addr, if version < 5 then 1 else existing_characters + 2);
  var i : int = 0;
  var more : bool = true;
  while i < max_characters & more do {
    match string_destruct(s) {
      None() => more = false,
      Some(c,t) => {
        if c == 10 then more = false else {
          s = t;
	  write_byte(add_bits_int(new_start_addr, i), add_bits_int(0x00, c));
	  i = i + 1;
        }
      }
    }
  };
  let total_characters = existing_characters + i;
  if more then unreachable("read overflow!");
  if version < 5 then {
    write_byte(add_bits_int(new_start_addr, total_characters), 0x00);
  } else {
    write_byte(text_addr + 0x00001, add_bits_int(0x00, total_characters));
  };
  // Perform lexical analysis
  if parse != 0x0000 | version < 5 then {
    let parse_addr = sail_zero_extend(parse, 20);
    let max_words = unsigned(read_byte(parse_addr));
    let dictionary = sail_zero_extend(read_word(0x00008), 20);
    let 'number_word_separators = unsigned(read_byte(dictionary));
    var word_separators : vector('number_word_separators + 1, bits(8)) = vector_init(0x32);
    if number_word_separators >= 1 then {
      foreach (i from 1 to number_word_separators) {
        word_separators[i] = read_byte(add_bits_int(dictionary, i))
      }
    };
    let dictionary_info = read_dictionary_info(dictionary, number_word_separators);

    var j : int = 0;
    var words : int = 0;
    let start_addr = add_bits_int(text_addr, if version < 5 then 1 else 2);
    let 'encode_triplets = if version <= 3 then 2 else 3;
    let empty_entry : vector('encode_triplets * 3, bits(5)) = vector_init(0b00101);

    while words < max_words & j < total_characters do {
      var char = read_byte(add_bits_int(start_addr, j));
      if char == 0x20 then j = j + 1
      else if byte_is_in(word_separators, char) then {
        let (encoded, _) = encode_zscii(empty_entry, 0, char);
        let word_entry = add_bits_int(parse_addr, 1 + 4 * words);
        let dictionary_entry = lookup_entry(dictionary_info, pack_zchars(encoded));
        // TODO: if dictionary_entry >_u 0x0ffff then
        write_word(word_entry, truncate(dictionary_entry, 16));
	write_byte(word_entry + 0x00002, 0x01);
	write_byte(word_entry + 0x00003, add_bits_int(0x00, j));
	words = words + 1;
	j = j + 1;
      } else {
        var k : int = 0;
        var encoded_i : nat = 0;
        var encoded = empty_entry;
        while j + k < total_characters & char != 0x20 & not_bool(byte_is_in(word_separators, char)) do {
          (encoded, encoded_i) = encode_zscii(encoded, encoded_i, char);
          k = k + 1;
          if j + k < total_characters then char = read_byte(add_bits_int(start_addr, j + k));
        };
        let word_entry = add_bits_int(parse_addr, 1 + 4 * words);
        let dictionary_entry = lookup_entry(dictionary_info, pack_zchars(encoded));
        // TODO: if dictionary_entry >_u 0x0ffff then
        write_word(word_entry, truncate(dictionary_entry, 16));
	write_byte(word_entry + 0x00002, add_bits_int(0x00, k));
	write_byte(word_entry + 0x00003, add_bits_int(0x00, j));
	words = words + 1;
        j = j + k;
      }
    };
    write_byte(parse_addr + 0x00001, add_bits_int(0x00, words));
  }
}

function clause decode_0op op = unimplemented("Unmodelled 0op instruction " @ bits_str(op))
function clause decode_1op (op,_) = unimplemented("Unmodelled 1op instruction " @ bits_str(op))
function clause decode_2op (op,_,_) = unimplemented("Unmodelled 2op instruction " @ bits_str(op))
function clause decode_var (op,_) = unimplemented("Unmodelled var instruction " @ bits_str(op))

end decode_0op
end decode_1op
end decode_2op
end decode_var
end instr
end execute
