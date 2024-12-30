
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
